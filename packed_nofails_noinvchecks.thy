section "Packed Traces without Failures and Invariant Checks"
theory packed_nofails_noinvchecks
imports no_failing_invchecks packed_no_fails consistency single_invocation_reduction_helper
begin


text \<open>
 To show that a program is correct, we only have to consider packed transactions 
 with no crashes and no invariant checks.
\<close>

definition isNotTrueInvcheck :: "(invocId \<times> ('proc, 'operation, 'any) action) \<Rightarrow> bool"
      where "isNotTrueInvcheck \<equiv> (\<lambda>a. case a of (s, AInvcheck True) \<Rightarrow> False | _\<Rightarrow> True)"

lemma packed_trace_filter:
  assumes packed: "packed_trace trace"
    and keepAllowedContextSwitch: "\<And>i a. allowed_context_switch a \<Longrightarrow> P (i, a)"
  shows "packed_trace (filter P trace)"
proof -
  from packed 
  have "packed_trace (filter P trace) 
       \<and> (filter P trace \<noteq> [] \<longrightarrow> get_invoc (last (filter P trace)) = get_invoc (last trace))"
  proof (induct trace rule: rev_induct)
    case Nil
    then show ?case by simp
  next
    case (snoc x xs)
    then have IH1: "packed_trace (filter P xs)"
      and IH2: "(filter P xs \<noteq> [] \<Longrightarrow> get_invoc (last (filter P xs)) = get_invoc (last xs))"
      using isPrefix_appendI prefixes_are_packed by blast+

    

    show ?case 
    proof (cases "filter P xs = []")
      case True
      then show ?thesis 
        by (auto simp add:  packed_trace_def nth_append)
    next
      case False
      
      from `packed_trace (xs @ [x])`
      have "get_invoc (last xs) = get_invoc x" if "\<not>allowed_context_switch (get_action x)"
        using that
        by (smt False append.assoc append_Cons append_butlast_last_id diff_Suc_1 filter.simps(1) length_append_singleton length_greater_0_conv lessI nth_append_length use_packed_trace) 
      
      from False have "get_invoc (last (filter P xs)) = get_invoc (last xs)"
        using IH2 by blast
      then show ?thesis 
      proof (auto simp add: packed_trace_def nth_append)

        show "get_invoc (last xs) = get_invoc x"
          if c0: "get_invoc (last (filter P xs)) = get_invoc (last xs)"
            and c1: "\<not> P x"
            and c2: "filter P xs \<noteq> []"
          using that
          by (metis \<open>\<not> allowed_context_switch (get_action x) \<Longrightarrow> get_invoc (last xs) = get_invoc x\<close> keepAllowedContextSwitch surjective_pairing) 

      next
        fix i
        assume a0: "get_invoc (last (filter P xs)) = get_invoc (last xs)"
          and a1: "P x"
          and a2: "i - Suc 0 < length (filter P xs)"

        show "allowed_context_switch (get_action (filter P xs ! i))"
          if a3: "i < length (filter P xs)"
            and a4: "0 < i"
            and a5: "get_invoc (filter P xs ! (i - Suc 0)) \<noteq> get_invoc (filter P xs ! i)"
          by (simp add: IH1 a3 a4 a5 use_packed_trace)



        show "allowed_context_switch (get_action x)"
          if a3: "\<not> i < length (filter P xs)"
            and a4: "i < Suc (length (filter P xs))"
            and a5: "get_invoc (filter P xs ! (i - Suc 0)) \<noteq> get_invoc x"
          using IH1 use_packed_trace[OF IH1]
          by (metis (no_types, lifting) False One_nat_def a0 a3 a4 a5 butlast_snoc diff_less filter.simps(1) last_conv_nth length_append_singleton length_greater_0_conv lessI less_antisym nth_append_length nth_butlast snoc.prems use_packed_trace)

      next
        fix i
        assume a0: "get_invoc (last (filter P xs)) = get_invoc (last xs)"
          and a1: "\<not> P x"
          and a2: "i - Suc 0 < length (filter P xs)"
          and a3: "0 < i"
          and a4: "i < length (filter P xs)"
          and a5: "get_invoc (filter P xs ! (i - Suc 0)) \<noteq> get_invoc (filter P xs ! i)"

        show "allowed_context_switch (get_action (filter P xs ! i))"
          by (simp add: IH1 a3 a4 a5 use_packed_trace)


      qed
    qed
  qed
  thus "packed_trace (filter P trace)"
    by auto
qed


theorem show_programCorrect_noTransactionInterleaving_no_passing_invchecks:
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>
        initialState program ~~ trace \<leadsto>* s; 
        packed_trace trace; 
        \<And>s. (s, ACrash) \<notin> set trace; 
        \<And>s. (s, AInvcheck True) \<notin> set trace
      \<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving)
  fix trace
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, ACrash) \<notin> set trace"

  show "traceCorrect trace"
  proof (rule ccontr)
    assume a: "\<not> traceCorrect trace"

    
    define trace' where "trace' \<equiv> filter isNotTrueInvcheck trace"

    have isNotTrueInvcheck_simps: "isNotTrueInvcheck a \<longleftrightarrow> \<not>(\<exists>s. a = (s, AInvcheck True))" for a
      by (auto simp add: isNotTrueInvcheck_def split: prod.splits action.splits)

    have "traceCorrect trace'"
    proof (rule packedTracesCorrect)
      from steps
      show "initialState program ~~ trace' \<leadsto>* S"
      proof (auto simp add: trace'_def, induct rule: steps_induct)
        case initial
        then show ?case   by (auto simp add: steps_empty )
      next
        case (step S' tr a S'')
        show ?case 
        proof auto
          assume  "isNotTrueInvcheck a"
          then show "initialState program ~~ filter isNotTrueInvcheck tr @ [a] \<leadsto>* S''"
            using step.IH step.step steps_step step.steps by blast 
        next 
          assume "\<not> isNotTrueInvcheck a"
          then have "S' = S''"
            using \<open>S' ~~ a \<leadsto> S''\<close>
            by (auto simp add: isNotTrueInvcheck_def step.simps split: bool.splits)
          then show "initialState program ~~ filter isNotTrueInvcheck tr  \<leadsto>* S''"
            using step.IH step.steps  by blast
        qed
      qed

      from packed 
      have "packed_trace (filter isNotTrueInvcheck trace)"
      proof (rule packed_trace_filter)
        show " \<And>i a. allowed_context_switch a \<Longrightarrow> isNotTrueInvcheck (i, a)"
          by (auto simp add: allowed_context_switch_simps isNotTrueInvcheck_simps)
      qed

      then show "packed_trace trace'"
        unfolding trace'_def by simp
        
      show " \<And>s. (s, ACrash) \<notin> set trace'"
        by (auto simp add: trace'_def nofail)

      show "\<And>s. (s, AInvcheck True) \<notin> set trace'"
        by  (auto simp add: trace'_def isNotTrueInvcheck_def)
    qed
    then have "traceCorrect trace"
      by  (auto simp add: trace'_def traceCorrect_def isNotTrueInvcheck_def actionCorrect_def, force+)

    then show "False"
      using a by blast
  qed
qed

lemma move_invariant_checks_out_of_transactions:
  assumes "initialState program ~~ trace \<leadsto>* S"
    and "packed_trace trace"
    and "\<And>s. (s, ACrash) \<notin> set trace"
    and "\<And>s. (s, AInvcheck True) \<notin> set trace"
    and "length trace > 0"
    and "last trace = (s, AInvcheck False)"
    and "\<And>i s'. i<length trace - 1 \<Longrightarrow> trace!i \<noteq> (s', AInvcheck False)"
  shows "\<exists>trace' s'. 
          (\<exists>S'. initialState program ~~ trace' \<leadsto>* S')
        \<and> packed_trace trace'
        \<and> (\<forall>s. (s, ACrash) \<notin> set trace')
        \<and> (\<forall>s. (s, AInvcheck True) \<notin> set trace')
        \<and> (last trace' = (s', AInvcheck False))
        \<and> length trace' > 0
        \<and> (no_invariant_checks_in_transaction trace')"
  using assms proof (induct "length trace" arbitrary: trace s S rule: less_induct)
  case (less trace s S)
  show ?case 
  proof (cases "no_invariant_checks_in_transaction trace")
    case True
    then show ?thesis 
      using less.prems by auto
  next
    case False

    from this obtain ib i s' tx ib_txns c 
      where ib1: "trace ! ib = (s', ABeginAtomic tx ib_txns)"
        and ib2: "ib < i"
        and "i < length trace"
        and noEndAtomic1: "\<forall>j. ib < j \<and> j < i \<longrightarrow> trace ! j \<noteq> (s', AEndAtomic)"
        and "trace ! i = (s', AInvcheck c)"
      by (auto simp add: no_invariant_checks_in_transaction_def)
    then have i_def: "i = length trace - 1" 
      by (smt One_nat_def Suc_pred less.prems(4) less.prems(5) less.prems(7) less_Suc_eq nth_mem)

    have [simp]: "s' = s" 
      using \<open>trace ! i = (s', AInvcheck c)\<close> i_def last_conv_nth less.prems by (auto simp add: last_conv_nth)



    have ib2: "ib < length trace - 1"
      using i_def ib2 by blast
    from noEndAtomic1
    have noEndAtomic: "trace ! j \<noteq> (s, AEndAtomic)" if "ib\<le>j" and "j<length trace" for j
      using that
      by (metis One_nat_def Pair_inject Suc_pred \<open>s' = s\<close> \<open>trace ! i = (s', AInvcheck c)\<close> action.distinct(31) action.distinct(51) i_def ib1 le_eq_less_or_eq less.prems(5) less_antisym)


    (* Let action a be the action before the invariant check.
     Get the state before and show that we can execute the invariant before that as well
     Then use IH.  *)

    have "xs = ys" if "\<And>i. i<length xs \<Longrightarrow> xs!i = ys!i" and "length xs = length ys" for xs ys
      using nth_equalityI that(1) that(2) by blast


    have "length trace \<ge> 2"
      using ib2 by linarith

    from this
    obtain trace_len_minus2 
        where trace_len_minus2_def: "length trace = Suc (Suc trace_len_minus2)"
      by (metis One_nat_def Suc_pred ib2 `0 < length trace` less_imp_Suc_add)

    have trace_nonempty: "trace \<noteq> []"
      using `0 < length trace` by blast


    have trace_split: "trace = take (length trace - 2) trace @ [trace!(length trace -2), last trace]"
    proof (rule nth_equalityI)
      show "length trace = length (take (length trace - 2) trace @ [trace ! (length trace - 2), last trace])"
        using \<open>length trace \<ge> 2\<close> by (auto simp add: min_def nth_append nth_Cons')
      show "\<And>i. i < length trace \<Longrightarrow>
         trace ! i = (take (length trace - 2) trace @ [trace ! (length trace - 2), last trace]) ! i"
        using trace_len_minus2_def trace_nonempty  by (auto simp add: le_less_Suc_eq last_conv_nth min_def nth_append nth_Cons' not_less)
    qed


    from \<open>initialState program ~~ trace \<leadsto>* S\<close>
    obtain S1 S2
      where steps_S1: "initialState program ~~ take (length trace - 2) trace \<leadsto>* S1"
        and step_S2: "S1 ~~ trace!(length trace -2) \<leadsto> S2"
        and step_inv: "S2 ~~ last trace \<leadsto> S"
      by (metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc last_snoc `0 < length trace` less_numeral_extra(3) list.simps(3) list.size(3) steps.cases steps_appendBack trace_split)

    from step_inv 
    have step_inv': "S2 ~~ (s, AInvcheck False) \<leadsto> S"
      by (auto simp add: \<open>last trace = (s, AInvcheck False)\<close>)

    have invariant_fail_S2[simp]: "\<not> invariant (prog S2) (invContext S2)"
      using step_elim_AInvcheck step_inv' by blast

    have "get_invoc (trace!(length trace -1)) = s"
      using \<open>trace ! i = (s', AInvcheck  c)\<close> i_def by auto

    with \<open>packed_trace trace\<close>
    have "get_invoc (trace!(length trace -2)) = s" 
      by (auto simp add: packed_trace_def allowed_context_switch_def,
          metis One_nat_def Suc_le_lessD \<open>2 \<le> length trace\<close> \<open>i < length trace\<close> \<open>trace ! i = (s', AInvcheck c)\<close> allowed_context_switch_simps(9) diff_Suc_eq_diff_pred i_def less.prems(2) numeral_2_eq_2 snd_conv use_packed_trace zero_less_diff)

    from this obtain action 
      where action_def: "trace!(length trace -2) = (s, action)"
      by (meson eq_fst_iff)
    with \<open>S1 ~~ trace!(length trace -2) \<leadsto> S2\<close>
    have "S1 ~~ (s, action) \<leadsto> S2"
      by simp


    have wf: "state_wellFormed S1"
      using state_wellFormed_combine state_wellFormed_init steps_S1
      by (metis contra_subsetD less.prems(3) set_take_subset) 



    show ?thesis
    proof (cases "ib < length trace - 2")
      case True
      then have [simp]: "ib < length trace - 2"
        by simp

      have currentTx: "currentTransaction S1 s \<triangleq> tx" 
      proof (rule currentTransaction2[OF steps_S1])

        show "take (length trace - 2) trace ! ib = (s, ABeginAtomic tx ib_txns)"
          using ib1 ib2  by auto

        show "ib < length (take (length trace - 2) trace)"
          using ib2 by auto
        show "\<And>j. \<lbrakk>ib < j; j < length (take (length trace - 2) trace)\<rbrakk> \<Longrightarrow> take (length trace - 2) trace ! j \<noteq> (s, ACrash)"
          using less.prems(3) nth_mem by fastforce 
        show "\<And>j. \<lbrakk>ib < j; j < length (take (length trace - 2) trace)\<rbrakk> \<Longrightarrow> take (length trace - 2) trace ! j \<noteq> (s, AEndAtomic)"
          using noEndAtomic by auto
      qed

      with wf
      have ls_none: "localState S1 s \<noteq> None"
        using inTransaction_localState by blast 

      have "S1 ~~ (s, AInvcheck False) \<leadsto> S1"
      proof (cases action)
        case ALocal
        then show ?thesis
          using invariant_fail_S2 \<open>S1 ~~ (s, action) \<leadsto> S2\<close> step_elim_AInvcheck step_inv' by (auto simp add: step_simps, fastforce)
      next
        case (ANewId x2)
        then show ?thesis
          using invariant_fail_S2 \<open>S1 ~~ (s, action) \<leadsto> S2\<close>  by (auto simp add: step_simps, auto)
      next
        case (ABeginAtomic x31 x32)
        then show ?thesis
          using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> currentTx step_simps(3) by force
      next
        case AEndAtomic
        then show ?thesis
          using action_def ib2 noEndAtomic by auto 
      next
        case (ADbOp cId proc res)

        obtain tx where currentTransaction: "currentTransaction S1 s \<triangleq> tx"
          using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> ADbOp
          by (auto simp add:  step_simps)
        then have uncommitted: "transactionStatus S1 tx \<triangleq> Uncommitted"
          using local.wf wellFormed_currentTransaction_unique_h(2) by blast

        have "calls S1 cId = None"
          using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> ADbOp
          by (auto simp add:  step_simps)
        then have "callOrigin S1 cId = None"
          using local.wf wellFormed_callOrigin_dom2 by blast


        have "committedCalls S2 = committedCalls S1" 
          using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> ADbOp
          by (auto simp add:  step_simps ls_none committedCallsH_def isCommittedH_def currentTransaction uncommitted \<open>callOrigin S1 cId = None\<close> split: if_splits)

        have "invContext S2 = invContext S1 "
          using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> ADbOp \<open>callOrigin S1 cId = None\<close> noOrigin_notCommitted
          by (auto simp add: invContextH_def \<open>committedCalls S2 = committedCalls S1\<close> invContextH_def step_simps ls_none restrict_map_def restrict_relation_def intro!: ext, blast+)


         with invariant_fail_S2
         have "\<not> invariant (prog S1) (invContext S1)"
           using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> prog_inv by force

         then show ?thesis 
          using invariant_fail_S2 ADbOp \<open>S1 ~~ (s, action) \<leadsto> S2\<close> by (auto simp add: step_simps ls_none)
      next
        case (AInvoc )
        then show ?thesis 
          using invariant_fail_S2 \<open>S1 ~~ (s, action) \<leadsto> S2\<close>  by (auto simp add: step_simps ls_none)
      next
        case (AReturn x7)
        then show ?thesis 
          using invariant_fail_S2 \<open>S1 ~~ (s, action) \<leadsto> S2\<close>  by (auto simp add: step_simps ls_none currentTx)
      next
        case ACrash
        then show ?thesis
          by (metis action_def diff_less less.prems(3) `0 < length trace` nth_mem zero_less_numeral)
      next
        case (AInvcheck r)
        then show ?thesis 
          by (metis (full_types) Suc_1 Suc_diff_Suc Suc_le_lessD \<open>2 \<le> length trace\<close> action_def diff_less less.prems(4) `0 < length trace` less.prems(7) lessI nth_mem zero_less_numeral)
      qed
      show ?thesis
      proof (rule less.hyps) \<comment> \<open>USE induction hypothesis\<close>
        from \<open>S1 ~~ (s, AInvcheck False) \<leadsto> S1\<close>
        show " initialState program ~~ take (length trace - 2) trace @ [(s, AInvcheck False)] \<leadsto>* S1"
          using steps_S1 steps_step by blast

        have no_ctxt_switch: "\<not>allowed_context_switch (get_action (trace!(length trace -2)))"
          using \<open>S1 ~~ trace ! (length trace - 2) \<leadsto> S2\<close>
          using action_def currentTx ls_none by (auto simp add: step.simps allowed_context_switch_simps)



        show "packed_trace (take (length trace - 2) trace @ [(s, AInvcheck False)])"
        proof (auto simp add: packed_trace_def nth_append min_def not_less)


          show "allowed_context_switch (get_action (trace ! i))"
            if c1: "i - Suc 0 < length trace - 2"
              and c3: "0 < i"
              and c4: "get_invoc (trace ! (i - Suc 0)) \<noteq> get_invoc (trace ! i)"
            for  i
            using c1 c3 c4 by (simp add: less.prems(2) use_packed_trace)

          show "allowed_context_switch (AInvcheck False)"
            if c0: "\<not> length trace \<le> length trace - 2"
              and c1: "i - Suc 0 < length trace - 2"
              and c2: "length trace - 2 \<le> i"
              and c3: "i < Suc (length trace - 2)"
              and c4: "get_invoc (trace ! (i - Suc 0)) \<noteq> s"
            for  i
          proof -
            have "i = length trace - 2"
              using c2 c3 le_less_Suc_eq by blast 

            show "allowed_context_switch (AInvcheck False)"
              using \<open>get_invoc (trace!(length trace -2)) = s\<close> 
               use_packed_trace[OF \<open>packed_trace trace\<close>, where i="length trace - 2"]
               \<open>i = length trace - 2\<close> c4 no_ctxt_switch
              by force
          qed
        qed

        show "0 < length (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          by simp



        show "\<And>s'. (s', AInvcheck True) \<notin> set (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          by (auto, meson in_set_takeD less.prems(4))

        show "\<And>s'. (s', ACrash) \<notin> set (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          by (auto, meson in_set_takeD less.prems(3))

        show "last (take (length trace - 2) trace @ [(s, AInvcheck False)]) = (s, AInvcheck False)"
          by simp

        show "length (take (length trace - 2) trace @ [(s, AInvcheck False)]) < length trace"
          by (metis add_Suc_right length_Cons length_append lessI trace_split)
        show "\<And>i s'.
       i < length (take (length trace - 2) trace @ [(s, AInvcheck False)]) - 1 \<Longrightarrow>
       (take (length trace - 2) trace @ [(s, AInvcheck False)]) ! i \<noteq> (s', AInvcheck False)"
          by (auto simp add: nth_append less.prems)
      qed


    next
      case False
      then have "ib = length trace - 2"
        using ib2 by linarith
      then have "action = ABeginAtomic tx ib_txns"
        using action_def ib1 by auto
      with  \<open>S1 ~~ (s, action) \<leadsto> S2\<close>
      have "invContext S1 = invContext S2"
        using invariant_fail_S2 by (auto simp add: step_simps invContextH_def restrict_map_def committedCallsH_update_uncommitted )

      with \<open>S1 ~~ (s, action) \<leadsto> S2\<close> and \<open>action = ABeginAtomic tx ib_txns\<close>
      have "S1 ~~ (s', AInvcheck False) \<leadsto> S1" for s'
        using invariant_fail_S2 by (auto simp add: step_simps, auto)

      define new_s where "new_s = get_invoc(trace ! (length trace - 3))" 

      show ?thesis
      proof (rule less.hyps) \<comment> \<open>USE induction hypothesis\<close>
        from \<open>S1 ~~ (new_s, AInvcheck False) \<leadsto> S1\<close>
        show " initialState program ~~ take (length trace - 2) trace @ [(new_s, AInvcheck False)] \<leadsto>* S1"
          using steps_S1 steps_step by blast


        show "packed_trace (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          by (auto simp add: packed_trace_def nth_append min_def not_less new_s_def  less.prems(2),
              simp add: less.prems(2) use_packed_trace,
              metis One_nat_def diff_Suc_eq_diff_pred le_less_Suc_eq numeral_2_eq_2 numeral_3_eq_3)

        show "0 < length (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          by simp

        show "\<And>s'. (s', AInvcheck True) \<notin> set (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          by (auto, meson in_set_takeD less.prems(4))

        show "\<And>s'. (s', ACrash) \<notin> set (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          by (auto, meson in_set_takeD less.prems(3))

        show "last (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) = (new_s, AInvcheck False)"
          by simp

        show "length (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) < length trace"
          by (metis add_Suc_right length_Cons length_append lessI trace_split)
        show "\<And>i s'.
       i < length (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) - 1 \<Longrightarrow>
       (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) ! i \<noteq> (s', AInvcheck False)"
          by (auto simp add: nth_append less.prems)
      qed
    qed
  qed
qed


text \<open>
 To show that a program is correct, we only have to consider packed transactions 
 with no invariant checks 
\<close>
theorem show_programCorrect_noTransactionInterleaving':
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, ACrash) \<notin> set trace; \<And>s. (s, AInvcheck True) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving_no_passing_invchecks)
  fix trace
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, ACrash) \<notin> set trace"
    and noTrueInvs: "\<And>s. (s, AInvcheck True) \<notin> set trace"



  show "traceCorrect trace"
  proof (cases "\<exists>a\<in>set trace. get_action a = AInvcheck False")
    case True
    from this
    obtain i1 where exists_inv_fail: "(\<exists>s. trace!i1 = (s, AInvcheck False)) \<and> i1 < length trace" 
      by (metis eq_snd_iff in_set_conv_nth)


    show "traceCorrect trace"
    proof (rule ccontr)
      assume a: "\<not> traceCorrect trace"

\<comment> \<open>get the first failing invariant check\<close>
      obtain i 
        where i1: "\<exists>s. trace ! i = (s, AInvcheck False)"
          and i2: "i < length trace"
          and i_min: "\<forall>i'. (\<exists> s'. trace ! i' = (s', AInvcheck False)) \<and> i' < length trace \<longrightarrow> i\<le>i'"
        by (atomize_elim,
            rule exI[where x="LEAST i'. (\<exists>s'. trace ! i' = (s', AInvcheck False)) \<and> i' < length trace"],
            rule LeastI2_wellorder_ex,
            insert exists_inv_fail, auto)




      from i1
      obtain s where i1': "trace ! i = (s, AInvcheck False)"
        by blast

      have trace_split3: "trace = take (Suc i) trace  @ drop (Suc i) trace"
        by auto

      with steps
      have "initialState program ~~ take (Suc i) trace  @ drop (Suc i) trace \<leadsto>* S" 
        by simp
      from this
      obtain Si 
        where steps_Si: "initialState program ~~ take (Suc i) trace \<leadsto>* Si"
        using steps_append by blast

      have "\<exists>trace' s'. (\<exists>S'. initialState program ~~ trace' \<leadsto>* S') \<and>
                  packed_trace trace' \<and>
                  (\<forall>s. (s, ACrash) \<notin> set trace') \<and>
                  (\<forall>s. (s, AInvcheck True) \<notin> set trace') \<and> last trace' = (s', AInvcheck False) \<and> 0 < length trace' \<and> no_invariant_checks_in_transaction trace'"
      proof (rule  move_invariant_checks_out_of_transactions[OF steps_Si])
        show "packed_trace (take (Suc i) trace)"
          by (metis isPrefix_appendI packed prefixes_are_packed trace_split3)
        show "\<And>s. (s, ACrash) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD nofail)
        show "\<And>s. (s, AInvcheck True) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD noTrueInvs)
        show "last (take (Suc i) trace) = (s, AInvcheck False)"
          by (simp add: i1' i2 take_Suc_conv_app_nth)
        show "0 < length (take (Suc i) trace)"
          using gr_implies_not_zero i2 by auto
        show "\<And>ia s' . ia < length (take (Suc i) trace) - 1 \<Longrightarrow> take (Suc i) trace ! ia \<noteq> (s', AInvcheck False)"
          using i_min by fastforce
      qed

      then show False
        using actionCorrect_def last_in_set packedTracesCorrect traceCorrect_def by fastforce
    qed
  next 
    case False
    show ?thesis
      using steps
    proof (rule packedTracesCorrect)
      show "packed_trace trace"
        by (simp add: packed)

      show "\<And>s. (s, ACrash) \<notin> set trace"
        by (simp add: nofail)

      show "\<And>s. (s, AInvcheck True) \<notin> set trace"
        by (simp add: noTrueInvs)


      show "no_invariant_checks_in_transaction trace"
        using False noTrueInvs 
        by (auto simp add: no_invariant_checks_in_transaction_def all_set_conv_all_nth in_set_conv_nth)
    qed
  qed
qed

(* TODO utils *)
lemma show_list_split:
  assumes "ys = take (length ys) xs"
    and "zs = drop (length ys) xs"
  shows "xs = ys @ zs"
  by (metis append_take_drop_id assms(1) assms(2))

lemma append_eq_conv_conj':
  shows "(xs = ys @ zs) \<longleftrightarrow> (ys = take (length ys) xs \<and> zs = drop (length ys) xs)"
  by (metis append_eq_conv_conj)

lemma cons_eq_conv_conj': 
  "(y # ys = xs) \<longleftrightarrow> (xs \<noteq> [] \<and> y = hd xs \<and> ys = tl xs)"  for xs ys zs
  by force

lemmas list_split_utils = 
  append_eq_conv_conj 
  append_eq_conv_conj'
  cons_eq_conv_conj 
  cons_eq_conv_conj'

lemma min_simps:
  fixes x :: nat
  shows
 "x < y \<Longrightarrow> min x y = x"
"x < y \<Longrightarrow> min y x = x"
 "x \<le> y \<Longrightarrow> min x y = x"
"x \<le> y \<Longrightarrow> min y x = x"
  by auto


lemma no_more_actions_on_packed_trace_if_context_switch_in_transaction:
  assumes "S ~~ tr \<leadsto>* S'"
    and "packed_trace tr"
    and "currentTransaction S i \<triangleq> tx"
    and "get_invoc (hd tr) \<noteq> i"
    and "tr \<noteq> []"
    and "state_wellFormed S"
    and "\<And>i. (i, ACrash) \<notin> set tr"
  shows "currentTransaction S' i \<triangleq> tx \<and> (\<forall>a\<in>set tr. get_invoc a \<noteq> i)"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case
    by simp
next
  case (step S' tr a S'')

  show ?case
  proof (cases tr)
    case Nil
    then show ?thesis
      using step by (auto simp add: steps_empty,
          metis prod.collapse unchangedInTransaction(3))
  next
    case (Cons x xs)




    have IH: "currentTransaction S' i \<triangleq> tx \<and> (\<forall>a\<in>set tr. get_invoc a \<noteq> i)"
    proof (rule step.IH)
      show "packed_trace tr"
        using packed_trace_prefix step.prems(1) by blast
      show "currentTransaction S i \<triangleq> tx"
        by (simp add: step.prems(2))
      show "tr \<noteq> []"
        using local.Cons by blast
      show " get_invoc (hd tr) \<noteq> i"
        using \<open>tr \<noteq> []\<close> step.prems(3) by auto
      show "state_wellFormed S"
        by (simp add: step.prems(5))
      show "\<And>i. (i, ACrash) \<notin> set tr"
        using step.prems(6) by auto

    qed

    have "state_wellFormed S'"
      using state_wellFormed_combine
        `S ~~ tr \<leadsto>* S'` `state_wellFormed S`
        step.prems(6) by fastforce 



    from use_packed_trace[OF `packed_trace (tr @ [a])`, where i="length tr"]
    have no_context_switch: "allowed_context_switch (get_action a)" if "get_invoc a = i"
      by (auto, metis IH diff_Suc_less length_greater_0_conv list.distinct(1) local.Cons nth_append nth_mem that)

    find_theorems allowed_context_switch packed_trace


    from `S' ~~ a \<leadsto> S''` IH no_context_switch
    show ?thesis
      using  state_wellFormed_ls_to_visibleCalls[OF \<open>state_wellFormed S'\<close>]
      by (auto simp add: step.simps allowed_context_switch_def, blast)



  qed
qed

lemma no_invariant_checks_in_transaction_prefix:
  assumes a: "no_invariant_checks_in_transaction tr"
and p: "isPrefix tr' tr"
shows "no_invariant_checks_in_transaction tr'"
  using a isPrefix_len[OF p] isPrefix_same[OF p] order.strict_trans2
  by (auto simp add: no_invariant_checks_in_transaction_def, blast)

lemma no_context_switch_transaction:
  assumes "S ~~ tr \<leadsto>* S'"
    and "(hd tr) = (invoc, ABeginAtomic tx txns)"
    and "(invoc, AEndAtomic) \<notin> set tr"
    and "packed_trace tr"
    and "\<forall>a\<in>set (tl tr). \<not>allowed_context_switch (get_action a)"
  shows "\<forall>a\<in>set tr. get_invoc a = invoc"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case
    by simp
next
  case (step S' tr a S'')

  show ?case
  proof (cases "tr=[]")
    case True
    then show ?thesis 
      using step.prems(1) by auto
  next
    case False


    have "packed_trace tr"
      using packed_trace_prefix step.prems(3) by blast

    have "hd tr = (invoc, ABeginAtomic tx txns)" 
      using step.prems(1) `tr \<noteq> []` by auto


    have "(invoc, AEndAtomic) \<notin> set tr"
      using step.prems(2) by auto

    from step.IH
    have "\<forall>a\<in>set tr. get_invoc a = invoc"
      using False \<open>(invoc, AEndAtomic) \<notin> set tr\<close> \<open>hd tr = (invoc, ABeginAtomic tx txns)\<close> \<open>packed_trace tr\<close> step.prems(4) by auto


    from `\<forall>a\<in>set (tl (tr @ [a])). \<not> allowed_context_switch (get_action a)`
    have "\<not>allowed_context_switch (get_action a)" if "tr \<noteq> []"
      using that by auto



    have "get_invoc a = invoc"
    proof (rule ccontr)
      assume "get_invoc a \<noteq> invoc"
      hence "allowed_context_switch (get_action a)"
        using use_packed_trace[OF `packed_trace (tr @ [a])`, where i="length tr"]
        by (simp add: False \<open>\<forall>a\<in>set tr. get_invoc a = invoc\<close> nth_append)

      thus False
        using False \<open>tr \<noteq> [] \<Longrightarrow> \<not> allowed_context_switch (get_action a)\<close> by blast
    qed


    show ?thesis
      using \<open>\<forall>a\<in>set tr. get_invoc a = invoc\<close> \<open>get_invoc a = invoc\<close> by auto
  qed
qed

lemma no_context_switch_transaction2:
  assumes "S ~~ tr \<leadsto>* S'"
    and "tr!i = (invoc, ABeginAtomic tx txns)"
    and "\<And>j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and "packed_trace tr"
    and "\<And>j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> \<not>allowed_context_switch (get_action (tr!j))"
    and "i \<le> k"
    and "k < length tr"
  shows "get_invoc (tr!k) = invoc"
proof -

  obtain tr1 tr2 tr3 
    where tr_split: "tr = tr1 @ tr2 @ tr3"
      and "i = length tr1"
      and "length tr1 + length tr2 = Suc k"
    by (metis Suc_leI append.assoc append_take_drop_id assms(6) assms(7) le_imp_less_Suc length_append length_take less_imp_le min.absorb2)


  with `S ~~ tr \<leadsto>* S'`
  obtain Sa Sb 
    where "S ~~ tr1 \<leadsto>* Sa"
      and "Sa ~~ tr2 \<leadsto>* Sb"
    using steps_append by blast


  have [simp]: "tr2 \<noteq> []"
    using \<open>i = length tr1\<close> \<open>length tr1 + length tr2 = Suc k\<close> assms(6) by auto

  have [simp]: "tr2 ! 0 = (invoc, ABeginAtomic tx txns)"
    by (metis \<open>i = length tr1\<close> \<open>tr2 \<noteq> []\<close> add.right_neutral assms(2) length_greater_0_conv nth_append_first nth_append_length_plus tr_split)
  hence [simp]: "hd tr2 = (invoc, ABeginAtomic tx txns)"
    by (simp add: hd_conv_nth)
    

  have "\<forall>a\<in>set tr2. get_invoc a = invoc"
    using `Sa ~~ tr2 \<leadsto>* Sb`
  proof (rule no_context_switch_transaction)
    show "hd tr2 = (invoc, ABeginAtomic tx txns)"
      using `tr!i = (invoc, ABeginAtomic tx txns)`
      by (auto simp add: tr_split nth_append `i = length tr1` split: if_splits)
    show "(invoc, AEndAtomic) \<notin> set tr2"
      using `\<And>j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)`
      using \<open>i = length tr1\<close> \<open>length tr1 + length tr2 = Suc k\<close> 
      apply (auto simp add: tr_split nth_append in_set_conv_nth split: if_splits)

      apply (drule_tac x="length tr1 + ia" in meta_spec)
      apply (auto simp add: tr_split nth_append in_set_conv_nth split: if_splits)
      apply (case_tac ia)
       apply auto
      done
    show "packed_trace tr2"
      using assms(4) packed_trace_postfix packed_trace_prefix tr_split by auto 
    show "\<forall>a\<in>set (tl tr2). \<not> allowed_context_switch (get_action a)"
      using `\<And>j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> \<not>allowed_context_switch (get_action (tr!j))`
      apply (auto simp add: tr_split nth_append in_set_conv_nth split: if_splits)
      apply (drule_tac x="length tr1 + ia" in meta_spec)
      apply (auto simp add: tr_split nth_append in_set_conv_nth nth_tl split: if_splits)
      by (metis One_nat_def Suc_leI \<open>i = length tr1\<close> \<open>length tr1 + length tr2 = Suc k\<close> add.commute add_Suc_right add_diff_cancel_left' assms(5) less_add_Suc1 less_diff_conv nth_append_first nth_append_length_plus plus_1_eq_Suc snd_conv tr_split)
  qed

  thus "get_invoc (tr ! k) = invoc"
    by (metis (no_types, lifting) Suc_diff_le \<open>i = length tr1\<close> \<open>length tr1 + length tr2 = Suc k\<close> add_diff_cancel_left' assms(6) in_set_conv_nth leD lessI nth_append tr_split)
qed

definition 
"drop_no_action_coupling S1 S2 i \<equiv> 
  calls S1 = calls S2
\<and> happensBefore S1 = happensBefore S2
\<and> callOrigin S1 = callOrigin S2
\<and> transactionOrigin S1 = transactionOrigin S2
\<and> knownIds S1 = knownIds S2
\<and> invocationOp S1 = invocationOp S2
\<and> invocationRes S1 = invocationRes S2
\<and> prog S1 = prog S2
\<and> transactionStatus S1 = transactionStatus S2
\<and> (\<forall>id i'. i' \<noteq> i \<longrightarrow>  generatedIds S1 id \<triangleq> i' \<longleftrightarrow> generatedIds S2 id \<triangleq> i')
\<and> (dom (generatedIds S2) \<subseteq> dom (generatedIds S1))
\<and> (\<forall>i'. i' \<noteq> i \<longrightarrow> localState S1 i' = localState S2 i')
\<and> currentProc S1 = currentProc S2
\<and> visibleCalls S1 = visibleCalls S2
\<and> currentTransaction S1 = currentTransaction S2
"

lemma drop_no_action:
  assumes "S1 ~~ tr \<leadsto>* S1'"
    and "\<forall>a\<in>set tr. get_invoc a \<noteq> i"
    and "drop_no_action_coupling S1 S2 i"
  shows "\<exists>S2'. (S2 ~~ tr \<leadsto>* S2') \<and> drop_no_action_coupling S1' S2' i" 
  using assms
proof (induct rule: steps_induct)
  case initial
  then show ?case
    using steps_empty by blast 

next
  case (step S' tr a S'')
  obtain S2' where "S2 ~~ tr \<leadsto>* S2'" and coup: "drop_no_action_coupling S' S2' i"
    using step.IH step.prems(1) step.prems(2) by auto

  have not_i: "get_invoc a \<noteq> i"
    by (simp add: step.prems(1))


  from ` S' ~~ a \<leadsto> S''`
  have "\<exists>S2''. (S2' ~~ a \<leadsto> S2'') \<and> drop_no_action_coupling S'' S2'' i"
  proof (cases rule: step.cases)
    case (local i ls f ok ls')
    then show ?thesis 
      using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (newId i ls f ls' uid uidv ls'')
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (beginAtomic i ls f ls' t vis snapshot)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def chooseSnapshot_unchanged)
  next
    case (endAtomic i ls f ls' t)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (dbop i ls f Op ls' t c res vis)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (invocation i proc initialState impl)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (return i ls f res)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (fail i ls)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  next
    case (invCheck res i)
    then show ?thesis using coup not_i by (auto simp add: step.simps  drop_no_action_coupling_def)
  qed

  then show ?case
    using \<open>S2 ~~ tr \<leadsto>* S2'\<close> steps_step by blast 
qed



lemma steps_dropLast_tx:
  assumes "S ~~ tr \<leadsto>* S'"
    and "i > 0"
    and "i < length tr"
    and forbidden_actions: "get_action (tr!i) \<notin> {AEndAtomic} \<union> AReturn ` UNIV"
    and no_more_actions: "\<And>j. j>i \<Longrightarrow> j < length tr \<Longrightarrow> get_invoc (tr!j) \<noteq> get_invoc (tr!i)"
  shows "\<exists>S''. S ~~ take (i-1) tr @ drop i tr \<leadsto>* S''"
proof
  have [simp]: "min (length tr) (i - Suc 0) = i - 1"
    by (simp add: assms(3) less_imp_diff_less min_simps(2))

  have [simp]: "i - Suc 0 + (length tr - i) = length tr - 1"
    by (simp add: Suc_leI assms(2) assms(3) less_or_eq_imp_le)

  have [simp]: "Suc (length tr - i) = Suc (length tr) - i"
    by (simp add: Suc_diff_le assms(3) less_imp_le)


  have [simp]: "length tr - (i - Suc 0) = Suc (length tr) - i"
    using assms(2) assms(3) by auto

  have [simp]: "Suc (length tr - Suc i) = length tr - i"
    using Suc_diff_Suc assms(3) by blast


  have "tr = take i tr @ drop i tr "
    by (auto simp add: list_eq_iff_nth_eq nth_append nth_Cons')

  moreover have "drop i tr = [tr!i] @ drop (Suc i) tr"
    by (auto simp add: list_eq_iff_nth_eq nth_append nth_Cons')



  ultimately have tr_split: "tr = take i tr @[tr!i] @ drop (Suc i) tr "
    by simp

  from this
  obtain S1 S2 S3
    where "S ~~ take i tr \<leadsto>* S1" and "S1 ~~ tr ! i \<leadsto> S2" and "S2 ~~ drop (Suc i) tr \<leadsto>* S3"
    by (smt Cons_nth_drop_Suc \<open>drop i tr = [tr ! i] @ drop (Suc i) tr\<close> assms(1) assms(3) steps_append steps_appendFront)

  from `S2 ~~ drop (Suc i) tr \<leadsto>* S3`
  have "\<exists>S2'. (S1 ~~ drop (Suc i) tr \<leadsto>* S2') \<and> drop_no_action_coupling S3 S2' (get_invoc (tr!i))"
  proof (rule drop_no_action)
    show "\<forall>a\<in>set (drop (Suc i) tr). get_invoc a \<noteq> get_invoc (tr!i)"
      apply (auto simp add: in_set_conv_nth)
      by (metis Suc_leI add_Suc assms(3) assms(5) fst_conv less_add_Suc1 nat_add_left_cancel_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse)

    from `S1 ~~ tr ! i \<leadsto> S2`
    show " drop_no_action_coupling S2 S1 (get_invoc (tr!i))"
    proof (cases rule: step.cases)
      case (local i'' ls f ok ls')
      then show ?thesis
        by (auto simp add: drop_no_action_coupling_def)
    next
      case (newId i ls f ls' uid uidv ls'')
      then show ?thesis 
        by (auto simp add: drop_no_action_coupling_def)
    next
      case (beginAtomic i ls f ls' t vis snapshot)
      then show ?thesis 
        apply (auto simp add: drop_no_action_coupling_def)
        sorry
    next
      case (endAtomic i ls f ls' t)
      then show ?thesis
        using forbidden_actions by auto 
    next
      case (dbop i ls f Op ls' t c res vis)
      then show ?thesis sorry
    next
      case (invocation i proc initialState impl)
      then show ?thesis sorry
    next
      case (return i ls f res)
      then show ?thesis 
        using forbidden_actions by auto 
    next
      case (fail i ls)
      then show ?thesis sorry
    next
      case (invCheck res i)
      then show ?thesis sorry
    qed
      apply (auto simp add: )


  sorry


definition "induct_measure" where "induct_measure  \<equiv> \<lambda>trace. \<lambda>pos'.
    case pos' of
        0 \<Rightarrow> True
      | Suc pos \<Rightarrow>  pos<length trace \<and> (\<exists>i j tx txns. get_invoc(trace!pos) = i \<and>  j\<le>pos \<and> trace!j = (i, ABeginAtomic tx txns) \<and> (\<nexists>k. k>j \<and> k<length trace \<and> trace!k = (i, AEndAtomic)))" 

text \<open>
 To show that a program is correct, we only have to consider packed traces
with no context switches in transactions.
\<close>
lemma remove_context_switches_in_transactions:
  assumes a1: "initialState program ~~ trace \<leadsto>* S"
    and a2: "packed_trace trace"
    and a3: "\<And>s. (s, ACrash) \<notin> set trace"
    and a4: "\<And>s. (s, AInvcheck True) \<notin> set trace"
    and a5: "no_invariant_checks_in_transaction trace"
    and a6: "\<not>traceCorrect trace"
  obtains trace' S'
  where "initialState program ~~ trace' \<leadsto>* S'"
    and "packed_trace trace'"
    and "\<And>s. (s, ACrash) \<notin> set trace'"
    and "\<And>s. (s, AInvcheck True) \<notin> set trace'"
    and "no_invariant_checks_in_transaction trace'"
    and "\<not>traceCorrect trace'"
    and "\<not>contextSwitchesInTransaction trace'"
  using a1 a2 a3 a4 a5 a6 proof (atomize_elim, induct "length trace" arbitrary: S trace rule: less_induct)
  case (less trace S)

  show ?case
  proof (rule classical, goal_cases trivial)
    case trivial

    hence trivial1: "(\<not>P \<Longrightarrow> ?case) \<Longrightarrow> P" for P
      by blast

    hence trivial2: "(P \<Longrightarrow> ?case) \<Longrightarrow> \<not>P" for P
      by blast

    have all_actions_correct_but_last: "actionCorrect (get_action a)" if "trace ! i = a" and "i < length trace - 1" for i a
    proof (rule trivial1)
      assume "\<not> actionCorrect (get_action a)"

      have len: "length (take (Suc i) trace) < length trace"
        using that(2) by auto


      obtain S' where steps': "initialState program ~~ take (Suc i) trace \<leadsto>* S'"
        by (metis append_take_drop_id less.prems(1) steps_append)


      show ?case 
        using len steps'
      proof (rule less)
        show "packed_trace (take (Suc i) trace)"
          using less.prems(2) packed_trace_take by blast
        show "\<And>s. (s, ACrash) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD less.prems(3))
        show "\<And>s. (s, AInvcheck True) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD less.prems(4))
        show "no_invariant_checks_in_transaction (take (Suc i) trace)"
          by (metis append_take_drop_id isPrefix_appendI less.prems(5) no_invariant_checks_in_transaction_prefix)
        show "\<not> traceCorrect (take (Suc i) trace)"
          by (metis (no_types, lifting) \<open>\<not> actionCorrect (get_action a)\<close> len length_take lessI min_less_iff_conj min_simps(2) nat_neq_iff nth_append_length nth_mem take_Suc_conv_app_nth that(1) traceCorrect_def)
        show "initialState program ~~ take (Suc i) trace \<leadsto>* S'"
          using steps' by blast
        show "packed_trace (take (Suc i) trace)"
          by (simp add: \<open>packed_trace (take (Suc i) trace)\<close>)
        show "\<And>s. (s, ACrash) \<notin> set (take (Suc i) trace)"
          using \<open>\<And>s. (s, ACrash) \<notin> set (take (Suc i) trace)\<close> by blast
        show "\<And>s. (s, AInvcheck True) \<notin> set (take (Suc i) trace)"
          by (simp add: \<open>\<And>s. (s, AInvcheck True) \<notin> set (take (Suc i) trace)\<close>)
        show "no_invariant_checks_in_transaction (take (Suc i) trace)"
          by (simp add: \<open>no_invariant_checks_in_transaction (take (Suc i) trace)\<close>)
        show "\<not> traceCorrect (take (Suc i) trace)"
          by (simp add: \<open>\<not> traceCorrect (take (Suc i) trace)\<close>)
      qed
    qed

    hence last_action_incorrect: "\<not>actionCorrect (get_action (last trace))"
      by (metis (no_types, lifting) append_butlast_last_id in_set_conv_nth last_conv_nth length_append_singleton length_butlast length_pos_if_in_set less.prems(6) less_antisym less_numeral_extra(3) list.size(3) traceCorrect_def)


    have "contextSwitchesInTransaction trace"
    proof (rule trivial1)
      assume "\<not>contextSwitchesInTransaction trace"
      thus ?case
        using less by blast
    qed

    from this obtain i_begin1 i_switch1
      where "contextSwitchInTransaction trace i_begin1 i_switch1"
      by (auto simp add: contextSwitchesInTransaction_def)

    from this obtain i_begin i_switch
      where i_switch: "contextSwitchInTransaction trace i_begin i_switch"
        and i_switch_min: "\<And>i_begin' i_switch'. contextSwitchInTransaction trace i_begin' i_switch' \<Longrightarrow> i_switch \<le> i_switch'"
      using exists_min_wellorder[where P="\<lambda>i_switch. \<exists>i_begin. contextSwitchInTransaction trace i_begin i_switch"]
      by meson

    from i_switch
    obtain invoc tx txns
      where a0: "i_begin < i_switch"
        and a1: "i_switch < length trace"
        and a2: "trace ! i_begin = (invoc, ABeginAtomic tx txns)"
        and a3: "\<forall>j. i_begin < j \<and> j < i_switch \<longrightarrow> trace ! j \<noteq> (invoc, AEndAtomic)"
        and a4: "allowed_context_switch (get_action (trace ! i_switch))"
      by (auto simp add: contextSwitchInTransaction_def)


    text "We are in a transaction, so execution up to j gives 
  us a state with a current transaction:"
    obtain S_j_pre
      where "initialState program ~~ take i_switch trace \<leadsto>* S_j_pre"
      by (metis a1 id_take_nth_drop less.prems(1) steps_append)


    from this
    have "currentTransaction S_j_pre invoc \<triangleq> tx"
    proof (rule currentTransaction2)
      show "i_begin < length (take i_switch trace)"
        by (simp add: a0 a1 min_simps(2))
      show " take i_switch trace ! i_begin = (invoc, ABeginAtomic tx txns)"
        by (simp add: a0 a2) 
      fix ja
      assume a0: "i_begin < ja"
        and a1: "ja < length (take i_switch trace)"

      show "take i_switch trace ! ja \<noteq> (invoc, ACrash)"
        using a1 less.prems(3) nth_mem by fastforce

      show "take i_switch trace ! ja \<noteq> (invoc, AEndAtomic)"
        using a0 a1 a3 by auto
    qed

    have "state_wellFormed S_j_pre"
      by (meson \<open>initialState program ~~ take i_switch trace \<leadsto>* S_j_pre\<close> less.prems(3) set_take_subset state_wellFormed_combine state_wellFormed_init subsetD)

    have "i_switch < length trace"
      by (simp add: a1)



    obtain S_j_post
      where "S_j_pre ~~ trace ! i_switch \<leadsto> S_j_post"
      by (metis (no_types, lifting) \<open>initialState program ~~ take i_switch trace \<leadsto>* S_j_pre\<close> a1 id_take_nth_drop less.prems(1) steps_append2 steps_appendFront)



    text "Since we are in a transaction, the action at position j cannot be a
  context switch on the same invocation"

    with `allowed_context_switch (get_action (trace ! i_switch))`
      and `currentTransaction S_j_pre invoc \<triangleq> tx`
    have "get_invoc (trace ! i_switch) \<noteq> invoc"
      using  inTransaction_localState[OF \<open>state_wellFormed S_j_pre\<close>] 
      by (auto simp add: step.simps, blast)

    have "i_switch < length trace"
      by (simp add: a1)

    have "i_switch > 0"
      using a0 by linarith


    have "S_j_pre ~~ drop i_switch trace \<leadsto>* S"
      using \<open>initialState program ~~ take i_switch trace \<leadsto>* S_j_pre\<close> less.prems(1) steps_append2 by fastforce

    from this
    have "currentTransaction S invoc \<triangleq> tx \<and> (\<forall>a\<in>set (drop i_switch trace). get_invoc a \<noteq> invoc)"
    proof (rule no_more_actions_on_packed_trace_if_context_switch_in_transaction)
      show "packed_trace (drop i_switch trace)"
        by (simp add: less.prems(2) packed_trace_drop)
      show "currentTransaction S_j_pre invoc \<triangleq> tx"
        by (simp add: \<open>currentTransaction S_j_pre invoc \<triangleq> tx\<close>)
      show "get_invoc (hd (drop i_switch trace)) \<noteq> invoc"
        by (simp add: \<open>get_invoc (trace ! i_switch) \<noteq> invoc\<close> \<open>i_switch < length trace\<close> hd_drop_conv_nth)
      show "drop i_switch trace \<noteq> []"
        using \<open>i_switch < length trace\<close> drop_eq_Nil leD by blast
      show "state_wellFormed S_j_pre"
        by (simp add: \<open>state_wellFormed S_j_pre\<close>)
      show "\<And>i. (i, ACrash) \<notin> set (drop i_switch trace)"
        by (meson in_set_dropD less.prems(3))
    qed


    hence "get_invoc (trace ! j') \<noteq> invoc" if "j' > i_switch" and "j' < length trace" for j'
      using that apply (auto simp add: all_set_conv_all_nth)
      by (metis diff_less_mono less_or_eq_imp_le ordered_cancel_comm_monoid_diff_class.add_diff_inverse)


    show ?thesis
    proof (cases "get_action (trace ! (i_switch - 1)) = ALocal False")
      case True
      text "If the action before j was a context, then only consider the trace up to this and use IH."

      thm less.hyps

      have "isPrefix (take i_switch trace) trace"
        by (metis append_take_drop_id isPrefix_appendI)


      show ?thesis
      proof (rule less.hyps)
        show "length (take i_switch trace) < length trace"
          using \<open>i_switch < length trace\<close> by auto
        show "initialState program ~~ take i_switch trace \<leadsto>* S_j_pre"
          using \<open>initialState program ~~ take i_switch trace \<leadsto>* S_j_pre\<close> by blast
        show "packed_trace (take i_switch trace)"
          using less.prems(2) packed_trace_take by blast
        show "\<And>s. (s, ACrash) \<notin> set (take i_switch trace)"
          by (meson in_set_takeD less.prems(3))
        show "no_invariant_checks_in_transaction (take i_switch trace)"
          using `no_invariant_checks_in_transaction trace`
          using \<open>isPrefix (take i_switch trace) trace\<close> no_invariant_checks_in_transaction_prefix by blast
        show "\<not> traceCorrect (take i_switch trace)"
        proof (auto simp add: traceCorrect_def, intro bexI)
          show "(trace ! (i_switch - 1)) \<in> set (take i_switch trace) "
            by (metis \<open>0 < i_switch\<close> a1 diff_less length_take min_simps(2) nth_mem nth_take zero_less_one)
          show "\<not> actionCorrect (get_action (trace ! (i_switch - 1)))"
            using True actionCorrect_def by blast
        qed
        show "initialState program ~~ take i_switch trace \<leadsto>* S_j_pre"
          using \<open>initialState program ~~ take i_switch trace \<leadsto>* S_j_pre\<close> by auto
        show "packed_trace (take i_switch trace)"
          using \<open>packed_trace (take i_switch trace)\<close> by blast
        show "\<And>s. (s, ACrash) \<notin> set (take i_switch trace)"
          using \<open>\<And>s. (s, ACrash) \<notin> set (take i_switch trace)\<close> by blast
        show "no_invariant_checks_in_transaction (take i_switch trace)"
          using \<open>no_invariant_checks_in_transaction (take i_switch trace)\<close> by blast
        show "\<not> traceCorrect (take i_switch trace)"
          by (simp add: \<open>\<not> traceCorrect (take i_switch trace)\<close>)
        show "\<And>s. (s, AInvcheck True) \<notin> set (take i_switch trace)"
          by (meson in_set_takeD less.prems(4))
        thus "\<And>s. (s, AInvcheck True) \<notin> set (take i_switch trace)" .
      qed

    next
      case False

      text "Otherwise, remove the action"

      define trace' where "trace' = take (i_switch - 1) trace @ drop i_switch trace"



      have "length trace = Suc (length trace')"
        using \<open>0 < i_switch\<close> \<open>i_switch < length trace\<close> trace'_def by auto


      obtain S' where 
        " initialState program ~~ trace' \<leadsto>* S'"
        unfolding trace'_def
      proof (atomize_elim, rule steps_dropLast_tx)
        show "initialState program ~~ trace \<leadsto>* S"
          by (simp add: less.prems(1))
        \<comment> \<open>TODO lemma\<close>
      qed


      show ?thesis
      proof (rule less.hyps)
        show "length trace' < length trace"
          by (simp add: \<open>length trace = Suc (length trace')\<close>)
        show "initialState program ~~ trace' \<leadsto>* S'"
          by (simp add: \<open>initialState program ~~ trace' \<leadsto>* S'\<close>)
        have [simp]: "min (length trace) i_switch = i_switch"
          by (simp add: \<open>i_switch < length trace\<close> min_simps(2))
        have [simp]: " i_switch + (length trace - Suc i_switch) = length trace - 1"
          by (simp add: Suc_leI \<open>i_switch < length trace\<close>)
        have [simp]: "min (length trace) (i_switch - Suc 0) = i_switch - Suc 0"
          using \<open>i_switch < length trace\<close> by auto
        have [simp]: "i_switch + (length trace - i_switch) = length trace"
          by (simp add: \<open>i_switch < length trace\<close> less_imp_le)
        have [simp]: "Suc (i_switch - Suc 0) = i_switch"
          using Suc_pred \<open>0 < i_switch\<close> by blast


        have h: "i = i_switch" if "i - Suc 0 < i_switch" and "\<not> i < i_switch" for i
          using that(1) that(2) by linarith

        show "packed_trace trace'"
          using `packed_trace trace`
          apply (auto simp add: packed_trace_def trace'_def  nth_append split: if_splits)
          by (metis \<open>Suc (i_switch - Suc 0) = i_switch\<close> a4 h less_SucI linorder_neqE_nat not_less_eq)
        show "\<And>s. (s, ACrash) \<notin> set trace'"
          by (metis Un_iff append_take_drop_id less.prems(3) set_append trace'_def)


        thm no_context_switch_transaction2

        from `initialState program ~~ trace \<leadsto>* S`
        have is_invoc: "get_invoc (trace ! (i_switch - 1)) = invoc"
          using `trace ! i_begin = (invoc, ABeginAtomic tx txns)`
        proof (rule no_context_switch_transaction2)
          show "\<And>j. \<lbrakk>i_begin < j; j \<le> i_switch - 1\<rbrakk> \<Longrightarrow> trace ! j \<noteq> (invoc, AEndAtomic)"
            by (simp add: a3)
          show "packed_trace trace"
            by (simp add: less.prems(2))
          show "\<not> allowed_context_switch (get_action (trace ! j))" if "i_begin < j" "j \<le> i_switch - 1" for j
          proof 
            assume "allowed_context_switch (get_action (trace ! j))"
            have "i_switch \<le> j"
            proof (rule i_switch_min[where i_begin'=i_begin and i_switch'=j])
              show "contextSwitchInTransaction trace i_begin j"
              proof (auto simp add: contextSwitchInTransaction_def)
                show "i_begin < j"
                  by (simp add: that(1))
                show "j < length trace"
                  using a1 that(2) by auto
                show "\<exists>invoc.
                   (\<exists>tx txns. trace ! i_begin = (invoc, ABeginAtomic tx txns)) \<and>
                   (\<forall>ja. i_begin < ja \<and> ja < j \<longrightarrow> trace ! ja \<noteq> (invoc, AEndAtomic)) \<and> allowed_context_switch (get_action (trace ! j))"
                proof (intro exI conjI allI impI)
                  show "trace ! i_begin = (invoc, ABeginAtomic tx txns)"
                    by (simp add: a2)
                  show "allowed_context_switch (get_action (trace ! j))"
                    by (simp add: \<open>allowed_context_switch (get_action (trace ! j))\<close>)
                  show "\<And>ja. i_begin < ja \<and> ja < j \<Longrightarrow> trace ! ja \<noteq> (invoc, AEndAtomic)"
                    using a3 that(2) by auto
                qed
              qed
            qed
            thus False
              using \<open>Suc (i_switch - Suc 0) = i_switch\<close> that(2) by auto
          qed

          show "i_begin \<le> i_switch - 1"
            using a0 by auto
          show "i_switch - 1 < length trace"
            using a1 less_imp_diff_less by blast
        qed

        from `no_invariant_checks_in_transaction trace`
        have "no_invariant_checks_in_transaction (take (i_switch - 1) trace @ drop (Suc (i_switch - 1)) trace)"
        proof (rule maintain_no_invariant_checks_in_transaction2)
          show "i_switch - 1 < length trace"
            by (simp add: \<open>i_switch < length trace\<close> less_imp_diff_less)
          show "
           \<lbrakk>i < i_switch - 1; trace ! i = (invoc, ABeginAtomic tx txns); \<And>ja. \<lbrakk>i < ja; ja < i_switch - 1\<rbrakk> \<Longrightarrow> trace ! ja \<noteq> (invoc, AEndAtomic)\<rbrakk>
             \<Longrightarrow> trace ! (i_switch - 1) \<noteq> (invoc, AEndAtomic)" for i invoc tx txns
              by (metis One_nat_def \<open>Suc (i_switch - Suc 0) = i_switch\<close> is_invoc a0 a2 a3 action.distinct(31) fst_conv le_eq_less_or_eq less_Suc_eq_le snd_conv)
        qed

        show " no_invariant_checks_in_transaction trace'"
          using maintain_no_invariant_checks_in_transaction[OF `no_invariant_checks_in_transaction trace`, where pos="i_switch - 1", simplified]
          using One_nat_def \<open>Suc (i_switch - Suc 0) = i_switch\<close> \<open>no_invariant_checks_in_transaction (take (i_switch - 1) trace @ drop (Suc (i_switch - 1)) trace)\<close> trace'_def by presburger
        show "\<not> traceCorrect trace'"
          using `\<not>traceCorrect trace` trace'_def
          apply (auto simp add: traceCorrect_def)
          by (metis (no_types, lifting) Suc_diff_Suc UnI2 \<open>i_switch + (length trace - Suc i_switch) = length trace - 1\<close> \<open>i_switch + (length trace - i_switch) = length trace\<close> \<open>length trace = Suc (length trace')\<close> \<open>length trace' < length trace\<close> a1 add_less_cancel_left diff_Suc_1 diff_is_0_eq last_action_incorrect last_conv_nth last_drop leD length_drop list.size(3) nth_mem)
        show "initialState program ~~ trace' \<leadsto>* S'"
          by (simp add: \<open>initialState program ~~ trace' \<leadsto>* S'\<close>)
        show "packed_trace trace'"
          by (simp add: \<open>packed_trace trace'\<close>)
        show "\<And>s. (s, ACrash) \<notin> set trace'"
          by (simp add: \<open>\<And>s. (s, ACrash) \<notin> set trace'\<close>)
        show "no_invariant_checks_in_transaction trace'"
          by (simp add: \<open>no_invariant_checks_in_transaction trace'\<close>)
        show " \<not> traceCorrect trace'"
          by (simp add: \<open>\<not> traceCorrect trace'\<close>)
        show "\<And>s. (s, AInvcheck True) \<notin> set trace'"
          by (metis Un_iff append_take_drop_id less.prems(4) set_append trace'_def)
        thus "\<And>s. (s, AInvcheck True) \<notin> set trace'" .
      qed
    qed
  qed
qed

theorem show_programCorrect_noTransactionInterleaving'':
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>
      initialState program ~~ trace \<leadsto>* s; 
      packed_trace trace; 
      \<not>contextSwitchesInTransaction trace;  
      \<And>s. (s, ACrash) \<notin> set trace; 
      no_invariant_checks_in_transaction trace
    \<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving', rule ccontr, goal_cases g)
  case (g trace s)
  obtain trace s
    where "initialState program ~~ trace \<leadsto>* s"
      "packed_trace trace"
      "\<not>contextSwitchesInTransaction trace"
      "\<And>s. (s, ACrash) \<notin> set trace"
      "no_invariant_checks_in_transaction trace"
      "\<not>traceCorrect trace"
    using remove_context_switches_in_transactions[OF g]
    by metis


  then show ?case
    using packedTracesCorrect by blast 
qed


(*
proof (rule show_programCorrect_noTransactionInterleaving')
  fix trace 
  fix s
  assume steps: "initialState program ~~ trace \<leadsto>* s"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, ACrash) \<notin> set trace"
    and no_inv_checks: "no_invariant_checks_in_transaction trace"


  show "traceCorrect trace"


  have induct_measure_ex: "\<exists>x. induct_measure trace x" for trace
    by (rule exI[where x=0], auto simp add: induct_measure_def)

  have induct_measure_bound: "\<exists>bound. \<forall>x. induct_measure trace x \<longrightarrow> x \<le> bound" for trace
    by (rule exI[where x="length trace"], auto simp add: induct_measure_def split: nat.split)

  from steps packed nofail no_inv_checks
  show "traceCorrect trace"
  proof (induct "GREATEST pos'. induct_measure trace pos'"
      arbitrary: trace s rule: less_induct)
    case (less trace')
    show ?case
    proof (cases "Greatest (induct_measure trace')")
      case (0)
      then have [simp]: "(GREATEST a. induct_measure trace' a) = 0" by simp
      have "induct_measure trace' (GREATEST x. induct_measure trace' x) \<and> (\<forall>y. induct_measure trace' y \<longrightarrow> y \<le> (GREATEST x. induct_measure trace' x))"
        by (rule use_Greatest[OF induct_measure_ex induct_measure_bound])
      then have "\<nexists>pos. pos < length trace' \<and>
                         (\<exists>i j tx txns. get_invoc (trace' ! pos) = i \<and> j \<le> pos \<and> trace' ! j = (i, ABeginAtomic tx txns) \<and> \<not> (\<exists>k>j. k < length trace' \<and> trace' ! k = (i, AEndAtomic)))"
        by (simp, auto simp add: induct_measure_def split: nat.splits)
      then have "allTransactionsEnd trace'"
        by (auto simp add: allTransactionsEnd_def, force)
      then show "traceCorrect trace'"
        using less.prems(1) less.prems(2) less.prems(3) less.prems(4) noContextSwitchesInTransaction_when_packed_and_all_end packedTracesCorrect state_wellFormed_init by blast
    next
      case (Suc pos )
      then have [simp]: "(GREATEST x. induct_measure trace' x) = Suc pos" by simp

      have "induct_measure trace' (GREATEST x. induct_measure trace' x) \<and> (\<forall>y. induct_measure trace' y \<longrightarrow> y \<le> (GREATEST x. induct_measure trace' x))"
        by (rule use_Greatest[OF induct_measure_ex induct_measure_bound])
      then have m: "induct_measure trace' (Suc pos)"
        and  m_max: "induct_measure trace' y \<Longrightarrow> y \<le> Suc pos" for y
        by auto

      from m have "pos<length trace' \<and> (\<exists>i j tx txns. get_invoc(trace'!pos) = i \<and>  j\<le>pos \<and> trace'!j = (i, ABeginAtomic tx txns) \<and> (\<nexists>k. k>j \<and> k<length trace' \<and> trace'!k = (i, AEndAtomic)))"
        by (auto simp add: induct_measure_def split: nat.splits)
      from this obtain j tx txns
        where pos_less: "pos < length trace'"
          and j_leq_pos: "j \<le> pos"
          and noEndAtomic_trace': "\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (get_invoc (trace' ! pos), AEndAtomic)"
          and beginAtomic_trace': "trace' ! j = (get_invoc (trace' ! pos), ABeginAtomic tx txns)"
        by auto

      have maxPos: "get_invoc (trace'!pos') \<noteq> get_invoc(trace'!pos)" if "pos' > pos" and "pos' < length trace'" for pos'
        using m_max[where y2="Suc pos'"] that
          beginAtomic_trace' j_leq_pos le_less_trans less_imp_le noEndAtomic_trace'
          by (auto simp add: induct_measure_def, blast )



\<comment> \<open>get new trace by removing action at pos\<close>
      define newTrace where "newTrace = take pos trace' @ drop (Suc pos) trace'"

      have newTraceLen: "length newTrace = length trace' - 1"
        using \<open>pos < length trace'\<close> newTrace_def by auto

      have [simp]: "min (length trace') pos = pos"
        using \<open>pos < length trace'\<close> by auto


      have newTraceIth: "newTrace!i = (if i<pos then trace'!i else trace'!Suc i)" if "i<length newTrace"  for i
        using that \<open>pos < length trace'\<close> by (auto simp add: newTrace_def nth_append)

      have IH: " \<lbrakk>Greatest (induct_measure trace) < Greatest (induct_measure trace'); \<exists>S. initialState program ~~ trace \<leadsto>* S; packed_trace trace; \<And>s. (s, ACrash) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk>
     \<Longrightarrow> traceCorrect trace" for trace
        using less.hyps   by auto 


      have "traceCorrect newTrace"
      proof (rule IH, simp)
        show "Greatest (induct_measure newTrace) < Suc pos"
        proof (rule Greatest_smaller[OF induct_measure_ex induct_measure_bound])
          fix y
          assume a0: "induct_measure newTrace y"
          {
            assume "y > 0" and "y > pos"

            with a0 obtain j tx txns
              where a1: "y < Suc (length newTrace)" 
                and a2: "j < y"
                and a3: "\<forall>k<length newTrace. j < k \<longrightarrow> newTrace ! k \<noteq> (get_invoc (newTrace ! (y-1)), AEndAtomic)"
                and a4: "newTrace ! j = (get_invoc (newTrace ! (y-1)), ABeginAtomic tx txns)"
              using le_imp_less_Suc by (auto simp add: induct_measure_def split: nat.splits, blast)

            have [simp]: "j < length newTrace"
              using a1 a2 by linarith

            have [simp]: "y - Suc 0 < length newTrace"
              using \<open>0 < y\<close> a1 by linarith

            have [simp]: " \<not>(y - Suc 0 < pos)"
              using \<open>pos < y\<close> by linarith

            have [simp]: "Suc (y - Suc 0) = y"
              by (simp add: \<open>0 < y\<close>)

            from a4 have a4': "newTrace ! j = (get_invoc (trace' ! y), ABeginAtomic tx txns)"
              by (simp add: newTraceIth)

            have [simp]: "y < length trace'"
              using \<open>pos < length trace'\<close> a1 newTraceLen by linarith

            have "induct_measure trace' (Suc y)"
              using a4 a3
            proof (auto simp add: induct_measure_def newTraceIth split: if_splits)
              show "\<exists>j\<le>y. (\<exists>tx txns. trace' ! j = (get_invoc (trace' ! y), ABeginAtomic tx txns)) \<and> (\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic))" 
                if c1: "\<forall>k. (j < k \<longrightarrow> k < length newTrace \<longrightarrow> k < pos \<longrightarrow> trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic)) 
                      \<and> (j < k \<longrightarrow> k < length newTrace \<longrightarrow> k < pos \<or> trace' ! Suc k \<noteq> (get_invoc (trace' ! y), AEndAtomic))"
                  and c2: "j < pos" 
                  and c3: "trace' ! j = (get_invoc (trace' ! y), ABeginAtomic tx txns)"
              proof (rule exI[where x=j], auto simp add: c3)
                show "j \<le> y"
                  using a2 by linarith
                show "False" 
                  if "k < length trace'" 
                    and "j < k" 
                    and "trace' ! k = (get_invoc (trace' ! y), AEndAtomic)" for k
                proof (cases "k < pos")
                  case True
                  with c1 have "trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic)"
                    using \<open>pos < y\<close> a1 that(2) by auto
                  then show False
                    using that(3) by blast
                next
                  case False
                  with c1[rule_format, where k="k - 1"]
                  have "trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic)"
                    by (smt One_nat_def Suc_pred \<open>pos < y\<close> \<open>y < length trace'\<close> c2 fst_conv less_Suc_eq maxPos newTraceLen not_less0 not_less_iff_gr_or_eq that(1) that(2))
                  then show False
                    using that(3) by blast
                qed
              qed
              show "\<exists>j\<le>y. (\<exists>tx txns. trace' ! j = (get_invoc (trace' ! y), ABeginAtomic tx txns)) \<and> (\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic))"
                if c1: "\<forall>k<length newTrace. j < k \<longrightarrow> trace' ! Suc k \<noteq> (get_invoc (trace' ! y), AEndAtomic)"
                  and c2: "\<not> j < pos"
                  and c3: "trace' ! Suc j = (get_invoc (trace' ! y), ABeginAtomic tx txns)"
              proof (rule exI[where x="Suc j"], auto simp add: c3)
                show "Suc j \<le> y"
                  using a2 by auto
                show "False" if "k < length trace'"
                  and "Suc j < k"
                  and "trace' ! k = (get_invoc (trace' ! y), AEndAtomic)"
                for k
                proof -
                  from c1[rule_format, where k="k-1"]
                  have "trace' ! k \<noteq> (get_invoc (trace' ! y), AEndAtomic)"
                    by (metis One_nat_def Suc_less_eq Suc_pred linorder_neqE_nat newTraceLen not_less0 that(1) that(2))
                  then show False
                    using that(3) by linarith
                qed
              qed
            qed
            then have "y < Suc pos"
              using Suc_le_lessD m_max by blast
            then have False
              using \<open>pos < y\<close> not_less_eq by blast
          }
          then show "y < Suc pos"
            using not_less_eq by blast
        qed
        show "\<exists>S_newEnd. initialState program ~~ newTrace \<leadsto>* S_newEnd"
        proof -
          
          have "trace' = take pos trace' @ [trace'!pos] @ drop (Suc pos) trace'"
            by (simp add: \<open>pos < length trace'\<close> id_take_nth_drop)

          with \<open>initialState program ~~ trace' \<leadsto>* s\<close>
          obtain S_pos S_pos2 S_end 
            where S_pos_steps: "initialState program ~~ take pos trace' \<leadsto>* S_pos"
              and S_pos_step: "S_pos ~~ trace'!pos \<leadsto> S_pos2"
              and S_pos2_steps: "S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end"
            by (smt append_Cons self_append_conv2 steps_append steps_appendFront)

          then have S_pos2_steps_initial: "initialState program ~~ take (Suc pos) trace' \<leadsto>* S_pos2"
            by (metis \<open>pos < length trace'\<close> steps_step take_Suc_conv_app_nth)



          define invoc where "invoc = get_invoc(trace'!pos)"

          from \<open>trace' ! j = (get_invoc (trace' ! pos), ABeginAtomic tx txns)\<close>
          have beginAtomic: "trace' ! j = (invoc, ABeginAtomic tx txns)"
            by (simp add: invoc_def)

          from \<open>\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (get_invoc (trace' ! pos), AEndAtomic)\<close>
          have noEndAtomic: "\<And>k. \<lbrakk>k<length trace'; j < k\<rbrakk> \<Longrightarrow> trace' ! k \<noteq> (invoc, AEndAtomic)"
            by (simp add: invoc_def)

          have inTx: "currentTransaction S_pos2 invoc \<noteq> None"
          proof (rule inTransaction_trace[OF S_pos2_steps_initial])

            from \<open>trace' ! j = (invoc, ABeginAtomic tx txns)\<close>
            show "take (Suc pos) trace' ! j = (invoc, ABeginAtomic tx txns)"
              by (simp add: \<open>j \<le> pos\<close> le_imp_less_Suc)

            show "j < length (take (Suc pos) trace')"
              by (simp add: Suc_leI \<open>j \<le> pos\<close> \<open>pos < length trace'\<close> le_imp_less_Suc min.absorb2)

            show "\<And>k. \<lbrakk>k < length (take (Suc pos) trace'); j < k\<rbrakk> \<Longrightarrow> take (Suc pos) trace' ! k \<noteq> (invoc, AEndAtomic)"
              by (simp add: noEndAtomic)

            show "\<And>i. (i, ACrash) \<notin> set (take (Suc pos) trace')"
              by (meson in_set_takeD less.prems(3))
          qed

          
          

          

          obtain pos_action where pos_action_def[simp]: "trace'!pos = (invoc, pos_action)"
            by (metis invoc_def prod.collapse)

          from S_pos_step
          have S_pos_step': "S_pos ~~ (invoc, pos_action) \<leadsto> S_pos2" 
            by simp

          have other_invocation: "\<And>a. a \<in> set (drop (Suc pos) trace') \<Longrightarrow> get_invoc a \<noteq> invoc"
            using \<open>invoc = get_invoc (trace' ! pos)\<close> \<open>min (length trace') pos = pos\<close> \<open>\<And>pos'. \<lbrakk>pos < pos'; pos' < length trace'\<rbrakk> \<Longrightarrow> get_invoc (trace' ! pos') \<noteq> get_invoc (trace' ! pos)\<close>
            by (auto simp add: in_set_conv_nth,
             metis Suc_leI add_Suc fst_conv le_add_diff_inverse less_add_Suc1 nat_add_left_cancel_less pos_less)

          have other_invocation'[simp]: "\<And>a. (invoc, a) \<notin> set (drop (Suc pos) trace')" 
            by (meson fst_conv other_invocation)


          from \<open>S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end\<close>
          have S_pos_steps_to_S_end: "S_pos ~~ (invoc, pos_action) # drop (Suc pos) trace' \<leadsto>* S_end"
            using S_pos_step' steps_appendFront by blast


          from \<open>initialState program ~~ take pos trace' \<leadsto>* S_pos\<close>
          have S_pos_wf[simp]: "state_wellFormed S_pos"
            using state_wellFormed_combine state_wellFormed_init
            by (metis contra_subsetD less.prems(3) set_take_subset) 

          have "\<exists>S_new_end. S_pos ~~ drop (Suc pos) trace' \<leadsto>* S_new_end"
          proof (cases "pos_action")
            case (ALocal ok)
            then have [simp]: "pos_action = ALocal ok" by simp

            show ?thesis
              by (rule exI, 
                  rule remove_local_step[OF S_pos_step' S_pos_steps_to_S_end S_pos2_steps],
                  auto simp add: other_invocation)

          next
            case (ANewId x2)

            show ?thesis 
              by (rule exI,
                  rule remove_newId_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps],
                  auto simp add: other_invocation ANewId)

          next
            case (ABeginAtomic x31 x32)

            

            show ?thesis
              by (rule exI,
              rule remove_beginAtomic_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps],
              auto simp add: other_invocation ABeginAtomic)

          next
            case AEndAtomic
            then show ?thesis 
              using \<open>j \<le> pos\<close> \<open>pos < length trace'\<close> local.beginAtomic noEndAtomic by fastforce
          next
            case (ADbOp )
            show ?thesis 
              by (rule exI,
                  rule remove_DBOp_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps],
                  auto simp add: other_invocation ADbOp)
          next
            case (AInvoc)

            \<comment> \<open>We already have an beginAtomic before, so we already have an invocId\<close>
            have "invocationOp S_pos invoc \<noteq> None"
            proof -

              have f4: "j < length (take pos trace')"
                using AInvoc Pair_inject j_leq_pos le_eq_less_or_eq local.beginAtomic by auto
              have f5: "take pos trace' ! j = (get_invoc (trace' ! pos), ABeginAtomic tx txns)"
                using AInvoc Pair_inject j_leq_pos le_eq_less_or_eq local.beginAtomic by auto

              have "currentTransaction S_pos (get_invoc (trace' ! pos)) \<noteq> None"
                using [[smt_timeout=60]]
                by (smt S_pos_steps \<open>min (length trace') pos = pos\<close> f4 f5 inTransaction_trace in_set_takeD length_take less.prems(3) less_trans noEndAtomic_trace' nth_take pos_less)
              then show ?thesis
                by (metis S_pos_wf invoc_def wellFormed_invoc_notStarted(1))
            qed



            with AInvoc
            show ?thesis
              using S_pos_step inTx by (auto simp add: step.simps inTx)
          next
            case (AReturn x7)
            then show ?thesis 
              using S_pos_step inTx by (auto simp add: step.simps inTx)
          next
            case ACrash
            then show ?thesis
              using \<open>pos < length trace'\<close> \<open>\<And>s. (s, ACrash) \<notin> set trace'\<close> nth_mem by fastforce
          next
            case (AInvcheck x92)
            then have "S_pos2 = S_pos"
              using S_pos_step by (auto simp add: step.simps)
            with \<open>S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end\<close> 
            show ?thesis by blast
          qed


          with \<open>initialState program ~~ take pos trace' \<leadsto>* S_pos\<close>
          show "\<exists>S_newEnd. initialState program ~~ newTrace \<leadsto>* S_newEnd"
            by (auto simp add: newTrace_def  steps_append)
        qed

        show "packed_trace newTrace"
          using \<open>packed_trace trace'\<close> 
        proof (auto simp add: newTrace_def packed_trace_def nth_append)


          show "allowed_context_switch (get_action (trace' ! i))"
            if c0: "\<forall>i>0. i < length trace' \<longrightarrow> get_invoc (trace' ! (i - Suc 0)) \<noteq> get_invoc (trace' ! i) \<longrightarrow> allowed_context_switch (get_action (trace' ! i))"
              and c1: "i - Suc 0 < pos"
              and c2: "i < pos"
              and c3: "0 < i"
              and c4: "get_invoc (trace' ! (i - Suc 0)) \<noteq> get_invoc (trace' ! i)"
            for  i
            using \<open>pos < length trace'\<close> dual_order.strict_trans that by blast


          show "allowed_context_switch (get_action (trace' ! Suc i))"
            if c0: "\<forall>i>0. i < length trace' \<longrightarrow> get_invoc (trace' ! (i - Suc 0)) \<noteq> get_invoc (trace' ! i) \<longrightarrow> allowed_context_switch (get_action (trace' ! i))"
              and c1: "i - Suc 0 < pos"
              and c2: "\<not> i < pos"
              and c3: "i < pos + (length trace' - Suc pos)"
              and c4: "get_invoc (trace' ! (i - Suc 0)) \<noteq> get_invoc (trace' ! Suc i)"
            for  i
            using that by (metis (no_types, hide_lams) Suc_pred diff_Suc_Suc diff_zero less_add_same_cancel1 maxPos not_gr_zero not_less_eq not_less_less_Suc_eq zero_less_Suc zero_less_diff)
        qed
        show " \<And>s. (s, ACrash) \<notin> set newTrace"
          using \<open>\<And>s. (s, ACrash) \<notin> set trace'\<close> by (auto simp add: newTrace_def dest: in_set_takeD in_set_dropD )

        show "no_invariant_checks_in_transaction newTrace"
        proof (cases "get_action (trace' ! pos) \<noteq> AEndAtomic")
          case True
          show ?thesis 
            unfolding newTrace_def
            by (rule maintain_no_invariant_checks_in_transaction[OF \<open>no_invariant_checks_in_transaction trace'\<close> True \<open>pos < length trace'\<close>])
          next
            case False
            with \<open>no_invariant_checks_in_transaction trace'\<close>
            show ?thesis 
              by (cases "trace' ! pos",
                  insert beginAtomic_trace' j_leq_pos le_eq_less_or_eq noEndAtomic_trace' pos_less,
                  auto simp add: newTrace_def no_invariant_checks_in_transaction_def nth_append)
          qed
        qed

\<comment> \<open>because no inv-checks in transaction\<close>
      have removedNoInvCheck: "get_action (trace'!pos) \<noteq> AInvcheck v" for v
        
        using \<open>no_invariant_checks_in_transaction trace'\<close>
        by (auto simp add: no_invariant_checks_in_transaction_def,
            smt \<open>pos < length trace' \<and> (\<exists>i j tx txns. get_invoc (trace' ! pos) = i \<and> j \<le> pos \<and> trace' ! j = (i, ABeginAtomic tx txns) \<and> \<not> (\<exists>k>j. k < length trace' \<and> trace' ! k = (i, AEndAtomic)))\<close> allowed_context_switch_def allowed_context_switch_simps(9) le_eq_less_or_eq min_def min_less_iff_conj prod.collapse prod.inject)



      show "traceCorrect trace'"
      proof (auto simp add: traceCorrect_def newTrace_def in_set_conv_nth, rule ccontr )
        fix s i action
        assume  "i < length trace'" and "trace' ! i = (s, action)" and "\<not>actionCorrect action"


        {
          assume "i<pos"
          then have "actionCorrect (get_action (newTrace ! i))"
            by (smt One_nat_def Suc_less_SucD Suc_pred \<open>traceCorrect newTrace\<close> length_greater_0_conv less_trans_Suc list.size(3) newTraceLen not_less0 nth_mem pos_less traceCorrect_def)
          then have "actionCorrect (get_action (trace' ! i))"
            using \<open>i < pos\<close> \<open>pos < length trace'\<close> newTraceIth newTraceLen by force
        }
        moreover
        {
          assume "i = pos"
          then have "actionCorrect (get_action (newTrace ! i))"

            thm removedNoInvCheck

            using \<open>trace' ! i = (s, AInvcheck False)\<close> removedNoInvCheck by auto
          then have "trace' ! i \<noteq> (s, AInvcheck False)"
            using \<open>i = pos\<close> removedNoInvCheck by fastforce
        }
        moreover
        {
          assume "i>pos"
          then have "newTrace ! i \<noteq> (s, AInvcheck False)"
            by (smt Suc_leI Suc_less_SucD \<open>i < length trace'\<close> \<open>trace' ! i = (s, AInvcheck False)\<close> \<open>traceCorrect newTrace\<close> diff_Suc_1 in_set_conv_nth leD less_imp_Suc_add newTraceIth newTraceLen traceCorrect_def)
          then have "trace' ! i \<noteq> (s, AInvcheck False)"
            by (smt Suc_leI Suc_less_SucD \<open>i < length trace'\<close> \<open>pos < i\<close> \<open>traceCorrect newTrace\<close> diff_Suc_1 in_set_conv_nth leD less_imp_Suc_add newTraceIth newTraceLen traceCorrect_def)
        }
        ultimately have "trace' ! i \<noteq> (s, AInvcheck False)"
          using antisym_conv3 by blast
        then show False
          using \<open>trace' ! i = (s, AInvcheck False)\<close> by blast
      qed
    qed
  qed
qed

*)

end
