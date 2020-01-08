section "Packed Traces without Failures and Invariant Checks"
theory packed_nofails_noinvchecks
imports no_failing_invchecks packed_no_fails consistency
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
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; \<And>s. (s, AInvcheck True) \<notin> set trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving)
  fix trace
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"

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
        
      show " \<And>s. (s, AFail) \<notin> set trace'"
        by (auto simp add: trace'_def nofail)

      show "\<And>s. (s, AInvcheck True) \<notin> set trace'"
        by  (auto simp add: trace'_def isNotTrueInvcheck_def)
    qed
    then have "traceCorrect trace"
      by (auto simp add: trace'_def traceCorrect_def isNotTrueInvcheck_def)

    then show "False"
      using a by blast
  qed
qed

lemma move_invariant_checks_out_of_transactions:
  assumes "initialState program ~~ trace \<leadsto>* S"
    and "packed_trace trace"
    and "\<And>s. (s, AFail) \<notin> set trace"
    and "\<And>s. (s, AInvcheck True) \<notin> set trace"
    and "length trace > 0"
    and "last trace = (s, AInvcheck False)"
    and "\<And>i s'. i<length trace - 1 \<Longrightarrow> trace!i \<noteq> (s', AInvcheck False)"
  shows "\<exists>trace' s'. 
          (\<exists>S'. initialState program ~~ trace' \<leadsto>* S')
        \<and> packed_trace trace'
        \<and> (\<forall>s. (s, AFail) \<notin> set trace')
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

    thm less

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
        show "\<And>j. \<lbrakk>ib < j; j < length (take (length trace - 2) trace)\<rbrakk> \<Longrightarrow> take (length trace - 2) trace ! j \<noteq> (s, AFail)"
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
        case AFail
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

        show "\<And>s'. (s', AFail) \<notin> set (take (length trace - 2) trace @ [(s, AInvcheck False)])"
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

        show "\<And>s'. (s', AFail) \<notin> set (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
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
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving_no_passing_invchecks)
  fix trace
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"
    and noTrueInvs: "\<And>s. (s, AInvcheck True) \<notin> set trace"



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
       insert a,
       auto simp add: traceCorrect_def in_set_conv_nth)

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
                  (\<forall>s. (s, AFail) \<notin> set trace') \<and>
                  (\<forall>s. (s, AInvcheck True) \<notin> set trace') \<and> last trace' = (s', AInvcheck False) \<and> 0 < length trace' \<and> no_invariant_checks_in_transaction trace'"
    proof (rule  move_invariant_checks_out_of_transactions[OF steps_Si])
      show "packed_trace (take (Suc i) trace)"
        by (metis isPrefix_appendI packed prefixes_are_packed trace_split3)
      show "\<And>s. (s, AFail) \<notin> set (take (Suc i) trace)"
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
      by (auto,
          metis last_in_set packedTracesCorrect traceCorrect_def)
  qed
qed

definition "induct_measure" where "induct_measure  \<equiv> \<lambda>trace. \<lambda>pos'.
    case pos' of
        0 \<Rightarrow> True
      | Suc pos \<Rightarrow>  pos<length trace \<and> (\<exists>i j tx txns. get_invoc(trace!pos) = i \<and>  j\<le>pos \<and> trace!j = (i, ABeginAtomic tx txns) \<and> (\<nexists>k. k>j \<and> k<length trace \<and> trace!k = (i, AEndAtomic)))" 


thm show_programCorrect_noTransactionInterleaving'
text \<open>
 To show that a program is correct, we only have to consider packed and finished transactions
\<close>
theorem show_programCorrect_noTransactionInterleaving'':
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; allTransactionsEnd trace;  \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving')
  fix trace 
  fix s
  assume steps: "initialState program ~~ trace \<leadsto>* s"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"
    and no_inv_checks: "no_invariant_checks_in_transaction trace"



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
        using "less.prems" packedTracesCorrect by blast
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

      have IH: " \<lbrakk>Greatest (induct_measure trace) < Greatest (induct_measure trace'); \<exists>S. initialState program ~~ trace \<leadsto>* S; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk>
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

            show "\<And>i. (i, AFail) \<notin> set (take (Suc pos) trace')"
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


          thm S_pos2_steps

          from \<open>S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end\<close>
          have S_pos_steps_to_S_end: "S_pos ~~ (invoc, pos_action) # drop (Suc pos) trace' \<leadsto>* S_end"
            using S_pos_step' steps_appendFront by blast


          from \<open>initialState program ~~ take pos trace' \<leadsto>* S_pos\<close>
          have S_pos_wf[simp]: "state_wellFormed S_pos"
            using state_wellFormed_combine state_wellFormed_init
            by (metis contra_subsetD less.prems(3) set_take_subset) 

          have "\<exists>S_new_end. S_pos ~~ drop (Suc pos) trace' \<leadsto>* S_new_end"
          proof (cases "pos_action")
            case ALocal
            then have [simp]: "pos_action = ALocal" by simp

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
            case AFail
            then show ?thesis
              using \<open>pos < length trace'\<close> \<open>\<And>s. (s, AFail) \<notin> set trace'\<close> nth_mem by fastforce
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
        show " \<And>s. (s, AFail) \<notin> set newTrace"
          using \<open>\<And>s. (s, AFail) \<notin> set trace'\<close> by (auto simp add: newTrace_def dest: in_set_takeD in_set_dropD )

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
      proof (auto simp add: traceCorrect_def newTrace_def in_set_conv_nth)
        fix s i
        assume  "i < length trace'" and "trace' ! i = (s, AInvcheck False)"

        {
          assume "i<pos"
          then have "newTrace ! i \<noteq> (s, AInvcheck False)"
            using \<open>traceCorrect newTrace\<close> \<open>pos < length trace'\<close> newTrace_def \<open>trace' ! i = (s, AInvcheck False)\<close> by (auto simp add: traceCorrect_def in_set_conv_nth)
          then have "trace' ! i \<noteq> (s, AInvcheck False)"
            using \<open>i < pos\<close> \<open>pos < length trace'\<close> newTraceIth newTraceLen by force
        }
        moreover
        {
          assume "i = pos"
          then have "newTrace ! i \<noteq> (s, AInvcheck False)"
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



(* TODO move lemmas below*)

definition noContextSwitchesInTransaction :: "('proc, 'operation, 'any) trace \<Rightarrow> bool" where
  "noContextSwitchesInTransaction tr \<equiv> \<forall>i k invoc. 
    i < k \<and> k \<le> length tr 
   \<and> (\<exists>tx txns.  tr!i = (invoc, ABeginAtomic tx txns))
   \<and> (\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic) )
   \<longrightarrow> (\<forall>j. i < j \<and> j < k \<longrightarrow>  \<not> allowed_context_switch (get_action (tr!j)))"

lemma use_noContextSwitchesInTransaction:
  assumes a0: "noContextSwitchesInTransaction tr"
    and a1: " tr!i = (invoc, ABeginAtomic tx txns)"
    and a2: "i < k" 
    and a3: "k \<le> length tr "
    and a4: "\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic)"
    and a5: "i < j"
    and a6: "j < k"
  shows "\<not>allowed_context_switch (get_action (tr!j))"
proof (simp add: allowed_context_switch_def; intro conjI allI)

  show "get_action (tr ! j) \<noteq> ABeginAtomic txId txns" for txId txns
    by (metis (full_types) a0 a1 a2 a3 a4 a5 a6 allowed_context_switch_simps(3) noContextSwitchesInTransaction_def)

  show " get_action (tr ! j) \<noteq> AInvoc p " for p 
    by (metis (full_types) a0 a1 a2 a3 a4 a5 a6 allowed_context_switch_simps(6) noContextSwitchesInTransaction_def)
qed



lemma prefixes_noContextSwitchesInTransaction:
  assumes "noContextSwitchesInTransaction tr'" 
    and "isPrefix tr tr'"
  shows "noContextSwitchesInTransaction tr"
proof (auto simp add: noContextSwitchesInTransaction_def)
fix i k j invoc tx txns
assume a0: "k \<le> length tr"
   and a1: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
   and a2: "tr ! i = (invoc, ABeginAtomic tx txns)"
   and a3: "i < j"
   and a4: "j < k"
   and a5: "allowed_context_switch (get_action (tr ! j))"


  have "\<not>allowed_context_switch (get_action (tr' ! j))"
  proof (rule use_noContextSwitchesInTransaction[OF \<open>noContextSwitchesInTransaction tr'\<close>, where i=i and j=j and k=k])
    show "tr' ! i = (invoc, ABeginAtomic tx txns)"
      using a0 a2 a3 a4 assms(2) isPrefix_same by fastforce
    show "i < j " using a3 .
    show "j < k" using a4 .
    show "i < k"
      using a3 a4 less_trans by blast 
    show " k \<le> length tr'"
      by (meson a0 assms(2) isPrefix_len leD le_trans nat_le_linear)
    show " \<forall>j. i < j \<and> j < k \<longrightarrow> tr' ! j \<noteq> (invoc, AEndAtomic)"
      using a0 a1 assms(2) isPrefix_same by fastforce
  qed
  then show "False"
    using a0 a4 a5 assms(2) isPrefix_same by fastforce
qed

lemma packed_trace_prefix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace xs"
  using assms isPrefix_appendI prefixes_are_packed by blast

lemma packed_trace_postfix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace ys"
  using assms  proof (auto simp add: packed_trace_def )
  fix i
  assume a0: "\<forall>i>0. i < length xs + length ys \<longrightarrow>
                 get_invoc ((xs @ ys) ! (i - Suc 0)) \<noteq> get_invoc ((xs @ ys) ! i) \<longrightarrow>
                 allowed_context_switch (get_action ((xs @ ys) ! i))"
    and a1: "0 < i"
    and a2: "i < length ys"
    and a3: "get_invoc (ys ! (i - Suc 0)) \<noteq> get_invoc (ys ! i)"

  have "(i + length xs) < length xs + length ys "
    by (simp add: a2)

  moreover have "get_invoc ((xs @ ys) ! ((i + length xs) - Suc 0)) \<noteq> get_invoc ((xs @ ys) ! (i + length xs))"
    using a1 a3 by (auto simp add: nth_append)

  ultimately have 
    "allowed_context_switch (get_action ((xs @ ys) ! (i + length xs)))"
    using a0 a1 by simp

  from this
  show "allowed_context_switch (get_action (ys ! i))"
    by (auto simp add: nth_append)
qed

lemma packed_trace_take:
  assumes "packed_trace tr"
  shows "packed_trace (take i tr)"
  by (metis append_take_drop_id assms packed_trace_prefix)


lemma packed_trace_drop:
  assumes "packed_trace tr"
  shows "packed_trace (drop i tr)"
  by (metis append_take_drop_id assms packed_trace_postfix)






lemma noContextSwitchAllowedInTransaction:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and  packed: "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and beginAtomic: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and noEndAtomic: "\<forall>j. i < j \<and> j < k \<longrightarrow> get_action (tr!j) \<noteq> AEndAtomic"
    and sameInvoc: "get_invoc (tr!j) = invoc"
    and i_less_j: "i<j" 
    and k_less_k: "j<k"
    and k_length: "k\<le>length tr"
    and wf: "state_wellFormed S"
  shows "\<not>allowed_context_switch (get_action (tr ! j))"
proof 
  assume a0: "allowed_context_switch (get_action (tr ! j))"

  from steps
  have "S ~~ take j tr @ (tr!j # drop (Suc j) tr) \<leadsto>* S'"
    by (metis id_take_nth_drop k_length k_less_k less_le_trans)

  from this
  obtain S1 S2
    where "S ~~ take j tr \<leadsto>* S1"
      and "S1 ~~ tr!j \<leadsto> S2"
    using steps_append steps_appendFront by blast 

  have h: "\<forall>z ps za n i t C. 
            \<not> (z ~~ ps \<leadsto>* za) 
          \<or> \<not> n < length ps 
          \<or> ps ! n \<noteq> (i, ABeginAtomic t C) 
          \<or> (\<exists>na. (n < na \<and> na < length ps) \<and> ps ! na = (i, AFail)) 
          \<or> (\<exists>na. (n < na \<and> na < length ps) \<and> ps ! na = (i, AEndAtomic)) 
          \<or> currentTransaction za i \<triangleq> t"
    by (meson currentTransaction2)


  have "get_invoc (tr!j) = invoc"
    using i_less_j k_less_k sameInvoc by blast

  moreover have "currentTransaction S1 invoc \<triangleq> tx"
    using `S ~~ take j tr \<leadsto>* S1`
  proof (rule currentTransaction2)
    show "i < length (take j tr)"
      using i_less_j k_length k_less_k by auto
    show "take j tr ! i = (invoc, ABeginAtomic tx txns)"
      by (simp add: i_less_j local.beginAtomic)
    show "\<And>ja. \<lbrakk>i < ja; ja < length (take j tr)\<rbrakk> \<Longrightarrow> take j tr ! ja \<noteq> (invoc, AFail)"
      using noFail nth_mem by fastforce
    show " \<And>ja. \<lbrakk>i < ja; ja < length (take j tr)\<rbrakk> \<Longrightarrow> take j tr ! ja \<noteq> (invoc, AEndAtomic)"
      using k_less_k noEndAtomic by auto
  qed

  moreover have "localState S1 invoc \<noteq> None"
    using \<open>S ~~ take j tr \<leadsto>* S1\<close> \<open>currentTransaction S1 invoc \<triangleq> tx\<close> inTransaction_localState local.wf state_wellFormed_combine
    by (metis noFail set_rev_mp set_take_subset) 
  ultimately 
  show False
    using  \<open>S1 ~~ tr!j \<leadsto> S2\<close> and \<open>allowed_context_switch (get_action (tr ! j))\<close>
    by (auto simp add: step.simps allowed_context_switch_def)
qed

lemma noContextSwitchesInTransaction_when_packed_and_all_end:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "allTransactionsEnd tr"
    and "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and wf: "state_wellFormed S"
  shows "noContextSwitchesInTransaction tr"
proof (auto simp add: noContextSwitchesInTransaction_def)
  fix i k j invoc tx txns
  assume a0: "k \<le> length tr"
    and a1: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and a3: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and a4: "i < j"
    and a5: "j < k"
    and a6: "allowed_context_switch (get_action (tr ! j))"


  obtain j_min 
    where a4_min: "i < j_min"
      and a5_min: "j_min < k"
      and a6_min: "allowed_context_switch (get_action(tr!j_min))"
      and j_min_min: "\<forall>j. i<j \<and> j<k \<and> allowed_context_switch (get_action (tr ! j)) \<longrightarrow> j_min \<le> j"
  proof (atomize_elim,
    rule exI[where x="Least (\<lambda>j. i<j \<and> j<k \<and> allowed_context_switch (get_action (tr ! j)))"],
    rule LeastI2_wellorder_ex, auto)
    show "\<exists>x>i. x < k \<and> allowed_context_switch (get_action (tr ! x))"
      using a4 a5 a6 by auto
  qed

  have tr_split: "tr = take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr"
    using a0 a5_min id_take_nth_drop less_le_trans by (auto, blast)
  with steps have tr_split_steps: "S ~~ take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr \<leadsto>* S'" by simp
  from this
  obtain S_j_min_pre S_j_min 
    where S_j_min_pre_steps: "S ~~ take j_min tr \<leadsto>* S_j_min_pre"
      and j_min_step: "S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min"
      and S_j_min_steps: "S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'"
    by (auto simp add: steps_append steps_appendFront  )


  have S_j_min_pre_wf: "state_wellFormed S_j_min_pre"
    by (meson S_j_min_pre_steps local.wf noFail rev_subsetD set_take_subset state_wellFormed_combine)

  then have "state_wellFormed S_j_min"
    using S_j_min_pre_steps j_min_step local.wf state_wellFormed_combine steps_step
    by (metis (no_types, lifting) append_assoc append_same_eq append_take_drop_id in_set_takeD noFail tr_split) 



  \<comment> \<open>we are still in a transaction:\<close>
  have currentTx: "currentTransaction S_j_min_pre invoc \<triangleq> tx"
    using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close>
      
  proof (rule currentTransaction[THEN iffD1])
    show "i < length (take j_min tr)"
      using a0 a4_min a5_min by auto

    show "take j_min tr ! i = (invoc, ABeginAtomic tx txns)"
      using \<open>i < length (take j_min tr)\<close> a1 by auto

    show " \<forall>j. i < j \<and> j < length (take j_min tr) \<longrightarrow>
        take j_min tr ! j \<noteq> (invoc, AEndAtomic) \<and> take j_min tr ! j \<noteq> (invoc, AFail)"
      using a3 a5_min noFail nth_mem by fastforce
  qed

  then have ls: "localState S_j_min_pre invoc \<noteq> None"
    using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> inTransaction_localState local.wf state_wellFormed_combine
    using S_j_min_pre_wf by blast


  with \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close> 
    and \<open>allowed_context_switch (get_action(tr!j_min))\<close>
  have "get_invoc (tr!j_min) \<noteq> invoc"
    by (auto simp add: step.simps currentTx allowed_context_switch_simps)



  \<comment> \<open>there must be an endAtomic for the beginAtomic\<close>
  from \<open>allTransactionsEnd tr\<close> 
  obtain i_end 
    where "tr!i_end = (invoc, AEndAtomic)" and "i_end \<ge> k" and "i_end < length tr"
  proof (auto simp add: allTransactionsEnd_def, atomize_elim)
    assume a0: "\<forall>i j. j < length tr \<longrightarrow> (\<exists>tx txns. tr ! j = (i, ABeginAtomic tx txns)) \<longrightarrow> 
           (\<exists>k>j. k < length tr \<and> tr ! k = (i, AEndAtomic))"

    have "\<exists>k>i. k < length tr \<and> tr ! k = (invoc, AEndAtomic)"
    proof (rule a0[rule_format, where j=i and i=invoc])
      show "i < length tr"
        using a4_min not_le tr_split by fastforce
      show "\<exists>tx txns. tr ! i = (invoc, ABeginAtomic tx txns)"
        using a1 by auto
    qed

    thus "\<exists>i_end. tr ! i_end = (invoc, AEndAtomic) \<and> k \<le> i_end \<and> i_end < length tr"
      using a3 less_imp_le not_le by (auto, blast)
  qed


  \<comment> \<open>this means, we must go back to invoc. Take the first index where we go back to invoc\<close>
  from this
  obtain back_min 
    where "back_min > j_min"
      and "back_min \<le> length tr"
      and "get_invoc (tr!back_min) = invoc"
      and back_min_min: "\<forall>i. i > j_min \<and> i < length tr \<and> get_invoc (tr!i) = invoc \<longrightarrow> i\<ge> back_min"
  proof (atomize_elim, intro exI[where x="Least (\<lambda>i. i > j_min \<and> i < length tr \<and> get_invoc (tr!i) = invoc)"] conjI)
    assume a0: "tr ! i_end = (invoc, AEndAtomic)"
      and a1: "k \<le> i_end"
      and a2: "i_end < length tr"
      and a3: "tr ! i_end = (invoc, AEndAtomic)"
      and a4: "k \<le> i_end"
      and a5: "i_end < length tr"



    have "i_end>j_min"
      using a1 a5_min order.strict_trans2 by blast 

    moreover have "get_invoc (tr ! i_end) = invoc"
      by (simp add: a0)

    ultimately
    have eX: "\<exists>x>j_min. x < length tr \<and> get_invoc (tr ! x) = invoc"
      using a2 by auto

    show "j_min < (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc)"
      using eX by (rule LeastI2_wellorder_ex, auto)

    show "(LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc) \<le> length tr"
      using eX by (rule LeastI2_wellorder_ex, auto)

    show "get_invoc (tr ! (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc)) = invoc"
      using eX by (rule LeastI2_wellorder_ex, auto)



    show "\<forall>i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc \<longrightarrow> (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc) \<le> i"
    proof auto

      show "(LEAST ia. j_min < ia \<and> ia < length tr \<and> get_invoc (tr ! ia) = get_invoc (tr ! i)) \<le> i"
        if c0: "j_min < i"
          and c1: "i < length tr"
          and c2: "invoc = get_invoc (tr ! i)"
        for  i
        by (simp add: Least_le c0 c1)
    qed
  qed

  have "back_min < length tr"
    by (metis \<open>back_min \<le> length tr\<close> \<open>i_end < length tr\<close> \<open>k \<le> i_end\<close> \<open>tr ! i_end = (invoc, AEndAtomic)\<close> a5_min back_min_min fst_conv leD le_imp_less_or_eq less_le_trans)


  \<comment> \<open>this must be a valid context switch, since it is the first to change back\<close>
  from \<open>packed_trace tr\<close>
  have "allowed_context_switch (get_action (tr ! back_min))"
  proof (rule use_packed_trace)
    show "0 < back_min"
      using \<open>j_min < back_min\<close> gr_implies_not0 by blast

    show "back_min < length tr"
      by (simp add: \<open>back_min < length tr\<close>)
    have "get_invoc (tr ! (back_min - 1)) \<noteq> invoc"
      using back_min_min[rule_format, where i="back_min-1"]
       \<open>back_min < length tr\<close> \<open>get_invoc (tr ! j_min) \<noteq> invoc\<close> \<open>j_min < back_min\<close> not_less_less_Suc_eq by fastforce

    then show "get_invoc (tr ! (back_min - 1)) \<noteq> get_invoc (tr ! back_min)"
      by (auto simp add: \<open>get_invoc (tr!back_min) = invoc\<close>)
  qed

  \<comment> \<open>but since we are already in a transaction, that cannot work\<close>

  have "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ drop back_min tr"
    by (auto simp add: Suc_leI \<open>back_min \<le> length tr\<close> \<open>j_min < back_min\<close> min.absorb2 min_diff nth_append add.commute intro: nth_equalityI)
  then have "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr"
    using Cons_nth_drop_Suc \<open>back_min < length tr\<close> by fastforce

  with \<open>S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'\<close>
  have "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr \<leadsto>* S'"
    by force
  from this
  obtain S_back_min_pre S_back_min
    where S_back_min_pre_steps: "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre"
      and back_min_step: "S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min"
      and S_back_min_steps: "S_back_min ~~ drop (Suc back_min) tr \<leadsto>* S'"
    by  (auto simp add: steps_append steps_appendFront )


  from S_back_min_pre_steps \<open>state_wellFormed S_j_min\<close>
  have "state_wellFormed S_back_min_pre"
    by (meson state_wellFormed_combine in_set_dropD in_set_takeD noFail)

  from \<open>currentTransaction S_j_min_pre invoc \<triangleq> tx\<close>
  have "currentTransaction S_j_min invoc \<triangleq> tx"
    using \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close> 
    using \<open>get_invoc (tr ! j_min) \<noteq> invoc\<close> by (auto simp add: step.simps )


  from  \<open>S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre\<close>
  have "currentTransaction S_back_min_pre invoc \<triangleq> tx"
    
  proof (rule currentTransaction_unchangedInternalSteps4(1))
    show "currentTransaction S_j_min invoc \<triangleq> tx"
      by (simp add: \<open>currentTransaction S_j_min invoc \<triangleq> tx\<close>) 
    show "state_wellFormed S_j_min"
    proof (rule state_wellFormed_combine[OF wf])
      show " S ~~ take j_min tr @ [tr ! j_min] \<leadsto>* S_j_min"
        using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close>
        using steps_step by blast 
      show "\<And>i. (i, AFail) \<notin> set (take j_min tr @ [tr ! j_min])"
        using noFail \<open>back_min < length tr\<close> \<open>j_min < back_min\<close> 
        by (auto, metis a6_min allowed_context_switch_simps(8) snd_conv, meson in_set_takeD)
    qed

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, AEndAtomic)"
      by (auto simp add: in_set_conv_nth,
       metis add.commute add_Suc back_min_min fst_conv less_add_Suc1 less_diff_conv linorder_not_le)

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, AFail)"
      by (meson in_set_dropD in_set_takeD noFail)
  qed





  then have "localState S_back_min_pre invoc \<noteq> None"
    using \<open>state_wellFormed S_back_min_pre\<close>
    using inTransaction_localState by blast



  \<comment> \<open>a contradiction\<close>
  with \<open>S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min\<close>
    and \<open>allowed_context_switch (get_action (tr ! back_min))\<close>
    and \<open>get_invoc (tr ! back_min) = invoc\<close>
    and \<open>currentTransaction S_back_min_pre invoc \<triangleq> tx\<close>
    and \<open>localState S_back_min_pre invoc \<noteq> None\<close>
  show "False"
    by (auto simp add:step.simps allowed_context_switch_simps)

qed




lemma only_one_commmitted_transaction_h:
  assumes  steps: "S ~~ tr \<leadsto>* S'"
    and wf: "state_wellFormed S"
    and packed: "packed_trace tr"
    and status: "transactionStatus S' tx \<triangleq> Uncommitted"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noSwitch: "noContextSwitchesInTransaction tr"
    and initial: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "(currentTransaction S' (get_invoc (last tr)) \<triangleq> tx) 
      \<and> (\<exists>i txns. i<length tr \<and> tr!i = (get_invoc (last tr), ABeginAtomic tx txns)
           \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)))" 
  using steps packed status noFails noSwitch proof (induct arbitrary: tx  rule: steps_induct)
  case initial
  with \<open>transactionStatus S tx \<noteq> Some Uncommitted\<close> show ?case by blast
next
  case (step S' tr a S'' tx)

  from \<open>noContextSwitchesInTransaction (tr @ [a])\<close>
  have noContextSwitch: "noContextSwitchesInTransaction tr"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast

  { 
    assume "transactionStatus S' tx \<triangleq> Uncommitted"
    with \<open> S ~~ tr \<leadsto>* S'\<close>
    have IH: "currentTransaction S' (get_invoc (last tr)) \<triangleq> tx 
          \<and> (\<exists>i txns. i<length tr \<and> tr!i = (get_invoc (last tr), ABeginAtomic tx txns)
                   \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)))"
      using isPrefix_appendI prefixes_are_packed step.IH \<open>\<And>s. (s, AFail) \<notin> set (tr @ [a])\<close> \<open>packed_trace (tr @ [a])\<close> noContextSwitch
      by (metis butlast_snoc in_set_butlastD) 



    obtain i' action where a_split[simp]: "a = (i',action)"
      by fastforce

    from IH
    have IH1: "currentTransaction S' (get_invoc (last tr)) \<triangleq> tx"
      by blast


    from IH
    obtain i txns
      where i1: "i<length tr"
        and i2: "tr!i = (get_invoc (last tr), ABeginAtomic tx txns)"
        and i3: "\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)"
      by fastforce

    then have "(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)"
      by (simp add: nth_append_first)

    have "a \<noteq> (get_invoc (last tr), AEndAtomic)" 
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open>transactionStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps IH1 split: if_splits )


    from \<open>noContextSwitchesInTransaction (tr @ [a])\<close> \<open>(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)\<close>
    have "\<not>allowed_context_switch (get_action ((tr@[a])!length tr))" 
    proof (rule use_noContextSwitchesInTransaction)
      show "\<forall>j. i < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last tr), AEndAtomic)"
        using \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close> i3 less_Suc_eq nth_append_first by fastforce
      show "i < length tr"
        by (simp add: i1)
      show "Suc (length tr) \<le> length (tr @ [a])"
        by simp
      show "i < Suc (length tr)"
        by (simp add: i1 less_SucI)
      show "length tr < Suc (length tr)"
        by simp
    qed
    then have "\<not>allowed_context_switch action"
      by simp 

    then have i'_simps: "i' = get_invoc (last tr)"
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"]
      apply (auto simp add: nth_append)
      by (metis i1 One_nat_def gr_implies_not_zero last_conv_nth length_0_conv)




    from \<open>S' ~~ a \<leadsto> S''\<close> IH1
    have "currentTransaction S'' (get_invoc (last (tr@[a]))) \<triangleq> tx"
      using \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close>  \<open>\<And>s. (s, AFail) \<notin> set (tr @ [a])\<close> by (auto simp add: step.simps  i'_simps)

    moreover have "(\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      apply (rule exI[where x=i])
      apply (rule exI[where x=txns])
      apply (auto simp add: )
      using i1 less_SucI apply blast
      using \<open>(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)\<close> a_split i'_simps apply blast
      by (metis \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close> a_split i'_simps i3 less_SucE nth_append_first nth_append_length)

    ultimately have "currentTransaction S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      by simp
  }
  moreover
  {
    assume "transactionStatus S' tx \<noteq> Some Uncommitted"
    then have  "currentTransaction S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open> transactionStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps split: if_splits)
  }
  ultimately show "currentTransaction S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
    by auto
qed




lemma at_most_one_active_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
  shows "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTransaction S' i = Some tx)
       \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  using steps  packed noFails noCtxtSwitchInTx proof (induct rule: steps_induct)
  case initial
  then show ?case 
    using wellFormed_currentTransaction_unique_h(2) noUncommitted S_wellformed open_transactions_empty by (auto simp add:  allowed_context_switch_simps)

next
  case (step S' tr a S'')

  have IH: "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTransaction S' i = Some tx)
            \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  proof (rule step)
    show "packed_trace tr"
      using packed_trace_prefix step.prems(1) by auto
    show "\<And>s. (s, AFail) \<notin> set tr"
      using step.prems(2) by auto
    show "noContextSwitchesInTransaction tr"
      using isPrefix_appendI prefixes_noContextSwitchesInTransaction step.prems(3) by blast
  qed

  from \<open>S' ~~ a \<leadsto> S''\<close>
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis 
      using IH by (auto simp add: open_transactions_append_one)
  next
    case (newId s ls f ls' uid)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (beginAtomic s ls f ls' t vis snapshot)

    have openTransactions_empty: "openTransactions tr = {}"
    proof (auto simp add: openTransactions_def)
      fix i' tx' j txns
      assume a0: "j < length tr"
        and a1: "\<forall>k<length tr. j < k \<longrightarrow> tr ! k \<noteq> (i', AEndAtomic)"
        and a2: "tr ! j = (i', ABeginAtomic tx' txns)"

      have "\<not> allowed_context_switch (get_action ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>noContextSwitchesInTransaction (tr @ [a])\<close>])
        show "(tr @ [a]) ! j = (i', ABeginAtomic tx' txns)"
          by (simp add: a0 a2 nth_append_first)
        show "\<forall>ja. j < ja \<and> ja < Suc (length tr) \<longrightarrow> (tr @ [a]) ! ja \<noteq> (i', AEndAtomic)"
          by (simp add: a1 local.beginAtomic(1) nth_append)
        show "j < Suc (length tr)"
          by (simp add: a0 less_SucI)
        show " j < length tr"
          by (simp add: a0) 
        show "Suc (length tr) \<le> length (tr @ [a])" 
          by simp
        show "length tr < Suc (length tr)"
          by simp
      qed

      then show "False"
        by (simp add: \<open>a = (s, ABeginAtomic t snapshot)\<close>  allowed_context_switch_simps)
    qed

    from beginAtomic
    show ?thesis using IH 
      by (auto simp add: open_transactions_append_one openTransactions_empty )
  next
    case (endAtomic s ls f ls' t)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (dbop s ls f Op  ls' t c res vis)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (invocation s proc initialState impl)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (return s ls f res)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (fail s ls)
    then show ?thesis
      using step.prems(2) by auto 
  next
    case (invCheck res s)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  qed
qed



lemma at_most_one_current_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    and packed: "packed_trace tr"
    and wf: "state_wellFormed S"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "\<forall>i. currentTransaction S' i \<noteq> None \<longrightarrow> i = get_invoc (last tr)"
  using steps noCtxtSwitchInTx packed  noFails
proof (induct rule: steps_induct)
  case initial
  then have "currentTransaction S i = None" for i
    using noUncommitted
    by (meson local.wf option.exhaust wellFormed_currentTransactionUncommitted) 
  then show ?case
    by simp
next
  case (step S' tr a S'')
  have IH: "\<forall>i. currentTransaction S' i \<noteq> None \<longrightarrow> i = get_invoc (last tr)"
  proof (rule step)
    show " noContextSwitchesInTransaction tr"
      using isPrefix_appendI prefixes_noContextSwitchesInTransaction step.prems(1) by blast
    show "packed_trace tr"
      using packed_trace_prefix step.prems(2) by blast
    show "\<And>s. (s, AFail) \<notin> set tr"
      using step.prems(3) by auto
  qed

  have noFail_tr: "(i, AFail) \<notin> set tr" for i
    using step.prems(3) by auto

  have noFail_a: "get_action a \<noteq> AFail"
    using step.prems(3)
    by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 




  show ?case
  proof (cases tr)
    case Nil
    then have "currentTransaction S' i = None" for i
      using noUncommitted \<open>S ~~ tr \<leadsto>* S'\<close>
      apply (auto simp add: steps_empty)
      by (metis local.wf option.exhaust wellFormed_currentTransaction_unique_h(2))

    with \<open>S' ~~ a \<leadsto> S''\<close>
    show ?thesis 
      by (auto simp add: step.simps split: if_splits)

  next
    case (Cons x xs)
    then have tr_nonempty[simp]: "tr \<noteq> []" by simp

    have last_same: "get_invoc (last tr) = get_invoc a" if "\<not> allowed_context_switch (get_action a)" 
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"] that
      by (auto simp add: nth_append last_conv_nth)

    have no_tx_if_context_switch: "currentTransaction S' i = None" if "allowed_context_switch (get_action a)" for i
    proof (rule ccontr, clarsimp)
      fix tx
      assume tx: "currentTransaction S' i \<triangleq> tx"

      have "currentTransaction S i = None"
        by (meson local.wf noUncommitted option.exhaust wellFormed_currentTransaction_unique_h(2))


      from tx
      obtain ib txns
        where ib: "tr!ib = (i, ABeginAtomic tx txns)"
          and ib_len: "ib < length tr" 
          and ib_no_end: "\<forall>j. ib<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (i, AEndAtomic)"
        using \<open>currentTransaction S i = None\<close> \<open>S ~~ tr \<leadsto>* S'\<close> currentTransaction_exists_beginAtomic local.wf  noFail_tr by blast

      thm step.prems(3)

      have "\<not> allowed_context_switch (get_action ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>noContextSwitchesInTransaction (tr @ [a])\<close>, where j="length tr"])
        show "(tr @ [a]) ! ib = (i, ABeginAtomic tx txns)"
          using ib by (simp add: ib_len nth_append) 
        show "\<forall>j. ib < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (i, AEndAtomic)"
          using that by (auto simp add: ib_no_end nth_append allowed_context_switch_simps)

        show "ib < Suc (length tr)"
          by (simp add: ib_len less_Suc_eq)
          apply_end (auto simp add: ib_len)
      qed
      then show False
        using that by simp
    qed


    from \<open>S' ~~ a \<leadsto> S''\<close>
    show ?thesis
    proof (cases rule: step.cases)
      case (local s ls f ls')
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (newId s ls f ls' uid)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (beginAtomic s ls f ls' t vis snapshot)
      then show ?thesis using IH no_tx_if_context_switch by (auto simp add: allowed_context_switch_simps)
    next
      case (endAtomic s ls f ls' t)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (dbop s ls f Op ls' t c res vis)
      then show ?thesis using IH by auto
    next
      case (invocation s proc  initialState impl)
      then show ?thesis using IH no_tx_if_context_switch by (auto simp add: allowed_context_switch_simps)
    next
      case (return s ls f res)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (fail s ls)
      then show ?thesis using IH
        using step.prems(3) by auto
    next
      case (invCheck res s)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    qed
  qed
qed



lemma chooseSnapshot_transactionConsistent_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and a3: "transactionConsistent (callOrigin S) (transactionStatus S) vis"
  shows "transactionConsistent (callOrigin S) (transactionStatus S) snapshot"
  using a1 a3 apply (auto simp add: chooseSnapshot_def downwardsClosure_def transactionConsistent_def callsInTransactionH_contains)
   apply (auto simp add: split: option.splits)
  apply (auto simp add: transactionConsistent_committed_def)[1]
  using all_committed apply blast
  using all_committed apply blast
  apply (auto simp add: transactionConsistent_atomic_def callsInTransactionH_contains split: option.splits)[1]
  using hb_callOrigin option.distinct(1) apply force
  by (metis (no_types, lifting) hb_tr option.distinct(1) option.sel)
  


lemma chooseSnapshot_consistentSnapshot_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and hb_trans: "trans (happensBefore S)"
    and callOrigin_ex: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> \<exists>ci. calls S c \<triangleq> ci"
    and a3: "consistentSnapshot S vis"
  shows "consistentSnapshot S snapshot"
proof (auto simp add: consistentSnapshotH_def)
  show "causallyConsistent (happensBefore S) snapshot"
    using a1 a3 chooseSnapshot_causallyConsistent_preserve consistentSnapshotH_def hb_trans by blast
  from a1
  show "transactionConsistent (callOrigin S) (transactionStatus S) snapshot"
  proof (rule chooseSnapshot_transactionConsistent_preserve)
    show " \<And>x y z tx. \<lbrakk>(x, z) \<in> happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y, z) \<in> happensBefore S"
      using hb_tr by blast
    show "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
      by (simp add: all_committed)
    show "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb, ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
      using hb_callOrigin by blast
    show "transactionConsistent (callOrigin S) (transactionStatus S) vis"
      using a3 consistentSnapshotH_def by blast
  qed
  show "\<And>x. x \<in> snapshot \<Longrightarrow> \<exists>y. calls S x \<triangleq> y"
    using a1 apply (auto simp add: chooseSnapshot_def)
    apply (meson a3 consistentSnapshotH_def in_dom)
    by (smt assms(6) callsInTransactionH_def downwardsClosure_in hb_callOrigin mem_Collect_eq)
qed









lemma wf_transactionConsistent_noTx:
  assumes wf: "state_wellFormed S"
and "visibleCalls S i \<triangleq> vis"
and "currentTransaction S i = None"
shows "transactionConsistent (callOrigin S) (transactionStatus S) vis"
proof (rule show_transactionConsistent)
  show "transactionStatus S tx \<triangleq> Committed" if "c \<in> vis" and "callOrigin S c \<triangleq> tx" for c tx
    using assms(2) assms(3) local.wf that(1) that(2) wellFormed_state_transaction_consistent(1) by fastforce

  show "\<And>c1 c2. \<lbrakk>c1 \<in> vis; callOrigin S c1 = callOrigin S c2\<rbrakk> \<Longrightarrow> c2 \<in> vis"
    using assms(2) local.wf wellFormed_state_transaction_consistent(2) by blast

qed

end