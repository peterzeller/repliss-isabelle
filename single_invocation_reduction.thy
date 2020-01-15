section \<open>Single Invocation Reduction\<close>
theory single_invocation_reduction
  imports commutativity
    repliss_sem_single_invocation
    consistency
    packed_nofails_noinvchecks
    single_invocation_reduction_helper
    state_monotonicGrowth_invariants
begin


text \<open>This theory includes the main soundness proof of our proof approach.
We reduce the verification problem from the interleaving semantics to the single invocation semantics.\<close>



text \<open>Coupling invariant: S is state from distributed execution and S is state from single-invocId execution.\<close>
definition state_coupling :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> invocId \<Rightarrow> bool \<Rightarrow> bool" where
  "state_coupling S S' i sameInvoc \<equiv> 
   if sameInvoc then
      \<comment> \<open>  did a step in the same invocId  \<close>
      S' = S
   else 
      \<comment> \<open>  did step in a different invocId  \<close>
        state_monotonicGrowth i S' S
      "

lemma state_coupling_refl: 
  assumes "state_wellFormed S"
  shows "state_coupling S S i s"
  by (auto simp add: state_coupling_def  state_monotonicGrowth_def assms steps_empty intro: exI[where x="[]"])



lemma state_coupling_same_inv:
  assumes "state_coupling S S' s True"
  shows "invariant_all S' \<longleftrightarrow> invariant_all S"
proof -
  have [simp]: "prog S' = prog S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "callOrigin S' = callOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "transactionOrigin S' = transactionOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "transactionStatus S' = transactionStatus S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "happensBefore S' = happensBefore S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "calls S' = calls S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "knownIds S' = knownIds S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationOp S' = invocationOp S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationRes S' = invocationRes S" using assms by (auto simp add: state_coupling_def split: if_splits)

  ultimately 
  show "invariant_all S' \<longleftrightarrow> invariant_all S"
    by  (auto simp add:  consistentSnapshotH_def)
qed    


lemma state_monotonicGrowth_refl2:
  shows "state_wellFormed S \<and> S = S' \<Longrightarrow> state_monotonicGrowth i S S'"
  using state_monotonicGrowth_refl by blast

lemma no_current_transactions:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noChrash: "\<And>i. (i, ACrash) \<notin> set tr"
    and noUncommitted: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noContextSwitch: "noContextSwitchesInTransaction tr"
    and ls_None: "localState S' i = None"
    and i_is_last: "tr = [] \<or> get_invoc (last tr) = i"
  shows "currentTransaction S' i' = None"
proof -

  have S'_wf: "state_wellFormed S'"
    using S_wf noChrash state_wellFormed_combine steps by blast


  have vis_None: "visibleCalls S' i = None"
    using S'_wf ls_None state_wellFormed_ls_visibleCalls by blast


  have at_most_one_tx: "(\<forall>i tx. ((i, tx) \<in> openTransactions tr) = currentTransaction S' i \<triangleq> tx) \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  proof (rule at_most_one_active_tx[OF \<open> S ~~ tr \<leadsto>* S'\<close>])
    show "state_wellFormed S"
      using S_wf by auto
    show "packed_trace tr"
      by (simp add: packed)
    show " \<And>s. (s, ACrash) \<notin> set tr"
      using noChrash by auto
    show  " \<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      using noUncommitted by blast
    show  "noContextSwitchesInTransaction tr"
      by (simp add: noContextSwitch)
  qed


  have noCurrentTransactionI: "currentTransaction S' i = None"
    by (meson S'_wf option.exhaust_sel state_wellFormed_tx_to_visibleCalls vis_None)


  show noCurrentTransaction: "currentTransaction S' i' = None" 
    using at_most_one_current_tx[OF \<open>S ~~ tr \<leadsto>* S'\<close> \<open>noContextSwitchesInTransaction tr\<close> \<open>packed_trace tr\<close> \<open>state_wellFormed S\<close> \<open>\<And>s. (s, ACrash) \<notin> set tr\<close> noUncommitted]
    using i_is_last noCurrentTransactionI
    by (metis S'_wf noUncommitted option.exhaust steps steps_empty wellFormed_currentTransaction_unique_h(2)) 


qed

text \<open>
If we have an execution on a a single invocId starting with state satisfying the invariant, then we can convert 
this trace to a single-invocId trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
\<close>
lemma convert_to_single_session_trace:
  fixes tr :: "('proc::valueType, 'operation, 'any::valueType) trace"
    and i :: invocId      
    and S S' :: "('proc, 'ls, 'operation, 'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds on all states in the execution\<close>
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  shows "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 i (tr = [] \<or> get_invoc (last tr) = i))"
  using steps S_wellformed packed inv noFails noUncommitted noCtxtSwitchInTx proof (induct rule: steps.induct)
  case (steps_refl S)

  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="S"], intro conjI; simp?)
    show "S ~~ (i, []) \<leadsto>\<^sub>S* S"
      by (simp add: steps_s_refl) 
    show "state_coupling S S i True"
      unfolding state_coupling_def 
      by auto
  qed
next
  case (steps_step S tr S' a S'')
  then have  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; packed_trace tr; 
               \<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) 
                   \<and> (\<forall>a. (a, False) \<notin> set tr') 
                   \<and> (state_coupling S' S2 i (tr = [] \<or> get_invoc (last tr) = i))"
    and  step: "S' ~~ a \<leadsto> S''"
    and  packed: "packed_trace (tr @ [a])"
    and prefix_invariant: "\<And>tr' S'.  \<lbrakk>isPrefix tr' (tr @ [a]); S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
    and noFails: "\<And>s. (s, ACrash) \<notin> set (tr @ [a])"
    and noContextSwitch: "noContextSwitchesInTransaction (tr @ [a])"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by (auto, blast)

  have noFails_tr: "\<And>i. (i, ACrash) \<notin> set tr"
    using steps_step.prems(4) by auto

  have steps': "S ~~ tr @ [a] \<leadsto>* S''"
    using steps step steps.steps_step by blast 

  from prefix_invariant steps
  have inv': "invariant_all S'"
    using isPrefix_appendI by blast


  from prefix_invariant steps'
  have inv'': "invariant_all S''"
    by (metis append.right_neutral isPrefix_appendI)

  have "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) 
         \<and> (\<forall>a. (a, False) \<notin> set tr') 
         \<and> (state_coupling S' S2 i (tr = [] \<or> get_invoc (last tr) = i))"
  proof (rule IH)
    have "isPrefix tr (tr@[a])"
      by (simp add: isPrefix_appendI)
    then show "packed_trace tr"
      using packed prefixes_are_packed by blast 
    show "\<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using prefix_invariant isPrefix_append by blast 
    show "state_wellFormed S" using S_wf .
  qed

  from this obtain tr' S2
    where ih1: "S ~~ (i, tr') \<leadsto>\<^sub>S* S2"
      and ih2: "\<And>a. (a, False) \<notin> set tr'"
      and ih3': "state_coupling S' S2 i  (tr = [] \<or> get_invoc (last tr) = i)"
    by blast

  show  "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 i (tr @ [a] = [] \<or> get_invoc (last (tr @ [a])) = i)"  
  proof (cases "get_invoc a = i"; simp)
    case False
    then have different_session[simp]:  "get_invoc a \<noteq> i" by simp

    text \<open>we are now in the case of doing steps in a different session.
   We show that all of these preserve the coupling. 
\<close>

    have "state_wellFormed S'"
      using S_wf noFails_tr state_wellFormed_combine steps by auto

    have wf_S2: "state_wellFormed S2"
      by (metis \<open>state_wellFormed S'\<close> ih3' state_coupling_def state_monotonicGrowth_wf1)


    text \<open>no matter what he had before, the coupling with "False" will hold:\<close>
    have old_coupling: "state_coupling S' S2 i False"
      using ih3' by (auto simp add: \<open>state_wellFormed S'\<close> state_coupling_def state_monotonicGrowth_refl  split: if_splits)




    from step
    have new_coupling: "state_coupling S'' S2 i False"
      by (metis append_is_Nil_conv different_session last_in_set last_snoc noFails not_Cons_self2 
          old_coupling state_coupling_def state_monotonicGrowth_step surjective_pairing wf_S2)


    then show "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 i False"
      using ih1 ih2 by blast
  next


    case True \<comment> \<open>the new action is on invocId i\<close>
    then have [simp]: "get_invoc a = i" .

    show "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 i True"  (is ?goal) 
    proof (cases "allowed_context_switch (get_action a)")
      case True
      hence acs: "allowed_context_switch (get_action a)" .



      have ih3: "state_coupling S' S2 i False" using ih3'
        by (metis S_wf noFails_tr state_coupling_def state_coupling_refl state_wellFormed_combine steps) 

      from ih3  
      have growth: "state_monotonicGrowth i S2 S'" 
        by (auto simp add: state_coupling_def)


      from this 
      have  ls_same: "localState S2 i = localState S' i" 
        and proc_same: "currentProc S2 i = currentProc S' i" 
        and tx_same: "currentTransaction S2 i = currentTransaction S' i" 
        and visible_same: "visibleCalls S2 i = visibleCalls S' i"
        by (auto simp add:  state_monotonicGrowth_localState state_monotonicGrowth_currentProc state_monotonicGrowth_currentTransaction state_monotonicGrowth_visibleCalls)




      from acs show ?goal
      proof (cases rule: allowed_context_switch_cases)
        case (invoc p)


        with step
        have step': "S' ~~ (i, AInvoc p) \<leadsto> S''"
          by (metis \<open>get_invoc a = i\<close> prod.collapse)

        from step_elim_AInvoc[OF step']  
        obtain initial impl 
          where a1: "S'' = S'\<lparr>
                    localState := localState S'(i \<mapsto> initial), 
                    currentProc := currentProc S'(i \<mapsto> impl), 
                    visibleCalls := visibleCalls S'(i \<mapsto> {}), 
                    invocationOp := invocationOp S'(i \<mapsto> p)\<rparr>"
            and a2: "localState S' i = None"
            and a3: "procedure (prog S') p = (initial, impl)"
            and a4: "uniqueIds p \<subseteq> knownIds S'"
            and a5: "invocationOp S' i = None"
          by metis

        show "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 i True"
        proof (intro exI conjI)
          have "S2 ~~ (i, AInvoc p, True) \<leadsto>\<^sub>S S''"
          proof (rule step_s.intros)
            have "\<And>p. invocationOp S2 i \<noteq> Some p"
              using a5 ih3' by (metis option.distinct(1) state_coupling_def state_monotonicGrowth_invocationOp)
            then show "invocationOp S2 i = None" by blast
            have [simp]: "prog S2 = prog S'"
              by (metis ih3' state_coupling_def state_monotonicGrowth_prog)
            show "procedure (prog S2) p = (initial, impl)"
              using a3 state_coupling_def by auto
            show "uniqueIds p \<subseteq> knownIds S'"
              using a4 ih3' state_coupling_def by auto
            show "invariant_all S'"
              by (simp add: inv')
            show "invocationOp S' i = None" using a5  .
            show "S'' = S'\<lparr>localState := localState S'(i \<mapsto> initial), currentProc := currentProc S'(i \<mapsto> impl), visibleCalls := visibleCalls S'(i \<mapsto> {}), invocationOp := invocationOp S'(i \<mapsto> p)\<rparr>"
              using a1 by auto
            show "True = invariant_all S''"
              by (simp add: inv'')
            show "prog S' = prog S2"
              by simp
            show "state_wellFormed S'"
              using S_wf state_wellFormed_combine steps noFails by auto

            have "currentTransaction S' i = None"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wellFormed_invoc_notStarted(1))

            have "\<And>s. (s, ACrash) \<notin> set tr"
              using steps_step.prems(4) by auto


            have "currentTransaction S' s = None" for s
              by (metis S_wf \<open>get_invoc a = i\<close> \<open>state_wellFormed S'\<close> a5 at_most_one_current_tx last_snoc noContextSwitch noFails packed step' steps' steps_step.prems(5) unchangedInTransaction(3) wellFormed_invoc_notStarted(1))

            from this
            show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
              using wellFormed_currentTransaction_back[OF steps \<open>\<And>s. (s, ACrash) \<notin> set tr\<close> \<open>\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted\<close> \<open>state_wellFormed S\<close>]
              by auto


            have "\<And>tx. transactionOrigin S' tx \<noteq> Some i"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wf_no_invocation_no_origin)

            then show "\<And>tx. transactionOrigin S'' tx \<noteq> Some i"
              using step' by (auto simp add: step_simps)
          qed
          then show "S ~~ (i, tr'@[(AInvoc p, True)]) \<leadsto>\<^sub>S* S''"
            using ih1 steps_s_step by blast
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(AInvoc p, True)])"
            using ih2 by auto
          show "state_coupling S'' S'' i True"
            by (auto simp add: state_coupling_def)
        qed

      next
        case (beginAtomic tx snapshot)


        with step
        have step': "S' ~~ (i, ABeginAtomic tx snapshot) \<leadsto> S''"
          by (metis \<open>get_invoc a = i\<close> surjective_pairing)


        from step_elim_ABeginAtomic[OF step']  
        obtain ls f ls' vis
          where a1: "S'' = S'\<lparr>
                    localState := localState S'(i \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(i \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted),
                    transactionOrigin := transactionOrigin S'(tx \<mapsto> i), 
                    visibleCalls := visibleCalls S'(i \<mapsto> snapshot)\<rparr>"
            and a2: "localState S' i \<triangleq> ls"
            and a3: "currentProc S' i \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' i = None"
            and a6: "transactionStatus S' tx = None"
            and a7: "visibleCalls S' i \<triangleq> vis"
            and a9: "chooseSnapshot snapshot vis S'"
          by smt


        show ?thesis
        proof (intro exI conjI)
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic tx snapshot, True)])"
            using ih2 by auto

          show "state_coupling S'' S'' i True"
            by (auto simp add: state_coupling_def)

          have "S2 ~~ (i, ABeginAtomic tx snapshot, True) \<leadsto>\<^sub>S S''"
          proof (rule step_s.beginAtomic)
            show "localState S2 i \<triangleq> ls"
              by (simp add: a2 ls_same)
            show "currentProc S2 i \<triangleq> f"
              by (simp add: a3 proc_same)  
            show "f ls = BeginAtomic ls'" using a4 .
            show "currentTransaction S2 i = None"
              using a5 tx_same by auto
            show "transactionStatus S2 tx = None"
            proof -
              from ih3 have "transactionStatus S2 tx \<le> transactionStatus S' tx"
                by (auto simp add: state_coupling_def state_monotonicGrowth_transactionStatus)
              with a6
              show ?thesis
                by (simp add: less_eq_option_None_is_None)
            qed
            show "prog S' = prog S2"
              using ih3  prog_inv[OF local.step]
              by (auto simp add: state_coupling_def state_monotonicGrowth_prog)
            show "invariant_all S'"
              using inv' by blast
            show "localState S' i \<triangleq> ls"
              using a2 by auto
            show "currentTransaction S' i = None"
              by (simp add: a5)
            show "transactionStatus S' tx = None"
              by (simp add: a6)
            show "transactionOrigin S' tx = None"
              using S_wf a6 noFails_tr state_wellFormed_combine steps wf_transaction_status_iff_origin by blast

            show "state_wellFormed S''"
              using S_wf state_wellFormed_combine steps' noFails by blast
            show "state_monotonicGrowth i S2 S'"
              using ih3 by (auto simp add: state_coupling_def)
            show "currentProc S' i \<triangleq> f"
              by (simp add: a1 a3)

            have "state_wellFormed S2"
              using growth state_monotonicGrowth_wf1 by blast 
            have "state_wellFormed S'"
              using growth state_monotonicGrowth_wf2 by auto


            show "\<And>c. callOrigin S' c \<noteq> Some tx"
              using `transactionStatus S' tx = None`
                and wf_no_transactionStatus_origin_for_nothing[OF \<open>state_wellFormed S'\<close>] by simp


            have "\<forall>i. currentTransaction S'' i \<noteq> None \<longrightarrow> i = get_invoc (last (tr@[a]))"
            proof (rule at_most_one_current_tx)
              show "S ~~ tr @ [a] \<leadsto>* S''"
                using steps' by auto

              show " noContextSwitchesInTransaction (tr@[a])"
                using  noContextSwitch  by blast
              show "packed_trace (tr@[a])"
                using packed by blast
              show "state_wellFormed S"
                by (simp add: S_wf)
              show "\<And>s. (s, ACrash) \<notin> set (tr@[a])"
                using noFails by blast
              show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
                by (simp add: steps_step.prems(5))
            qed
            then have noCurrentTransaction: "currentTransaction S'' i' = None" if "i'\<noteq>i" for i'
              using that by auto
            have "\<And>tx'. tx' \<noteq> tx \<Longrightarrow> transactionStatus S'' tx' \<noteq> Some Uncommitted"
            proof (rule wellFormed_currentTransaction_back4[OF \<open>state_wellFormed S''\<close>])
              fix tx' i'
              assume a: "tx' \<noteq> tx"

              show "currentTransaction S'' i' \<noteq> Some tx'"
              proof (cases "i'=i")
                case True
                then show ?thesis 
                  using a by (simp add: a1)
              next
                case False
                then show ?thesis
                  by (simp add: noCurrentTransaction)
              qed
            qed


            then show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
              apply (simp add: a1)
              using a6 by force

            show "S'' = S'\<lparr>transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(tx \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> tx),
               localState := localState S'(i \<mapsto> ls'), visibleCalls := visibleCalls S'(i \<mapsto> snapshot)\<rparr>"
              by (auto simp add: a1 state_ext)

            show "chooseSnapshot snapshot vis S'" using a9 .



            show "state_wellFormed S'"
              using S_wf noFails_tr state_wellFormed_combine steps by auto



            show "visibleCalls S' i \<triangleq> vis"
              using a7 by auto


            from \<open>visibleCalls S' i \<triangleq> vis\<close>
            show "visibleCalls S2 i \<triangleq> vis"
              using visible_same by auto


            show " \<And>t. transactionOrigin S2 t \<triangleq> i = transactionOrigin S' t \<triangleq> i"
              using growth state_monotonicGrowth_transactionOrigin_i by blast

            have wf_S': "state_wellFormed S'"
              using S_wf noFails_tr state_wellFormed_combine steps by auto

            have "consistentSnapshot S'' snapshot"
              using \<open>state_wellFormed S''\<close>
            proof (rule wellFormed_state_consistent_snapshot)
              show "visibleCalls S'' i \<triangleq> snapshot"
                by (auto simp add: a1)
              show "\<And>c tx. currentTransaction S'' i \<triangleq> tx \<Longrightarrow> callOrigin S'' c \<noteq> Some tx"
                using \<open>\<And>c. callOrigin S' c \<noteq> Some tx\<close> by (auto simp add: a1)
            qed

            from this
            show "consistentSnapshot S' snapshot"
              by (auto simp add: a1 consistentSnapshotH_def transactionConsistent_def transactionConsistent_committed_def split: if_splits)
          qed

          then show "S ~~ (i, tr'@[(ABeginAtomic tx snapshot, True)]) \<leadsto>\<^sub>S*  S''"
            using ih1 steps_s_step by blast
        qed
      qed

    next 
      case False
      hence noacs: "\<not>allowed_context_switch (get_action a)" .

      have [simp]:"tr = [] \<or> get_invoc (last tr) = i"
      proof (rule ccontr, auto)
        assume "tr \<noteq> []" and "get_invoc (last tr) \<noteq> i"

        from packed
        have "allowed_context_switch (get_action ((tr@[a]) ! length tr))"
        proof (rule use_packed_trace)
          show "0 < length tr" using `tr \<noteq> []` by auto
          show "length tr < length (tr @ [a])" by auto
          show "get_invoc ((tr @ [a]) ! (length tr - 1)) \<noteq> get_invoc ((tr @ [a]) ! length tr)"
            using `get_invoc (last tr) \<noteq> i` by (simp add: \<open>tr \<noteq> []\<close> last_conv_nth nth_append)
        qed
        thus False
          by (simp add: noacs)
      qed

      then have ih3: "state_coupling S' S2 i True"
        using ih3' by simp

      have ih3_tx: "S2 = S'"
        using ih3' state_coupling_def by force


      have S2_calls: "calls S2 = calls S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_happensBefore: "happensBefore S2 = happensBefore S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_prog: "prog S2 = prog S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_localState: "localState S2 = localState S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_currentProc: "currentProc S2 = currentProc S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_currentTransaction: "currentTransaction S2 = currentTransaction S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_transactionStatus: "transactionStatus S2 = transactionStatus S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_callOrigin: "callOrigin S2 = callOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_transactionOrigin: "transactionOrigin S2 = transactionOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_generatedIds: "generatedIds S2 = generatedIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_knownIds: "knownIds S2 = knownIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocationOp: "invocationOp S2 = invocationOp S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocationRes: "invocationRes S2 = invocationRes S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)

      note S2_simps = 
        S2_calls S2_happensBefore S2_prog S2_localState S2_currentProc S2_currentTransaction
        S2_transactionStatus S2_callOrigin S2_transactionOrigin S2_generatedIds S2_knownIds S2_invocationOp S2_invocationRes


      have S'_wf: "state_wellFormed S'"
        using S_wf steps noFails_tr by (rule state_wellFormed_combine)


      have vis_defined: "visibleCalls S' i \<noteq> None" if "currentTransaction S' i \<noteq> None"
        using S'_wf state_wellFormed_tx_to_visibleCalls that by auto

      have tr_noSwitch: "noContextSwitchesInTransaction tr"
        using isPrefix_appendI noContextSwitch prefixes_noContextSwitchesInTransaction by blast

      have tr_packed: "packed_trace tr"
        using packed packed_trace_prefix by blast

      have tr_noFail: "\<And>s. (s, ACrash) \<notin> set tr"
        using steps_step.prems(4) by auto


      obtain action where a_def: "a = (i, action)"
        using \<open>get_invoc a = i\<close> surjective_pairing by blast



      from ` S' ~~ a \<leadsto> S''`
      have "S' ~~ (i,get_action a) \<leadsto> S''"
        by (simp add: a_def)

      have inv_S': "invariant_all S'"
        using isPrefix_appendI step_prog_invariant steps steps_step.prems(3) by fastforce  

      have inv_S'': "invariant_all S''"
        by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps_appendBack)

      have wf_S'': "state_wellFormed S''"
        using S_wf noFails state_wellFormed_combine steps' by blast




      show ?thesis 
      proof (cases "\<exists>ir. get_action a = AInvcheck ir ")
        case True
        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (i, tr') \<leadsto>\<^sub>S* S'"
            using ih1 ih3_tx by blast
          show "\<forall>a. (a, False) \<notin> set tr'"
            by (simp add: ih2)
          show "state_coupling S'' S' i True"
            using True \<open>S' ~~ (i, get_action a) \<leadsto> S''\<close> state_coupling_def step_elim_AInvcheck by fastforce
        qed


      next
        case False
        hence "get_action a \<noteq> AInvcheck ir" for ir
          by auto
        show ?thesis 
        proof (intro exI conjI)
          show " state_coupling S'' S'' i True "
            by (simp add: state_coupling_def)

          show " \<forall>x. (x, False) \<notin> set (tr' @ [(get_action a, True)])"
            by (simp add: ih2)

          have "S' ~~ (i,get_action a, True) \<leadsto>\<^sub>S S''"
          proof (cases "get_action a")
            case ALocal
            then have [simp]: "a = (i, ALocal)"
              by (simp add: prod.expand) 


            show ?thesis
              using step unfolding step.simps step_s.simps by auto
          next
            case (ANewId uid)
            then have [simp]: "a = (i, ANewId uid)"
              by (simp add: prod_eqI steps_step.prems) 
            show ?thesis
              using step unfolding step.simps step_s.simps by auto

          next
            case AEndAtomic
            then have [simp]: "a = (i, AEndAtomic)"
              by (simp add: local.steps_step(5) prod_eqI)

            show ?thesis
              using step inv_S'' wf_S'' unfolding step.simps step_s.simps by auto

          next
            case (ADbOp cId operation res)
            then have [simp]: "a = (i, ADbOp cId operation res)"
              by (simp add: prod.expand steps_step.prems(2)) 

            show ?thesis
              using step by (auto simp add: step.simps step_s.simps)

          next
            case (AInvoc proc)
            thus ?thesis
              using allowed_context_switch_simps noacs by fastforce

          next
            case (AReturn res)
            then have [simp]: "a = (i, AReturn res)"
              by (simp add: prod_eqI steps_step.prems(2))

            show ?thesis
              using step inv_S'' by (auto simp add: step.simps step_s.simps)


          next
            case ACrash
            then have "a = (i, ACrash)"
              by (simp add: prod_eqI steps_step.prems(2))
            with \<open>\<And>i. (i, ACrash) \<notin> set (tr @ [a])\<close>  have "False"
              by auto
            then show ?thesis ..
          next
            case (AInvcheck res)
            thus ?thesis
              using ` \<nexists>ir. get_action a = AInvcheck ir` by blast
          next
            case (ABeginAtomic txId snapshot)
            thus ?thesis
              using allowed_context_switch_simps(3) noacs by auto
          qed
          thus "S ~~ (i, tr' @ [(get_action a, True)]) \<leadsto>\<^sub>S* S''"
            using ih1 ih3_tx steps_s_step by blast
        qed
      qed
    qed
  qed
qed


lemma convert_to_single_session_trace_invFail_step:
  fixes tr :: "('proc::valueType, 'operation, 'any::valueType) trace"
    and s :: invocId      
    and S S' :: "('proc, 'ls, 'operation, 'any) state"
  assumes step: "S ~~ (s,a) \<leadsto> S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "a \<noteq> ACrash"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not>invariant_all S'"
    and coupling: "state_coupling S S2 s sameSession"
    and ctxtSwitchCases: "\<not>sameSession \<Longrightarrow> allowed_context_switch a" 
    and noUncommitted:  "a \<noteq> AEndAtomic \<Longrightarrow>  \<forall>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    \<comment> \<open>we assume that we are not in a transaction (inside a transaction it is not necessary for invariants to hold)\<close>
  shows "\<exists>tr' S2'. (S2 ~~ (s, tr') \<leadsto>\<^sub>S* S2') 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
  using step proof (cases rule: step.cases)
  case (local ls f ls')
  text \<open>a local step does not change the invariant\<close>

  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S'  = invContext S "
      using local by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed

  with inv and not_inv
  have False by simp

  then show ?thesis ..
next
  case (newId ls f ls' uid)
  text \<open>generating a new id does not change the invariant\<close>

  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S' = invContext S"
      using newId by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed

  with inv and not_inv
  have False by simp

  then show ?thesis ..
next
  case (beginAtomic ls f ls' t)
  text \<open>starting a transaction does not change the invariant\<close>

  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S' = invContext S " 
      using beginAtomic by (auto simp add: invContextH_def restrict_map_def   committedCallsH_update_uncommitted )

    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed

  with inv and not_inv
  have False by simp

  then show ?thesis ..
next
  case (endAtomic ls f ls' t)
  text \<open>Ending a transaction includes an invariant-check in the single-invocId semantics, so we get a failing trace.\<close>

  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Committed)\<rparr>"

  have [simp]: "sameSession"
    using allowed_context_switch_def[where action=a] ctxtSwitchCases local.endAtomic(1) by blast

  have "S2 ~~ (s,(AEndAtomic, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls" 
      and "currentProc S2 s \<triangleq> f"  
      and "f ls = EndAtomic ls'"
      and "currentTransaction S2 s \<triangleq> t"
      using coupling local.endAtomic state_coupling_def by force+
    show "S2' 
        = S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Committed)\<rparr>"
      using S2'_def by simp

    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add:  state_coupling_def local.endAtomic(6) split: if_splits)
      show "False" if "\<not> invariant_all S'" and "S2 = S" and "invariant_all S2'"
        using that apply (auto simp add: S2'_def \<open>S2 = S\<close>)
        using S2'_def local.endAtomic(2) that(2) that(3) by blast
    qed
    show "state_wellFormed S2'"
      by (metis (full_types) S2'_def S_wellformed \<open>sameSession\<close> action.distinct(49) coupling local.endAtomic(1) local.endAtomic(2) local.step snd_conv state_coupling_def state_wellFormed_combine_step)

  qed

  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (dbop ls f Op ls' t c res vis)
  text \<open>uncommitted operations do not affect the invariant\<close>

  have hb': "happensBefore S' = happensBefore S \<union> vis \<times> {c}"
    using dbop by auto



  have "invariant_all S'" if "invariant_all S"
    using S_wellformed local.dbop(1) local.dbop(6) noUncommitted wellFormed_currentTransactionUncommitted by blast

  then have False
    by (simp add: inv not_inv)
  then show ?thesis ..
next
  case (invocation proc initialState impl)
  text \<open>invocations include an invariant-check\<close>

  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> initialState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> proc)\<rparr>"

  have "S2 ~~ (s,(AInvoc proc, False)) \<leadsto>\<^sub>S S'"
  proof (rule step_s.intros)

    have "localState S2 s = None"
      using invocation coupling
      by (metis state_coupling_def state_monotonicGrowth_localState)
    have "\<And>x. invocationOp S2 s \<noteq> Some x"      
      using invocation coupling by (auto simp add: state_coupling_def state_monotonicGrowth_invocationOp split: if_splits)
    then show "invocationOp S2 s = None" by blast     
    show "procedure (prog S2) proc = (initialState, impl)"
      using invocation coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "uniqueIds proc \<subseteq> knownIds S"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invocationOp S s = None"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invariant_all S"
      by (simp add: inv)
    show "S' = S\<lparr>localState := localState S(s \<mapsto> initialState), currentProc := currentProc S(s \<mapsto> impl), visibleCalls := visibleCalls S(s \<mapsto> {}), invocationOp := invocationOp S(s \<mapsto> proc)\<rparr>"
      using local.invocation(2) by linarith
    show "False = invariant_all S'"
      by (simp add: not_inv)
    show "prog S = prog S2" 
      using coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "state_wellFormed S"
      by (simp add: S_wellformed)
    show " \<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      by (simp add: local.invocation(1) noUncommitted)

    have "\<And>tx. transactionOrigin S tx \<noteq> Some s"
      by (simp add: S_wellformed local.invocation(6) wf_no_invocation_no_origin)
    then show "\<And>tx. transactionOrigin S' tx \<noteq> Some s"
      using step \<open>a = AInvoc proc\<close> by (auto simp add: step_simps)

  qed    

  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (return ls f res)
  text \<open>return contains an invariant check\<close>

  define S2' where "S2' \<equiv> S2\<lparr>localState := (localState S2)(s := None), 
                              currentProc := (currentProc S2)(s := None), 
                              visibleCalls := (visibleCalls S2)(s := None), 
                              invocationRes := invocationRes S2(s \<mapsto> res), 
                              knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"

  have [simp]: sameSession
    using ctxtSwitchCases local.return(1) allowed_context_switch_def[where action = a] by blast                            

  have "S2 ~~ (s,(AReturn res, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls"
      and "currentProc S2 s \<triangleq> f"
      and "f ls = Return res"
      and "currentTransaction S2 s = None"
      using return coupling by (auto simp add: state_coupling_def)

    show "S2' = S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S2(s \<mapsto> res), knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"
      using S2'_def by simp

    have not_in_transaction: "currentTransaction S s = None"
      using S_wellformed return wellFormed_invoc_notStarted(1) by auto  

    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add:  state_coupling_def not_in_transaction)
      fix vis
      assume a3: "S2 = S"
        and a0: "invariant_all S2'"
        and a1: "\<not> invariant_all S'"

      show False
        using S2'_def a0 a3 local.return(2) not_inv by blast
    qed
  qed

  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (fail ls)
  text \<open>we assumed that there are no fails\<close>
  then show ?thesis
    using noFails by blast
next
  case (invCheck  res)
  then show ?thesis
    using inv not_inv by blast \<comment> \<open>same state\<close>
qed

lemma uncommitted_tx_is_current_somewhere:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and tx_uncommitted: "transactionStatus S' tx \<triangleq> Uncommitted"
  shows "\<exists>invoc. currentTransaction S' invoc \<triangleq> tx" 
  using steps noFails tx_uncommitted proof (induct rule: steps_induct)
  case initial
  then show ?case
    using noUncommittedTx by blast 
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: step.simps split: if_splits, force+)
qed

lemma no_current_transaction_when_invariant_fails:
  assumes "S ~~ a \<leadsto> S_fail"
    and "\<not> invariant_all S_fail"
    and "state_wellFormed S"
    and " invariant_all S"
    and wf: "state_wellFormed S"
    and noEndAtomic: "get_action a \<noteq> AEndAtomic"
  shows "currentTransaction S (get_invoc a) = None"
proof (rule ccontr)
  assume " currentTransaction S (get_invoc a) \<noteq> None"
  from this obtain tx where ctx: "currentTransaction S (get_invoc a) \<triangleq> tx"
    by (metis not_None_eq)

  have uncommitted: "transactionStatus S tx \<triangleq> Uncommitted"
    by (metis ctx local.wf wellFormed_currentTransactionUncommitted)



  have committedCallsH_same: "committedCallsH (callOrigin S_fail) (transactionStatus S_fail) = committedCallsH (callOrigin S) (transactionStatus S)"
    using \<open>S ~~ a \<leadsto> S_fail\<close>
    using \<open>currentTransaction S (get_invoc a) \<noteq> None\<close> noEndAtomic apply (auto simp add: step.simps committedCallsH_def )
     apply (auto simp add: isCommittedH_def split: if_splits)
    using wellFormed_currentTransactionUncommitted[OF wf] apply auto
    by (metis local.wf option.distinct(1) wellFormed_callOrigin_dom2)


  have committedCallsExist: "calls S c = None \<Longrightarrow> c \<notin> committedCalls S" for c
    by (metis local.wf wellFormed_committedCallsExist)


  have "invContext S_fail = invContext S" 
    apply (auto simp add: invContextH_def committedCallsH_same)
    using \<open>S ~~ a \<leadsto> S_fail\<close> noEndAtomic \<open>currentTransaction S (get_invoc a) \<noteq> None\<close>
    by (auto simp add: step.simps restrict_map_def restrict_relation_def committedCallsExist inTransaction_localState[OF wf])

  with   \<open>\<not> invariant_all S_fail\<close> \<open>invariant_all S\<close>
  show False
    by (metis (no_types, lifting)  prog_inv[OF \<open>S ~~ a \<leadsto> S_fail\<close>] )
qed


lemma convert_to_single_session_trace_invFail:
  fixes tr :: "('proc::valueType, 'operation, 'any::valueType) trace"
    and S S' :: "('proc, 'ls, 'operation, 'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noContextSwitches: "noContextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not> invariant_all S'"
  shows "\<exists>tr' S2 s. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
proof -

  have not_inv_ex: "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"
    by (rule exI[where x="tr"], rule exI[where x="S'"], auto  simp add: not_inv steps isPrefix_refl)



  text \<open>There must be a place where the invariant fails for the first time:\<close>
  obtain tr1 a tr2 S1 S_fail
    where tr_split: "tr = tr1@a#tr2"
      and steps1: "S ~~ tr1 \<leadsto>* S1"
      and stepA: "S1 ~~ a \<leadsto> S_fail"
      and first_not_inv: "\<not>invariant_all S_fail"
      and inv_before: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr1; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  proof (atomize_elim)  
    show "\<exists>tr1 a tr2 S1 S_fail. tr = tr1 @ a # tr2 \<and> (S ~~ tr1 \<leadsto>* S1) \<and> (S1 ~~ a \<leadsto> S_fail) \<and> \<not> invariant_all S_fail \<and> (\<forall>S' tr'. isPrefix tr' tr1 \<longrightarrow> (S ~~ tr' \<leadsto>* S') \<longrightarrow> invariant_all S')"
      using steps inv not_inv_ex proof (induct rule: steps_induct)
      case initial
      then show ?case
        by (simp add: isPrefix_empty steps_empty)
    next
      case (step S' tr a S'')
      then show ?case 
      proof (cases "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail")
        case True
        then show ?thesis
          using inv step.IH by force 
      next
        case False

        then have invariant_in_tr: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
          by blast

        from \<open>\<exists>tr_pre S_fail. isPrefix tr_pre (tr @ [a]) \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail\<close>
        obtain tr_pre S_fail 
          where "isPrefix tr_pre (tr @ [a])" 
            and "S ~~ tr_pre \<leadsto>* S_fail" 
            and "\<not> invariant_all S_fail"
          by blast

        have "tr_pre = tr @ [a]"
        proof (rule ccontr)
          assume "tr_pre \<noteq> tr @ [a]"
          with \<open>isPrefix tr_pre (tr @ [a])\<close>
          have "isPrefix tr_pre tr"
            by (metis (no_types, lifting) append_eq_append_conv_if append_take_drop_id isPrefix_def length_append_singleton not_less_eq_eq take_all)

          with invariant_in_tr
          have "invariant_all S_fail"
            using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> by blast
          with \<open>\<not> invariant_all S_fail\<close>
          show False ..
        qed

        then have "S_fail = S''"
          using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> step.step step.steps steps_step traceDeterministic by blast

        with \<open>\<not> invariant_all S_fail\<close>
        have "\<not>invariant_all S''"
          by auto


        show ?thesis 
          using step invariant_in_tr \<open>\<not>invariant_all S''\<close> by blast 
      qed
    qed  
  qed

  obtain as aa where a_def: "a = (as,aa)"
    by force


  have noFails_tr1: "\<And>i. (i, ACrash) \<notin> set tr1"
    using noFails tr_split by auto

  have noFails_tr2: "\<And>i. (i, ACrash) \<notin> set tr2"
    using noFails tr_split by auto


  obtain tr1' S1' 
    where tr1'_steps: "S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'"
      and tr1'_ok: "\<forall>a. (a, False)\<notin>set tr1'"
      and tr1'_coupling: "state_coupling S1 S1' as (tr1 = [] \<or> get_invoc (last tr1) = as)"
  proof (atomize_elim, rule convert_to_single_session_trace)
    show "S ~~ tr1 \<leadsto>* S1" using steps1 .
    show "state_wellFormed S" using S_wellformed .
    show "packed_trace tr1"
      using isPrefix_appendI packed prefixes_are_packed tr_split by blast 
    show "\<And>s. (s, ACrash) \<notin> set tr1"
      using noFails tr_split by auto
    show "\<And>S' tr1'. \<lbrakk>isPrefix tr1' tr1; S ~~ tr1' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using inv_before by auto
    show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      by (simp add: noUncommittedTx)
    show "noContextSwitchesInTransaction tr1"
      using isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split by blast
  qed


  have tr1_packed: "packed_trace (tr1@[a])"     
    using packed proof (rule prefixes_are_packed)
    have "isPrefix (tr1 @ [a]) ((tr1 @ [a]) @ tr2)" by (rule isPrefix_appendI)
    then show "isPrefix (tr1 @ [a]) tr" using tr_split by auto
  qed  


  obtain tr_a S_fail'
    where steps_tr_a: "S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'"
      and tr_a_fails: "\<exists>a. (a, False)\<in>set tr_a"
  proof (atomize_elim, rule convert_to_single_session_trace_invFail_step)
    show "S1 ~~ (as,aa) \<leadsto> S_fail"
      using a_def stepA by blast
    show "state_wellFormed S1"
      using S_wellformed state_wellFormed_combine steps1 noFails_tr1 by blast
    show "aa \<noteq> ACrash"
      using a_def noFails tr_split by auto
    show "invariant_all S1"
      using inv_before isPrefix_refl steps1 by blast
    show "\<not> invariant_all S_fail"
      by (simp add: first_not_inv)
    show "state_coupling S1 S1' as (tr1 = [] \<or> get_invoc (last tr1) = as)"  
      using tr1'_coupling .



    show "\<forall>tx. transactionStatus S1 tx \<noteq> Some Uncommitted " if "aa \<noteq> AEndAtomic"
    proof -
      have  noFails_tr1: "\<And>s. (s, ACrash) \<notin> set tr1"
        using noFails tr_split by auto

      have current_tx:  "\<forall>i. currentTransaction S1 i \<noteq> None \<longrightarrow> i = get_invoc (last tr1)"
      proof (rule at_most_one_current_tx[OF \<open>S ~~ tr1 \<leadsto>* S1\<close>])
        show "noContextSwitchesInTransaction tr1"
          using isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split by blast

        show "packed_trace tr1"
          using packed_trace_prefix tr1_packed by blast

        show "state_wellFormed S"
          by (simp add: S_wellformed)

        show "\<And>s. (s, ACrash) \<notin> set tr1" using noFails_tr1 .

        show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
          by (simp add: noUncommittedTx)
      qed



      have noCurrentTx_a: "currentTransaction S1 (get_invoc a) = None"
      proof (rule no_current_transaction_when_invariant_fails[OF \<open>S1 ~~ a \<leadsto> S_fail\<close> \<open>\<not> invariant_all S_fail\<close>])
        show "state_wellFormed S1"
          by (simp add: \<open>state_wellFormed S1\<close>) 
        show "invariant_all S1"
          by (simp add: \<open>invariant_all S1\<close>)
        show "state_wellFormed S1"
          by (metis \<open>state_wellFormed S1\<close>)
        show "get_action a \<noteq> AEndAtomic"
          by (metis a_def sndI that) 
      qed

      have noCurrentTx: "currentTransaction S1 (get_invoc (last tr1)) = None"
      proof (cases "tr1")
        case Nil
        then have "S1 = S"
          using steps1 steps_refl traceDeterministic by blast
        then show ?thesis 
          by (meson S_wellformed noUncommittedTx not_Some_eq wellFormed_currentTransactionUncommitted)
      next
        case (Cons tr1_first tr1_rest)
        then have tr1_len: "0 < length tr1"
          by simp

        show ?thesis 
        proof (cases "get_invoc (last tr1) = get_invoc a")
          case True
          then show ?thesis
            by (simp add: noCurrentTx_a) 
        next
          case False
          show ?thesis
          proof (rule ccontr)
            assume a0: "currentTransaction S1 (get_invoc (last tr1)) \<noteq> None"

            define invoc where "invoc \<equiv> get_invoc (last tr1)"

            from a0 obtain tx where "currentTransaction S1 invoc \<triangleq> tx"
              by (metis not_Some_eq invoc_def)


            have "\<exists>ib txns. tr1 ! ib = (invoc, ABeginAtomic tx txns) \<and> ib < length tr1 \<and> (\<forall>j. ib < j \<and> j < length tr1 \<longrightarrow> tr1 ! j \<noteq> (invoc, AEndAtomic))"
            proof (rule currentTransaction_exists_beginAtomic[OF \<open>S ~~ tr1 \<leadsto>* S1\<close> \<open>currentTransaction S1 invoc \<triangleq> tx\<close>])
              show "currentTransaction S invoc = None"
                by (metis S_wellformed noUncommittedTx option.exhaust wellFormed_currentTransaction_unique_h(2))
              show "state_wellFormed S"
                by (metis S_wellformed)
              show "\<And>i. (i, ACrash) \<notin> set tr1"
                by (simp add: noFails_tr1) 
            qed
            from this obtain ib txns 
              where ib1: "tr1 ! ib = (invoc, ABeginAtomic tx txns)"
                and ib2: "ib < length tr1"
                and ib3: "\<forall>j. ib < j \<and> j < length tr1 \<longrightarrow> tr1 ! j \<noteq> (invoc, AEndAtomic)"
              by blast


            have steps_fail: "S ~~ tr1@[a] \<leadsto>* S_fail"
              using stepA steps1 steps_step by blast

            have "allowed_context_switch (get_action ((tr1@[a]) ! length tr1))"
            proof (rule use_packed_trace)  
              show " packed_trace (tr1 @ [a])"
                by (simp add: tr1_packed)
              show "0 < length tr1"
                using tr1_len .
              show "length tr1 < length (tr1 @ [a])"
                by simp
              show "get_invoc ((tr1 @ [a]) ! (length tr1 - 1)) \<noteq> get_invoc ((tr1 @ [a]) ! length tr1)"
                by (metis False One_nat_def diff_Suc_less last_conv_nth list.simps(3) local.Cons nth_append nth_append_length tr1_len)
            qed



            moreover have "\<not> allowed_context_switch (get_action ((tr1@[a]) ! length tr1))"
            proof (rule use_noContextSwitchesInTransaction)
              show "noContextSwitchesInTransaction (tr1 @ [a])"
                by (metis append.assoc append_Cons append_Nil isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split)
              show "(tr1 @ [a]) ! ib = (invoc, ABeginAtomic tx txns)"
                by (metis ib1 ib2 nth_append)
              show " ib < length (tr1@[a])"
                using ib2  by simp
              show "length (tr1 @ [a]) \<le> length (tr1 @ [a])" 
                by simp
              show "\<forall>j. ib < j \<and> j < length (tr1 @ [a]) \<longrightarrow> (tr1 @ [a]) ! j \<noteq> (invoc, AEndAtomic)"
                apply (auto simp add: nth_append ib3)
                by (metis False fst_conv invoc_def)
              show "ib < length tr1" using ib2 .
              show "length tr1 < length (tr1 @ [a])"
                by simp
            qed
            ultimately show False by simp
          qed
        qed
      qed


      have "transactionStatus S1 tx \<noteq> Some Uncommitted" for tx
      proof 
        assume a: "transactionStatus S1 tx \<triangleq> Uncommitted"

        obtain invoc where "currentTransaction S1 invoc = Some tx"
          using uncommitted_tx_is_current_somewhere[OF \<open>S ~~ tr1 \<leadsto>* S1\<close> \<open>state_wellFormed S\<close> noFails_tr1 noUncommittedTx a] by blast

        then have "invoc = get_invoc (last tr1)"
          by (simp add: current_tx)

        with \<open>currentTransaction S1 invoc = Some tx\<close> show False
          by (simp add: noCurrentTx)
      qed
      then show "\<forall>tx. transactionStatus S1 tx \<noteq> Some Uncommitted"
        by simp
    qed




    assume "\<not> (tr1 = [] \<or> get_invoc (last tr1) = as)"
    then have "tr1 \<noteq> []" and "get_invoc (last tr1) \<noteq> as"
      by auto
    show "allowed_context_switch aa"  
      using tr1_packed proof (rule context_switches_in_packed)
      show "tr1 @ [a] = butlast tr1 @ [(get_invoc (last tr1), get_action (last tr1)), (as, aa)] @ []"
        by (simp add: \<open>tr1 \<noteq> []\<close> a_def)
      show "get_invoc (last tr1) \<noteq> as"
        by (simp add: \<open>get_invoc (last tr1) \<noteq> as\<close>)
    qed    
  qed    

  show ?thesis
  proof (rule exI[where x="tr1'@tr_a"], rule exI[where x="S_fail'"], rule exI[where x="as"], intro conjI)
    from \<open>S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'\<close> 
      and \<open>S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'\<close>
    show " S ~~ (as, tr1' @ tr_a) \<leadsto>\<^sub>S* S_fail'"
      by (rule steps_s_append)  
    show "\<exists>a. (a, False) \<in> set (tr1' @ tr_a)"
      using tr_a_fails by auto
  qed
qed


text \<open>if there is an failing invariant check in the trace, then there is a prefix of the trace leading to a
  state that does not satisfy the invariant\<close>
lemma invCheck_to_failing_state:
  assumes steps: "S ~~ trace \<leadsto>* S'"
    and inv_fail: "(s, AInvcheck False) \<in> set trace"
    and state_wf: "state_wellFormed S"
    and noFail: "\<And>i. (i, ACrash) \<notin> set trace"
  shows "\<exists>tr' S_fail. isPrefix tr' trace \<and> (S ~~ tr' \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail" 
  using steps inv_fail noFail proof (induct rule: steps_induct)
  case initial
  then show ?case
    by auto 
next
  case (step S' tr a S'')

  have noFail_tr: "\<And>i. (i, ACrash) \<notin> set tr"
    using step by auto


  show ?case 
  proof (cases "(s, AInvcheck False) \<in> set tr")
    case True
    with step.IH
    obtain tr' S_fail 
      where "isPrefix tr' tr" 
        and"S ~~ tr' \<leadsto>* S_fail" 
        and "\<not> invariant_all S_fail"
      using noFail_tr by blast

    then show ?thesis
      using isPrefix_append by blast 

  next
    case False
    with \<open>(s, AInvcheck False) \<in> set (tr @ [a])\<close>
    have "a = (s, AInvcheck False)" by auto

    show ?thesis
    proof (intro exI conjI)
      show "isPrefix (tr @ [a]) (tr @ [a])"
        by (simp add: isPrefix_refl)
      show "S ~~ tr @ [a] \<leadsto>* S''"
        using step.step step.steps steps_step by fastforce   

      from \<open>S' ~~ a \<leadsto> S''\<close>
      have "S' ~~ (s, AInvcheck False) \<leadsto> S''" using \<open>a = (s, AInvcheck False)\<close> by simp
      then have  [simp]: "S'' = S'" 
        and invFail: "\<not> invariant (prog S') (invContext S')"
        by (auto simp add: step_simps)


      show "\<not> invariant_all S''"
        using invFail by auto  
    qed
  qed
qed

lemma GreatestI: 
  "\<lbrakk>P k; \<forall>y. P y \<longrightarrow> y < b\<rbrakk> \<Longrightarrow> P (GREATEST x. P x)"
  for k :: nat
  by (metis GreatestI_nat le_eq_less_or_eq)

lemma GreatestI2:
  assumes example: "Q k"
    and impl: "\<And>i. Q i \<Longrightarrow> P i"
    and bound: "\<And>i. Q i \<Longrightarrow> i < bound"
  shows "P (GREATEST x::nat. Q x)"
  using assms GreatestI by blast 

lemma prefix_induct[case_names Nil snoc[IH]]:
  assumes empty: "P []"
    and step: "\<And>ys a. \<lbrakk>\<And>xs. isPrefix xs ys \<Longrightarrow> P xs\<rbrakk> \<Longrightarrow> P (ys@[a])"
  shows "P xs"
proof -
  have "\<forall>xs'. isPrefix xs' xs \<longrightarrow> P xs'"
    using assms proof (induct rule: rev_induct)
    case Nil
    then show ?case
      by (simp add: isPrefix_empty)
  next
    case (snoc x ys)
    show ?case
    proof auto
      fix xs' 
      assume a1: "isPrefix xs' (ys @ [x])"
      show "P xs'"
      proof (cases "isPrefix xs' ys")
        case True
        then show ?thesis
          using local.empty local.step snoc.hyps by blast 
      next
        case False
        with a1
        have "xs' = ys@[x]"
          apply (auto simp add: isPrefix_def)
          by (metis append_self_conv butlast.simps(2) diff_is_0_eq nat_le_linear not_le take_all take_butlast take_eq_Nil)

        have " P (ys@[x])"
        proof (rule local.snoc(3))
          show "\<And>xs. isPrefix xs ys \<Longrightarrow> P xs"
            using local.empty local.step snoc.hyps by blast
        qed    
        then show "P xs'" using \<open>xs' = ys@[x]\<close> by simp
      qed
    qed
  qed
  then show "P xs"
    using isPrefix_refl by blast
qed  

lemma smallestPrefix_exists:
  fixes tr :: "'a list"
    and  x :: 'b
  assumes example: "P tr x"
  shows "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not>isPrefix tr' tr)"
  using example proof (induct tr arbitrary: x rule: prefix_induct)
  case Nil
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="x"], auto simp add: isPrefix_empty)
    show "P [] x" using Nil .
  qed
next
  case (snoc xs a)
  show ?case 
  proof (cases "\<exists>tr' x'. P tr' x' \<and> isPrefix tr' xs")
    case True
    from this obtain tr' x'
      where "isPrefix tr' xs" and "P tr' x'"
      by blast
    then show "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
      by (rule snoc.IH)
  next 
    case False
    then have noPrefix: "\<not>isPrefix tr' xs" if "P tr' x'" for tr' x'
      using that by blast

    show " \<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
    proof (rule exI[where x="xs@[a]"], rule exI[where x=x], intro conjI allI impI; (elim conjE)?)
      show "P (xs @ [a]) x"
        using snoc.prems .
      fix tr' x'
      assume "P tr' x'"
      then have "\<not>isPrefix tr' xs"
        using False by blast
      fix tr' x'
      assume a0: "P tr' x'"
        and a1: "tr' \<noteq> xs @ [a]"

      show "\<not> isPrefix tr' (xs @ [a])"
        by (metis False a0 a1 butlast_snoc isPrefix_def not_le take_all take_butlast)
    qed    
  qed 
qed


text \<open>
When a program is correct in the single invocId semantics, 
it is also correct when executed in the concurrent interleaving semantics.
\<close>
theorem show_correctness_via_single_session:
  assumes works_in_single_session: "programCorrect_s program"
    and inv_init: "invariant_all (initialState program)"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving'')
  text \<open>Assume we have a trace and a final state S\<close>
  fix trace S
  text \<open>Such that executing the trace finishes in state S.\<close>
  assume steps: "initialState program ~~ trace \<leadsto>* S"

  text \<open>We can assume the trace is packed.\<close>
  assume packed: "packed_trace trace"

  text \<open>We may also assume that there are no failures\<close>
  assume noFail: "\<And>s. (s, ACrash) \<notin> set trace"

  assume "allTransactionsEnd trace"

  assume noInvchecksInTxns: "no_invariant_checks_in_transaction trace"

  text \<open>We show that the trace must be correct (proof by contradiction).\<close>
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"

    text \<open>If the trace is incorrect, there must be a failing invariant check in the trace:\<close>
    from this obtain s where "(s, AInvcheck False) \<in> set trace"
      using steps by (auto simp add: traceCorrect_def)

    obtain tr' S_fail
      where "isPrefix tr' trace"
        and "initialState program ~~ tr' \<leadsto>* S_fail"
        and "\<not> invariant_all S_fail"
      using \<open>(s, AInvcheck False) \<in> set trace\<close> invCheck_to_failing_state state_wellFormed_init steps noFail by blast 

    text \<open>No take the first state where the invariant fails\<close>
    from this
    obtain tr'_min S_fail_min
      where tr'_min_prefix: "isPrefix tr'_min trace"
        and S_fail_min_steps:"initialState program ~~ tr'_min \<leadsto>* S_fail_min"
        and S_fail_min_fail: "\<not> invariant_all S_fail_min"    
        and S_fail_min_min: "\<And>tr' S_fail. \<lbrakk>isPrefix tr' trace; initialState program ~~ tr' \<leadsto>* S_fail; \<not> invariant_all S_fail; tr' \<noteq> tr'_min\<rbrakk> \<Longrightarrow> \<not>isPrefix tr' tr'_min"
      using smallestPrefix_exists[where P="\<lambda>tr x. isPrefix tr trace \<and> (initialState program ~~ tr \<leadsto>* x) \<and> \<not> invariant_all x"]
      by metis

    text \<open>Next get the invocId start before the failure\<close>  



    obtain tr'_s S_fail_s s'
      where "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        and "\<exists>a. (a, False) \<in> set tr'_s"
    proof (atomize_elim)
      have "\<exists>tr'_s S_fail_s s'. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
      proof (rule convert_to_single_session_trace_invFail[OF \<open>initialState program ~~ tr' \<leadsto>* S_fail\<close>])
        show "state_wellFormed (initialState program)"
          by (simp add: state_wellFormed_init)
        show "packed_trace tr'"
          using \<open>isPrefix tr' trace\<close> packed prefixes_are_packed by blast
        show "\<And>s'. (s', ACrash) \<notin> set tr'"
          using \<open>isPrefix tr' trace\<close> noFail apply (auto simp add: isPrefix_def) (* IMPROVE extract lemma for isPrefix with \<in> or \<subseteq> *)
          by (metis in_set_takeD)
        show "invariant_all (initialState program)"
          using inv_init .
        show "\<not> invariant_all S_fail"
          by (simp add: \<open>\<not> invariant_all S_fail\<close>)
        show "\<And>tx. transactionStatus (initialState program) tx \<noteq> Some Uncommitted"
          by (simp add: initialState_def)
        show " noContextSwitchesInTransaction tr'"
          by (metis \<open>allTransactionsEnd trace\<close> \<open>isPrefix tr' trace\<close> \<open>state_wellFormed (initialState program)\<close> noContextSwitchesInTransaction_when_packed_and_all_end noFail packed prefixes_noContextSwitchesInTransaction steps)

      qed
      then show "\<exists>s' tr'_s S_fail_s. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
        by blast
    qed

    have not_correct: "\<not>traceCorrect_s  tr'_s"
      by (simp add: \<open>\<exists>a. (a, False) \<in> set tr'_s\<close> traceCorrect_s_def)



(*
    from works_in_single_session
    have use_single_session: "traceCorrect_s program trace" if "invariant program (invContext init s)" and "prog init = program" and "init ~~ (s, trace) \<leadsto>\<^sub>S* S" for init trace s S
      using that by (auto simp add: programCorrect_s_def)
    *)
    from works_in_single_session
    have use_single_session: "traceCorrect_s  trace" if "initialState program ~~ (s, trace) \<leadsto>\<^sub>S* S" for  trace s S
      using that by (auto simp add: programCorrect_s_def)  

    have correct: "traceCorrect_s  tr'_s" 
    proof (rule use_single_session)
      show "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        using \<open>initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s\<close> .
    qed    

    with not_correct
    show False ..
  qed
qed  



end
