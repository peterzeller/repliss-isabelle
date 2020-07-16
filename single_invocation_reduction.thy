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
definition state_coupling :: "('proc::valueType, 'ls, 'op, 'any::valueType) state \<Rightarrow> ('proc, 'ls, 'op, 'any) state \<Rightarrow> invocId \<Rightarrow> bool \<Rightarrow> bool" where
  "state_coupling S S' i sameInvoc \<equiv> 
   if sameInvoc then
      \<comment> \<open>  did a step in the same invocId  \<close>
      S' = S
   else 
      \<comment> \<open>  did step in a different invocId  \<close>
        state_monotonicGrowth i S' S
      "

text \<open>\DefineSnippet{state_coupling_def}{
  @{thm [display] state_coupling_def}
}%EndSnippet\<close>


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
  moreover have [simp]: "txOrigin S' = txOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "txStatus S' = txStatus S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "happensBefore S' = happensBefore S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "calls S' = calls S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "knownIds S' = knownIds S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocOp S' = invocOp S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocRes S' = invocRes S" using assms by (auto simp add: state_coupling_def split: if_splits)

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
    and noUncommitted: "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
    and noContextSwitch: "\<not>contextSwitchesInTransaction tr"
    and ls_None: "localState S' i = None"
    and i_is_last: "tr = [] \<or> get_invoc (last tr) = i"
  shows "currentTx S' i' = None"
proof -

  have S'_wf: "state_wellFormed S'"
    using S_wf noChrash state_wellFormed_combine steps by blast


  have vis_None: "visibleCalls S' i = None"
    using S'_wf ls_None state_wellFormed_ls_visibleCalls by blast


  have at_most_one_tx: "(\<forall>i tx. ((i, tx) \<in> openTransactions tr) = currentTx S' i \<triangleq> tx) \<and> (\<forall>i j. currentTx S' i \<noteq> None \<and> currentTx S' j \<noteq> None \<longrightarrow> i = j)"
  proof (rule at_most_one_active_tx[OF \<open> S ~~ tr \<leadsto>* S'\<close>])
    show "state_wellFormed S"
      using S_wf by auto
    show "packed_trace tr"
      by (simp add: packed)
    show " \<And>s. (s, ACrash) \<notin> set tr"
      using noChrash by auto
    show  " \<And>tx. txStatus S tx \<noteq> Some Uncommitted"
      using noUncommitted by blast
    show  "\<not> contextSwitchesInTransaction tr"
      by (simp add: noContextSwitch)
  qed


  have noCurrentTransactionI: "currentTx S' i = None"
    by (meson S'_wf option.exhaust_sel state_wellFormed_tx_to_visibleCalls vis_None)

  find_theorems contextSwitchesInTransaction

  show noCurrentTransaction: "currentTx S' i' = None" 
    using at_most_one_current_tx[OF \<open>S ~~ tr \<leadsto>* S'\<close> \<open>\<not> contextSwitchesInTransaction tr\<close> \<open>packed_trace tr\<close> \<open>state_wellFormed S\<close> \<open>\<And>s. (s, ACrash) \<notin> set tr\<close> noUncommitted]
    using i_is_last noCurrentTransactionI
    by (metis S'_wf noUncommitted option.exhaust steps steps_empty wellFormed_currentTx_unique_h(2)) 


qed

text \<open>
If we have an execution on a a single invocId starting with state satisfying the invariant, then we can convert 
this trace to a single-invocId trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
\<close>
text_raw \<open>\DefineSnippet{convert_to_single_session_trace}{\<close>
lemma convert_to_single_session_trace:
  fixes tr :: "('proc::valueType, 'op, 'any::valueType) trace"
    and i :: invocId      
    and S S' :: "('proc, 'ls, 'op, 'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommitted:  "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "\<not>contextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds on all states in the execution\<close>
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
    and noAssertionFail: "\<And>a. a\<in>set tr \<Longrightarrow> get_action a \<noteq> ALocal False"
  shows "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 i (tr = [] \<or> get_invoc (last tr) = i))"
text_raw \<open>}%EndSnippet\<close>
  using steps S_wellformed packed inv noFails noUncommitted noCtxtSwitchInTx noAssertionFail
proof (induct rule: steps.induct)
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
    and noContextSwitch: "\<not>contextSwitchesInTransaction (tr @ [a])"
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
        and tx_same: "currentTx S2 i = currentTx S' i" 
        and visible_same: "visibleCalls S2 i = visibleCalls S' i"
        by (auto simp add:  state_monotonicGrowth_localState state_monotonicGrowth_currentProc state_monotonicGrowth_currentTx state_monotonicGrowth_visibleCalls)




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
                    invocOp := invocOp S'(i \<mapsto> p)\<rparr>"
            and a2: "localState S' i = None"
            and a3: "procedure (prog S') p = (initial, impl)"
            and a4: "uniqueIds p \<subseteq> knownIds S'"
            and a5: "invocOp S' i = None"
          by metis

        show "\<exists>tr' S2. (S ~~ (i, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 i True"
        proof (intro exI conjI)
          have "S2 ~~ (i, AInvoc p, True) \<leadsto>\<^sub>S S''"
          proof (rule step_s.intros)
            have "\<And>p. invocOp S2 i \<noteq> Some p"
              using a5 ih3' by (metis option.distinct(1) state_coupling_def state_monotonicGrowth_invocOp)
            then show "invocOp S2 i = None" by blast
            have [simp]: "prog S2 = prog S'"
              by (metis ih3' state_coupling_def state_monotonicGrowth_prog)
            show "procedure (prog S2) p = (initial, impl)"
              using a3 state_coupling_def by auto
            show "uniqueIds p \<subseteq> knownIds S'"
              using a4 ih3' state_coupling_def by auto
            show "invariant_all S'"
              by (simp add: inv')
            show "invocOp S' i = None" using a5  .
            show "S'' = S'\<lparr>localState := localState S'(i \<mapsto> initial), currentProc := currentProc S'(i \<mapsto> impl), visibleCalls := visibleCalls S'(i \<mapsto> {}), invocOp := invocOp S'(i \<mapsto> p)\<rparr>"
              using a1 by auto
            show "True = invariant_all S''"
              by (simp add: inv'')
            show "prog S' = prog S2"
              by simp
            show "state_wellFormed S'"
              using S_wf state_wellFormed_combine steps noFails by auto

            have "currentTx S' i = None"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wellFormed_invoc_notStarted(1))

            have "\<And>s. (s, ACrash) \<notin> set tr"
              using steps_step.prems(4) by auto


            have "currentTx S' s = None" for s
              by (metis S_wf \<open>get_invoc a = i\<close> \<open>state_wellFormed S'\<close> a5 at_most_one_current_tx last_snoc noContextSwitch noFails packed step' steps' steps_step.prems(5) unchangedInTransaction(3) wellFormed_invoc_notStarted(1))

            from this
            show "\<And>tx. txStatus S' tx \<noteq> Some Uncommitted"
              using wellFormed_currentTx_back[OF steps \<open>\<And>s. (s, ACrash) \<notin> set tr\<close> \<open>\<And>tx. txStatus S tx \<noteq> Some Uncommitted\<close> \<open>state_wellFormed S\<close>]
              by auto


            have "\<And>tx. txOrigin S' tx \<noteq> Some i"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wf_no_invocation_no_origin)

            then show "\<And>tx. txOrigin S'' tx \<noteq> Some i"
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
                    currentTx := currentTx S'(i \<mapsto> tx), 
                    txStatus := txStatus S'(tx \<mapsto> Uncommitted),
                    txOrigin := txOrigin S'(tx \<mapsto> i), 
                    visibleCalls := visibleCalls S'(i \<mapsto> snapshot)\<rparr>"
            and a2: "localState S' i \<triangleq> ls"
            and a3: "currentProc S' i \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTx S' i = None"
            and a6: "txStatus S' tx = None"
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
            show "currentTx S2 i = None"
              using a5 tx_same by auto
            show "txStatus S2 tx = None"
            proof -
              from ih3 have "txStatus S2 tx \<le> txStatus S' tx"
                by (auto simp add: state_coupling_def state_monotonicGrowth_txStatus)
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
            show "currentTx S' i = None"
              by (simp add: a5)
            show "txStatus S' tx = None"
              by (simp add: a6)
            show "txOrigin S' tx = None"
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
              using `txStatus S' tx = None`
                and wf_no_txStatus_origin_for_nothing[OF \<open>state_wellFormed S'\<close>] by simp


            have "\<forall>i. currentTx S'' i \<noteq> None \<longrightarrow> i = get_invoc (last (tr@[a]))"
            proof (rule at_most_one_current_tx)
              show "S ~~ tr @ [a] \<leadsto>* S''"
                using steps' by auto

              show " \<not>contextSwitchesInTransaction (tr@[a])"
                using  noContextSwitch  by blast
              show "packed_trace (tr@[a])"
                using packed by blast
              show "state_wellFormed S"
                by (simp add: S_wf)
              show "\<And>s. (s, ACrash) \<notin> set (tr@[a])"
                using noFails by blast
              show "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
                by (simp add: steps_step.prems(5))
            qed
            then have noCurrentTransaction: "currentTx S'' i' = None" if "i'\<noteq>i" for i'
              using that by auto
            have "\<And>tx'. tx' \<noteq> tx \<Longrightarrow> txStatus S'' tx' \<noteq> Some Uncommitted"
            proof (rule wellFormed_currentTx_back4[OF \<open>state_wellFormed S''\<close>])
              fix tx' i'
              assume a: "tx' \<noteq> tx"

              show "currentTx S'' i' \<noteq> Some tx'"
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


            then show "\<And>tx. txStatus S' tx \<noteq> Some Uncommitted"
              apply (simp add: a1)
              using a6 by force

            show "S'' = S'\<lparr>txStatus := txStatus S'(tx \<mapsto> Uncommitted), txOrigin := txOrigin S'(tx \<mapsto> i), currentTx := currentTx S'(i \<mapsto> tx),
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


            have wf_S': "state_wellFormed S'"
              using S_wf noFails_tr state_wellFormed_combine steps by auto

            have "consistentSnapshot S'' snapshot"
              using \<open>state_wellFormed S''\<close>
            proof (rule wellFormed_state_consistent_snapshot)
              show "visibleCalls S'' i \<triangleq> snapshot"
                by (auto simp add: a1)
              show "\<And>c tx. currentTx S'' i \<triangleq> tx \<Longrightarrow> callOrigin S'' c \<noteq> Some tx"
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
      have S2_currentTx: "currentTx S2 = currentTx S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_txStatus: "txStatus S2 = txStatus S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_callOrigin: "callOrigin S2 = callOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_txOrigin: "txOrigin S2 = txOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_generatedIds: "generatedIds S2 = generatedIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_knownIds: "knownIds S2 = knownIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocOp: "invocOp S2 = invocOp S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocRes: "invocRes S2 = invocRes S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)

      note S2_simps = 
        S2_calls S2_happensBefore S2_prog S2_localState S2_currentProc S2_currentTx
        S2_txStatus S2_callOrigin S2_txOrigin S2_generatedIds S2_knownIds S2_invocOp S2_invocRes


      have S'_wf: "state_wellFormed S'"
        using S_wf steps noFails_tr by (rule state_wellFormed_combine)


      have vis_defined: "visibleCalls S' i \<noteq> None" if "currentTx S' i \<noteq> None"
        using S'_wf state_wellFormed_tx_to_visibleCalls that by auto

      have tr_noSwitch: "\<not>contextSwitchesInTransaction tr"
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

          show all_ok: " \<forall>x. (x, False) \<notin> set (tr' @ [(get_action a, True)])"
            by (simp add: ih2)

          have "S' ~~ (i,get_action a, True) \<leadsto>\<^sub>S S''"
          proof (cases "get_action a")
            case (ALocal ok)
            then have [simp]: "a = (i, ALocal ok)"
              by (simp add: prod.expand) 

            hence ok
              using `a \<in> set (tr @ [a]) \<Longrightarrow> get_action a \<noteq> ALocal False` by fastforce

            show ?thesis
              using step unfolding step.simps step_s.simps by (auto simp add: `ok`)


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

lemma invContext_changed_cases:
  assumes step: "S ~~ (i,a) \<leadsto> S'"
    and different: "invContext S' \<noteq> invContext S"
and S_wellformed: "state_wellFormed S"
  shows "a = AEndAtomic \<or> (\<exists>p. a = AInvoc p) \<or> (\<exists>r. a = AReturn r)"
  using step different apply (auto simp add: step.simps )
   apply (auto simp add: invContextH_def committedCallsH_update_uncommitted 
      restrict_relation_def S_wellformed committedCalls_unchanged_callOrigin wellFormed_callOrigin_dom3 wellFormed_currentTx_unique_h(2)
      split: if_splits)
  subgoal
    by (metis  option.distinct(1))
  subgoal
    using noOrigin_notCommitted by (auto simp add: restrict_relation_def S_wellformed committedCalls_unchanged_callOrigin wellFormed_callOrigin_dom3 wellFormed_currentTx_unique_h(2))
  subgoal
    by (auto simp add: restrict_map_def S_wellformed committedCalls_unchanged_callOrigin wellFormed_callOrigin_dom3 wellFormed_committedCallsExist wellFormed_currentTx_unique_h(2))
  subgoal
    apply (auto simp add: restrict_map_def S_wellformed committedCalls_unchanged_callOrigin wellFormed_callOrigin_dom3 wellFormed_currentTx_unique_h(2))
    using S_wellformed noOrigin_notCommitted wellFormed_callOrigin_dom2 by blast
  done

lemma invContext_unchanged:
assumes step: "S ~~ (i,a) \<leadsto> S'"
and cases:"a = ALocal ok \<or> a = ANewId uidv \<or> a = ABeginAtomic t snapshot \<or> a = ADbOp c Op res"
and S_wellformed: "state_wellFormed S"
shows "invContext S' = invContext S"
  using invContext_changed_cases[OF step] cases S_wellformed  by (case_tac a, auto)


lemma inv_unchanged:
assumes step: "S ~~ (i,a) \<leadsto> S'"
and S_wellformed: "state_wellFormed S"
and cases:"a = ALocal ok \<or> a = ANewId uidv \<or> a = ABeginAtomic t snapshot \<or> a = ADbOp c Op res"
shows "invariant_all S' = invariant_all S"
  using invContext_unchanged[OF step cases S_wellformed ] prog_inv[OF step] by auto

lemma inv_unchanged2:
assumes step: "S ~~ (i,a) \<leadsto> S'"
and S_wellformed: "state_wellFormed S"
shows "a = ALocal ok  \<Longrightarrow> invariant_all S' = invariant_all S"
and "a = ANewId uidv \<Longrightarrow> invariant_all S' = invariant_all S"
and "a = ABeginAtomic t snapshot  \<Longrightarrow> invariant_all S' = invariant_all S"
and " a = ADbOp c Op res \<Longrightarrow> invariant_all S' = invariant_all S"
  using inv_unchanged[OF step S_wellformed ] by auto


text_raw \<open>\DefineSnippet{convert_to_single_session_trace_invFail_step}{\<close>
lemma convert_to_single_session_trace_invFail_step:
  fixes tr :: "('proc::valueType, 'op, 'any::valueType) trace"
    and i :: invocId      
    and S S' :: "('proc, 'ls, 'op, 'any) state"
  assumes step: "S ~~ (i,a) \<leadsto> S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "a \<noteq> ACrash"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not>invariant_all S'"
    and coupling: "state_coupling S S2 i sameSession"
    and ctxtSwitchCases: "\<not>sameSession \<Longrightarrow> allowed_context_switch a" 
    and noUncommitted:  "\<And>p. a = AInvoc p \<Longrightarrow>  \<forall>tx. txStatus S tx \<noteq> Some Uncommitted"
shows "(S2 ~~ (i, a, False) \<leadsto>\<^sub>S S')"
text_raw \<open>}%EndSnippet\<close>

  using step proof (cases rule: step.cases)

  case (endAtomic ls f ls' t)
  text \<open>Ending a transaction includes an invariant-check in the single-invocId semantics, so we get a failing trace.\<close>


  have [simp]: "sameSession"
    using `a = AEndAtomic` ctxtSwitchCases by blast

  hence "S2 = S"
    by (meson coupling state_coupling_def)

  have "state_wellFormed S'"
    using S_wellformed `a = AEndAtomic` local.step state_wellFormed_combine_step by fastforce


  have "S ~~ (i,(AEndAtomic, False)) \<leadsto>\<^sub>S S'"
    using not_inv `state_wellFormed S'`
    by (auto simp add: step_s.simps endAtomic )

  then show ?thesis
    using `a = AEndAtomic` `S2 = S` by auto
next
  case (invocation proc initialState impl)
  text \<open>invocations include an invariant-check\<close>


  have [simp]: "prog S2 = prog S"
    by (metis coupling state_coupling_def state_monotonicGrowth_prog)

  have "localState S2 i = None"
    using invocation coupling
    by (metis state_coupling_def state_monotonicGrowth_localState)
  have "\<And>x. invocOp S2 i \<noteq> Some x"
    using invocation coupling by (auto simp add: state_coupling_def state_monotonicGrowth_invocOp split: if_splits)
  then have [simp]: "invocOp S2 i = None" by blast     

  have no_transactions: "txOrigin S tx \<noteq> Some i" for tx
    using wf_no_invocation_no_origin[OF S_wellformed] `invocOp S i = None` by simp


  show "S2 ~~ (i, a, False) \<leadsto>\<^sub>S S'"
    using invocation inv not_inv 
    by (auto simp add: step_s.simps S_wellformed noUncommitted no_transactions)

next
  case (return ls f res)
  text \<open>return contains an invariant check\<close>


  have [simp]: sameSession
    using `a = AReturn res` ctxtSwitchCases by auto
  hence "S2 = S"
    by (meson coupling state_coupling_def)

  have "S  ~~ (i,(AReturn res, False)) \<leadsto>\<^sub>S S'"
    using not_inv  by (auto simp add: step_s.simps return)

  then show ?thesis
    using \<open>S2 = S\<close> \<open>a = AReturn res\<close> by blast
next    
  case (crash ls)
  text \<open>we assumed that there are no fails\<close>
  then show ?thesis
    using noFails by blast
\<comment> \<open>remaining cases cannot change the invariant\<close>
qed (insert inv not_inv inv_unchanged[OF step S_wellformed], auto)

lemma uncommitted_tx_is_current_somewhere:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
    and tx_uncommitted: "txStatus S' tx \<triangleq> Uncommitted"
  shows "\<exists>invoc. currentTx S' invoc \<triangleq> tx" 
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
  shows "currentTx S (get_invoc a) = None"
proof (rule ccontr)
  assume " currentTx S (get_invoc a) \<noteq> None"
  from this obtain tx where ctx: "currentTx S (get_invoc a) \<triangleq> tx"
    by (metis not_None_eq)

  have uncommitted: "txStatus S tx \<triangleq> Uncommitted"
    by (metis ctx local.wf wellFormed_currentTxUncommitted)



  have committedCallsH_same: "committedCallsH (callOrigin S_fail) (txStatus S_fail) = committedCallsH (callOrigin S) (txStatus S)"
    using \<open>S ~~ a \<leadsto> S_fail\<close>
    using \<open>currentTx S (get_invoc a) \<noteq> None\<close> noEndAtomic apply (auto simp add: step.simps committedCallsH_def )
     apply (auto simp add: isCommittedH_def split: if_splits)
    using wellFormed_currentTxUncommitted[OF wf] apply auto
    by (metis local.wf option.distinct(1) wellFormed_callOrigin_dom2)


  have committedCallsExist: "calls S c = None \<Longrightarrow> c \<notin> committedCalls S" for c
    by (metis local.wf wellFormed_committedCallsExist)


  have "invContext S_fail = invContext S" 
    apply (auto simp add: invContextH_def committedCallsH_same)
    using \<open>S ~~ a \<leadsto> S_fail\<close> noEndAtomic \<open>currentTx S (get_invoc a) \<noteq> None\<close>
    by (auto simp add: step.simps restrict_map_def restrict_relation_def committedCallsExist inTransaction_localState[OF wf])

  with   \<open>\<not> invariant_all S_fail\<close> \<open>invariant_all S\<close>
  show False
    by (metis (no_types, lifting)  prog_inv[OF \<open>S ~~ a \<leadsto> S_fail\<close>] )
qed


text_raw \<open>\DefineSnippet{convert_to_single_session_trace_invFail}{\<close>
lemma convert_to_single_session_trace_invFail:
  fixes tr :: "('proc::valueType, 'op, 'any::valueType) trace"
    and S S' :: "('proc, 'ls, 'op, 'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
    and noContextSwitches: "\<not>contextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not> invariant_all S'"
    and noAssertionErrors: "\<And>a. a\<in>set tr \<Longrightarrow> get_action a \<noteq> ALocal False"
  shows "\<exists>tr' S2 s. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
  text_raw \<open>}%EndSnippet\<close>
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
    show "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
      by (simp add: noUncommittedTx)
    show "\<not>contextSwitchesInTransaction tr1"
      using isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split by blast
    show "\<And>a. a \<in> set tr1 \<Longrightarrow> get_action a \<noteq> ALocal False"
      by (simp add: noAssertionErrors tr_split)
  qed


  have tr1_packed: "packed_trace (tr1@[a])"     
    using packed proof (rule prefixes_are_packed)
    have "isPrefix (tr1 @ [a]) ((tr1 @ [a]) @ tr2)" by (rule isPrefix_appendI)
    then show "isPrefix (tr1 @ [a]) tr" using tr_split by auto
  qed  


  have steps_tr_a: "S1' ~~ (as, aa, False) \<leadsto>\<^sub>S S_fail"
  proof (rule convert_to_single_session_trace_invFail_step)
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

    

    show "\<forall>tx. txStatus S1 tx \<noteq> Some Uncommitted " if " aa = AInvoc p" for p
    proof -

      have tr1a_isPrefix: "isPrefix (tr1@[a]) tr"
        using tr_split
        by (simp add: isPrefix_def)

      have "\<not>contextSwitchesInTransaction (tr1@[a])"
        using tr1a_isPrefix noContextSwitches prefixes_noContextSwitchesInTransaction by blast


      have steps_tr1_a: "S ~~ tr1 @ [a] \<leadsto>* S_fail"
        using \<open>S1 ~~ (as, aa) \<leadsto> S_fail\<close> a_def steps1 steps_step by blast



      have "\<forall>i. currentTx S_fail i \<noteq> None \<longrightarrow> i = get_invoc (last (tr1@[a]))"
        using steps_tr1_a `\<not>contextSwitchesInTransaction (tr1@[a])` `packed_trace (tr1@[a])`
          S_wellformed
      proof (rule at_most_one_current_tx)
        show "\<And>s. (s, ACrash) \<notin> set (tr1 @[a])"
          by (metis in_set_takeD isPrefix_def noFails tr1a_isPrefix)
        show "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
          using noUncommittedTx .
      qed

      hence h0': "\<forall>i. currentTx S_fail i \<noteq> None \<longrightarrow> i = as"
        by (simp add: a_def)

      have "currentTx S1 i = None" if "i \<noteq> as" for i
        by (metis \<open>S1 ~~ (as, aa) \<leadsto> S_fail\<close> h0' that unchangedInTransaction(3))

      have h1: "\<And>tx. currentTx S1 as \<noteq> Some tx \<Longrightarrow> txStatus S1 tx \<noteq> Some Uncommitted" 
        using \<open>\<And>i. i \<noteq> as \<Longrightarrow> currentTx S1 i = None\<close> \<open>state_wellFormed S1\<close> wellFormed_currentTx_back3 by force


      show ?thesis
      using \<open>S1 ~~ (as, aa) \<leadsto> S_fail\<close> \<open>invariant_all S1\<close> \<open>state_wellFormed S1\<close> first_not_inv h1 no_current_transaction_when_invariant_fails that by fastforce
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
  proof (rule exI[where x="tr1'@[(aa, False)]"], rule exI[where x="S_fail"], rule exI[where x="as"], intro conjI)
    from \<open>S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'\<close> 
      and \<open>S1' ~~ (as, aa, False) \<leadsto>\<^sub>S S_fail\<close>
    show " S ~~ (as, tr1' @ [(aa, False)]) \<leadsto>\<^sub>S* S_fail"
      using steps_s_step by blast
    show "\<exists>a. (a, False) \<in> set (tr1' @ [(aa, False)])"
      by auto
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

(* TODO move to utils *)

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

(* TODO utils *)

lemma last_take:
  assumes "n \<le> length xs"
    and "n > 0"
  shows "last (take n xs) = xs ! (n - 1)"
  by (metis (no_types, lifting) assms(1) assms(2) diff_less last_conv_nth length_greater_0_conv length_take min.absorb2 nth_take zero_less_one)

lemma cases2: 
  assumes "A \<or> B"
    and "A \<Longrightarrow> P"
    and "\<not>A \<Longrightarrow> B \<Longrightarrow> P"
  shows P
  using assms by auto

lemma cases2_rev: 
  assumes "B \<or> A"
    and "\<not>A \<Longrightarrow> B \<Longrightarrow> P"
    and "A \<Longrightarrow> P"
  shows P
  using assms by auto

text \<open>
When a program is correct in the single invocId semantics, 
it is also correct when executed in the concurrent interleaving semantics.
\<close>
text_raw \<open>\DefineSnippet{show_correctness_via_single_session}{\<close>
theorem show_correctness_via_single_session:
  assumes works_in_single_session: "programCorrect_s program"
    and inv_init: "invariant_all (initialState program)"
shows "programCorrect program"
  text_raw \<open>}%EndSnippet\<close>
proof (rule show_programCorrect_noTransactionInterleaving'')
  text \<open>Assume we have a trace and a final state S\<close>
  fix trace S
  text \<open>Such that executing the trace finishes in state S.\<close>
  assume steps: "initialState program ~~ trace \<leadsto>* S"

  text \<open>We can assume the trace is packed.\<close>
  assume packed: "packed_trace trace"

  text \<open>We may also assume that there are no failures\<close>
  assume noFail: "\<And>s. (s, ACrash) \<notin> set trace"

  assume "\<not>contextSwitchesInTransaction trace"

  assume noInvchecksInTxns: "no_invariant_checks_in_transaction trace"

  text \<open>We show that the trace must be correct (proof by contradiction).\<close>
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"

    text \<open>If the trace is incorrect, there must be a failing invariant check or assertion check in the trace:\<close>
    from this 
    have "\<exists>i<length trace. get_action (trace!i) \<in> {AInvcheck False, ALocal False}"
      by (metis (no_types, lifting) actionCorrect_def in_set_conv_nth insert_iff traceCorrect_def')

    text \<open>So there is an index, where an assertion fails or the invariant is violated. \<close>
    hence ex_fail:
      "\<exists>i<length trace. get_action (trace!i) = ALocal False 
      \<or> (\<exists>S_fail. (initialState program ~~ take i trace \<leadsto>* S_fail) \<and> \<not>invariant_all S_fail)  "
      by (smt eq_snd_iff id_take_nth_drop insertE singletonD steps steps_append steps_simp_AInvcheck)

    text "Let i be the smallest first position with a failure"
    from ex_least_nat_le''[OF ex_fail]
    obtain i 
      where i_bound: "i < length trace"
        and i_fail: "get_action (trace!i) = ALocal False \<or> 
              (\<exists>S_fail. (initialState program ~~ take i trace \<leadsto>* S_fail) \<and> \<not>invariant_all S_fail)"
        and i_smallest:
            "(\<forall>i'<i. \<not> (i' < length trace \<and>
                 (get_action (trace ! i') = ALocal False \<or>
                  (\<exists>S_fail. (initialState program ~~ take i' trace \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail))))"
      by blast

    from i_smallest 
    have i_smallest_assertionFail: "get_action (trace!i') \<noteq> ALocal False" if "i' < i" for i'
      using dual_order.strict_trans i_bound that by blast


    from i_fail
    show False
    proof (rule cases2_rev)
      assume "\<exists>S_fail. (initialState program ~~ take i trace \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"
      from this
      obtain S_fail_min 
        where "initialState program ~~ take i trace \<leadsto>* S_fail_min"
          and S_fail_min_fail: "\<not> invariant_all S_fail_min"
        by blast

      from i_smallest_assertionFail 
      have "get_action a \<noteq> ALocal False" if "a\<in>set (take i trace)" for a
        using that by (auto simp add: in_set_conv_nth)

      define tr'_min where "tr'_min \<equiv> take i trace"

      have S_fail_min_steps:"initialState program ~~ tr'_min \<leadsto>* S_fail_min"
        by (simp add: \<open>initialState program ~~ take i trace \<leadsto>* S_fail_min\<close> tr'_min_def)


      have tr'_min_prefix: "isPrefix tr'_min trace"
        by (metis append_take_drop_id isPrefix_appendI tr'_min_def)



      have S_fail_min_min: "\<And>tr' S_fail. \<lbrakk>isPrefix tr' trace; initialState program ~~ tr' \<leadsto>* S_fail; \<not> invariant_all S_fail; tr' \<noteq> tr'_min\<rbrakk> \<Longrightarrow> \<not>isPrefix tr' tr'_min"
        apply (auto simp add: tr'_min_def isPrefix_def)
        by (metis (no_types, lifting) i_bound i_smallest min.right_idem min.strict_coboundedI2 min.strict_order_iff)




    from \<open>initialState program ~~ tr'_min \<leadsto>* S_fail_min\<close>
    have "\<exists>tr'_s S_fail_s s'. 
              (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) 
            \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
    proof (rule convert_to_single_session_trace_invFail)
      show "state_wellFormed (initialState program)"
        by (simp add: state_wellFormed_init)
      show "packed_trace tr'_min"
        using \<open>isPrefix tr'_min trace\<close> packed prefixes_are_packed by blast
      show "\<And>s'. (s', ACrash) \<notin> set tr'_min"
        by (metis \<open>isPrefix tr'_min trace\<close> in_set_takeD isPrefix_def noFail)
      show "invariant_all (initialState program)"
        using inv_init .
      show "\<not> invariant_all S_fail_min"
        by (simp add: \<open>\<not> invariant_all S_fail_min\<close>)
      show "\<And>tx. txStatus (initialState program) tx \<noteq> Some Uncommitted"
        by (simp add: initialState_def)
      show " \<not>contextSwitchesInTransaction tr'_min"
        using \<open>\<not>contextSwitchesInTransaction trace\<close> prefixes_noContextSwitchesInTransaction tr'_min_prefix by blast
      show "\<And>a. a \<in> set tr'_min \<Longrightarrow> get_action a \<noteq> ALocal False"
        using \<open>\<And>a. a \<in> set (take i trace) \<Longrightarrow> get_action a \<noteq> ALocal False\<close> tr'_min_def by blast

    qed

    from this
    obtain tr'_s S_fail_s s'
      where "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        and "\<exists>a. (a, False) \<in> set tr'_s"
      by blast

    with works_in_single_session
    show False
      by (meson programCorrect_s_def traceCorrect_s_def works_in_single_session)
  next
    assume "get_action (trace ! i) = ALocal False"
    assume "\<nexists>S_fail. (initialState program ~~ take i trace \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"

    define tr'_min where "tr'_min \<equiv> take i trace"

    obtain S_fail where "initialState program ~~ tr'_min \<leadsto>* S_fail"
      by (metis append_take_drop_id steps steps_append tr'_min_def)

    have "isPrefix tr'_min trace"
      by (metis append_take_drop_id isPrefix_appendI tr'_min_def)

    define invoc where "invoc \<equiv> get_invoc (trace ! i)"

    have [simp]: "i < length trace"
      by (simp add: i_bound)
    hence [simp]: "i \<le> length trace"
      using less_or_eq_imp_le by auto

    have [simp]: "i > 0" \<comment> \<open>Since at the beginning of a trace we can only have invariant check or invocation.\<close>
    proof (rule ccontr)
      assume "\<not> 0 < i"
      hence "i = 0"
        by blast
      hence "trace = [trace ! i] @ tl trace"
        by (metis append_Cons append_Nil i_bound length_greater_0_conv list.collapse nth_Cons_0)

      with ` initialState program ~~ trace \<leadsto>* S`
      obtain S' where "initialState program ~~ [trace ! i] \<leadsto>* S'"
        by (metis steps_append)
      hence "initialState program ~~ trace ! i \<leadsto> S'"
        using steps_single by blast
      thus False using \<open>get_action (trace ! i) = ALocal False\<close>
        by (auto simp add: step.simps initialState_def)

    qed



    from packed
    have "get_invoc (last tr'_min) = invoc"
      apply (auto simp add: invoc_def tr'_min_def last_take)
      by (metis One_nat_def \<open>0 < i\<close> \<open>get_action (trace ! i) = ALocal False\<close> allowed_context_switch_simps(1) i_bound  use_packed_trace)



    from \<open>initialState program ~~ tr'_min \<leadsto>* S_fail\<close>
    have "\<exists>tr' S2.
       (initialState program ~~ (invoc, tr') \<leadsto>\<^sub>S* S2) \<and>
       (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S_fail S2 invoc (tr'_min = [] \<or> get_invoc (last tr'_min) = invoc)"
    proof (rule convert_to_single_session_trace)
      show "state_wellFormed (initialState program)"
        by (simp add: state_wellFormed_init)
      show "packed_trace tr'_min"

        using \<open>isPrefix tr'_min trace\<close> packed prefixes_are_packed by blast
      show "\<And>s'. (s', ACrash) \<notin> set tr'_min"
        by (metis \<open>isPrefix tr'_min trace\<close> in_set_takeD isPrefix_def noFail)
      show "\<And>tx. txStatus (initialState program) tx \<noteq> Some Uncommitted"
        by (simp add: initialState_def)
      show " \<not>contextSwitchesInTransaction tr'_min"
        using \<open>isPrefix tr'_min trace\<close> \<open>\<not>contextSwitchesInTransaction trace\<close> prefixes_noContextSwitchesInTransaction by blast
      show "\<And>a. a \<in> set tr'_min \<Longrightarrow> get_action a \<noteq> ALocal False"
        by (metis \<open>i \<le> length trace\<close> i_smallest_assertionFail in_set_conv_nth length_take min.absorb2 nth_take tr'_min_def)
      
      have "length tr'_min = i"
        by (simp add: tr'_min_def min.absorb2)

      show "\<lbrakk>isPrefix tr' tr'_min; initialState program ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'" for S' tr'
        using i_smallest[rule_format, where i'="length tr'"]
        apply auto
        apply (cases "length tr' < i", auto)
        using dual_order.strict_trans i_bound apply blast
        apply (smt \<open>isPrefix tr'_min trace\<close> \<open>length tr'_min = i\<close> dual_order.strict_trans i_bound isPrefix_def less_imp_le nth_take nth_take_lemma)
        by (metis \<open>\<nexists>S_fail. (initialState program ~~ take i trace \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail\<close> \<open>length tr'_min = i\<close> isPrefix_def not_le_imp_less take_all tr'_min_def)
    qed

    from this obtain tr'
      where single_steps: "initialState program ~~ (invoc, tr') \<leadsto>\<^sub>S* S_fail" and "\<forall>a. (a, False) \<notin> set tr'"
      by (auto simp add: `get_invoc (last tr'_min) = invoc` state_coupling_def)

    obtain S_fail' 
      where "S_fail ~~ trace ! i \<leadsto> S_fail'"
      by (metis \<open>initialState program ~~ tr'_min \<leadsto>* S_fail\<close> i_bound id_take_nth_drop steps steps_append2 steps_appendFront tr'_min_def)
    hence "S_fail ~~ (invoc, ALocal False) \<leadsto> S_fail'"
      by (metis \<open>get_action (trace ! i) = ALocal False\<close> invoc_def surjective_pairing)

    hence single_step: "S_fail ~~ (invoc, ALocal False, False) \<leadsto>\<^sub>S S_fail'"
      by (auto simp add: step_s.simps step.simps)

    with single_steps
    have single_steps2:  "initialState program ~~ (invoc, tr'@[(ALocal False, False)]) \<leadsto>\<^sub>S* S_fail'"
      using steps_s_step by blast

    thus False
      by (metis append_is_Nil_conv last_in_set last_snoc not_Cons_self2 programCorrect_s_def traceCorrect_s_def works_in_single_session)

  qed
qed  
qed


end
