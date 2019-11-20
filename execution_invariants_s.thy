theory execution_invariants_s
  imports repliss_sem_single_invocation execution_invariants
begin

section \<open>Invariants of single-invocId executions.\<close>

text \<open>This theory includes proof for invariants that hold for all single-invocId executions.\<close>





definition initialStates :: "('proc::valueType, 'ls, 'operation, 'any::valueType) prog \<Rightarrow> invocId \<Rightarrow> ('proc, 'ls, 'operation, 'any) state set"   where
  "initialStates progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocationOp := (invocationOp S)(i \<mapsto> proc)\<rparr>) 
 | S proc initState impl.
    prog S = progr
  \<and> procedure progr proc = (initState, impl)  
  \<and> uniqueIds proc \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> state_wellFormed S \<comment> \<open>   TODO add wellformed?  \<close>
  \<and> invocationOp S i = None
  \<and> (\<forall>tx. transactionStatus S tx \<noteq> Some Uncommitted)
  \<and> (\<forall>tx. transactionOrigin S tx \<noteq> Some i)
}"


lemma initialStates_wellFormed:
"state_wellFormed S" if "S \<in> initialStates progr i"
  using that proof (auto simp add: initialStates_def)
  fix Sa proc initState impl
  assume S_def: "S = Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),
                 invocationOp := invocationOp Sa(i \<mapsto> proc)\<rparr>"
    and "progr = prog Sa"
    and "procedure (prog Sa) proc = (initState, impl)"
    and "uniqueIds proc \<subseteq> knownIds Sa"
    and "invariant_all Sa"
    and "state_wellFormed Sa"
    and "invocationOp Sa i = None"
    and "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"

  have step: "Sa ~~ (i, AInvoc proc) \<leadsto> S"
    apply (auto simp add: step.simps S_def)
    by (metis \<open>invocationOp Sa i = None\<close> \<open>procedure (prog Sa) proc = (initState, impl)\<close> \<open>state_wellFormed Sa\<close> \<open>uniqueIds proc \<subseteq> knownIds Sa\<close> state.surjective state.unfold_congs(12) state.update_convs(1) wf_localState_to_invocationOp)

  with \<open>state_wellFormed Sa\<close>
  have "state_wellFormed S"
    using state_wellFormed_combine_step by fastforce

  then show " state_wellFormed
            (Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),
                  invocationOp := invocationOp Sa(i \<mapsto> proc)\<rparr>)"
    using S_def by simp
qed

definition state_wellFormed_s where
  "state_wellFormed_s S i \<equiv> \<exists>prog tr. initialState prog ~~ (i,tr) \<leadsto>\<^sub>S* S"


lemma initialStates_reachable_from_initialState:
  assumes "init\<in>initialStates progr i"
  shows "\<exists>p invr. initialState progr ~~ (i, AInvoc p, invr) \<leadsto>\<^sub>S init" 
  using assms apply (auto simp add: initialStates_def step_s.simps )
   apply (auto simp add: initialState_def)
  by blast


lemma initialStates_wf:
  assumes "init\<in>initialStates progr i"
    and "init ~~ (i,tr) \<leadsto>\<^sub>S* S"
  shows "state_wellFormed_s S i"
  using assms initialStates_reachable_from_initialState state_wellFormed_s_def steps_s_append steps_s_single by blast


(*
definition state_wellFormed_s where
"state_wellFormed_s S i \<equiv> \<exists>prog init tr. init\<in>initialStates prog i \<and> init ~~ (i,tr) \<leadsto>\<^sub>S* S"
*)


lemma state_wellFormed_s_induct[consumes 1, case_names initial step[IH steps step]]:
  assumes wf: "state_wellFormed_s S i"
    and initial_P: "\<And>progr. P (initialState progr)"
    and step_P: "\<And>tr S a S' progr. \<lbrakk>P S; initialState progr ~~ (i,tr) \<leadsto>\<^sub>S* S;  S ~~ (i, a) \<leadsto>\<^sub>S S'\<rbrakk> \<Longrightarrow> P S'"
  shows "P S"
proof -
  from wf
  obtain prog tr where  steps: "initialState prog ~~ (i, tr) \<leadsto>\<^sub>S* S"
    by (auto simp add: state_wellFormed_s_def)

  from steps 
  show "P S"
  proof (induct rule: step_s_induct)
    case initial
    then show ?case
      using initial_P by blast 
  next
    case (step tr S a S')
    then show ?case
      using step_P by blast
  qed      
qed

lemma state_wellFormed_s_to_wf: 
  "state_wellFormed_s S i \<Longrightarrow> state_wellFormed S"
proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  then show ?case
    by (simp add: state_wellFormed_init)
next
  case (step tr S a S' progr)
  from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close>
  show ?case 
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    then have "S ~~ (i, ALocal) \<leadsto> S'"
      by (auto simp add: step_simps)
    then show ?case
      using state_wellFormed_combine_step step.IH by fastforce 
  next
    case (newId C s ls f ls' uidv uid)
    then have "S ~~ (i, ANewId uid) \<leadsto> S'"
      by (auto simp add: step_simps)
    then show ?case
      using state_wellFormed_combine_step step.IH by fastforce 
  next
    case (beginAtomic C s ls f ls' t C' C'' vis vis')
    then show ?case
      by blast 
  next
    case (endAtomic C s ls f ls' t C' valid)
        then have "S ~~ (i, AEndAtomic) \<leadsto> S'"
      by (auto simp add: step_simps)
    then show ?case
      using state_wellFormed_combine_step step.IH by fastforce 
  next
    case (dbop C s ls f Op ls' t c res vis)
    then have "S ~~ (i, ADbOp c Op res) \<leadsto> S'"
      by (auto simp add: step_simps)
    then show ?case
      using state_wellFormed_combine_step step.IH by fastforce 
  next
    case (invocation C s procName initState impl C' C'' valid)
    then have "C' ~~ (i, AInvoc procName) \<leadsto> S'"
      apply (auto simp add: step_simps)
      using wf_localState_to_invocationOp by blast+

    then show ?case
      using \<open>state_wellFormed C'\<close> state_wellFormed_combine_step by fastforce 
  next
    case (return C s ls f res C' valid)
    then have "S ~~ (i, AReturn res) \<leadsto> S'"
      by (auto simp add: step_simps)
    then show ?case
      using state_wellFormed_combine_step step.IH by fastforce 
  qed
qed

(*TODO could use lemma state_wellFormed_s_to_wf above to simplify lemmas below*)

lemma wf_s_localState_to_invocationOp:
  "\<lbrakk>state_wellFormed_s S i; localState S i \<noteq> None\<rbrakk> \<Longrightarrow> invocationOp S i \<noteq> None"
proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  then show ?case by (auto simp add: initialStates_def wf_localState_to_invocationOp state_wellFormed_init )

next
  case (step tr S a S' progr)
  then show ?case 
    by (auto simp add: step_s.simps wf_localState_to_invocationOp dest!: wf_localState_to_invocationOp)
qed

lemma wf_s_localState_to_invocationOp2:
  "\<lbrakk>state_wellFormed_s S i; localState S i \<triangleq> x\<rbrakk> \<Longrightarrow> \<exists>p. invocationOp S i \<triangleq> p"
  using wf_s_localState_to_invocationOp by fastforce

lemma wellFormed_s_invoc_notStarted1:
  assumes "state_wellFormed_s S i"
    and "invocationOp S i = None"
  shows "currentTransaction S i = None"      
  using assms proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  then show ?case by (auto simp add: initialState_def)
next
  case (step tr S a S' progr)
  then show ?case 
    by (auto simp add: step_s.simps wf_localState_to_invocationOp)
qed


lemma wellFormed_s_invoc_notStarted2:
  assumes "state_wellFormed_s S i"
    and "invocationOp S i = None"
  shows  "localState S i = None"
  using assms proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  then show ?case by (auto simp add: initialState_def)
next
  case (step tr S a S' progr)
  then show ?case 
    by (auto simp add: step_s.simps wf_localState_to_invocationOp)
qed


lemma unchangedProg:
  assumes steps: "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
  shows "prog S' = prog S"
  using assms proof (induct rule: step_s_induct)
  case initial
  then show ?case by simp
next
  case (step tr S a S')
  then show ?case by (auto simp add: step_s.simps)
qed

lemma state_wellFormed_s_currentTransactionsOnlyInCurrent:
  assumes wf: "state_wellFormed_s S i" 
    and other: "i' \<noteq> i"
  shows "currentTransaction S i' = None"
  using assms proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  show ?case 
    by (auto simp add: initialState_def)
next
  case (step tr S a S' progr)
  then show ?case 
    apply (auto simp add: step_s.simps)
     apply (metis not_None_eq wellFormed_currentTransaction_unique wellFormed_currentTransaction_unique_h(2))
    by (meson option.exhaust wellFormed_currentTransaction_unique_h(2))
qed

lemma state_wellFormed_s_currentTransactions_iff_uncommitted:
  assumes wf: "state_wellFormed_s S i" 
  shows "currentTransaction S i \<triangleq> tx \<longleftrightarrow> (transactionStatus S tx \<triangleq> Uncommitted)"
  using local.wf state_wellFormed_s_currentTransactionsOnlyInCurrent state_wellFormed_s_to_wf wellFormed_currentTransactionUncommitted wellFormed_currentTransaction_back3 by fastforce




end