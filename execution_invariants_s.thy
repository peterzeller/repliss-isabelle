section \<open>Invariants of single-invocId executions.\<close>
theory execution_invariants_s
  imports repliss_sem_single_invocation execution_invariants
begin


text \<open>This theory includes proof for invariants that hold for all single-invocId executions.\<close>


lemma state_wellFormed_s_steps:
  assumes wf: "state_wellFormed S"
    and steps: "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
  shows "state_wellFormed S'"
  using steps 
proof (induct rule: step_s_induct)
  case initial
  then show ?case 
    using wf by simp
next
  case (step tr S' a S'')

  from ` state_wellFormed S'`
  have step_wf: "state_wellFormed S''" if "S' ~~ (i, fst a) \<leadsto> S''"
    using that
  proof (rule state_wellFormed_combine_step)
    show "get_action (i, fst a) \<noteq> ACrash"
      by (metis prod.collapse sndI step.hyps step_s_no_Fail)
  qed

  from `S' ~~ (i, a) \<leadsto>\<^sub>S S''`
  show ?case
  proof cases
    case (local ls f ok ls')
    show ?thesis
      by (rule step_wf, auto simp add: local step.simps)
  next
    case (newId ls f ls' uid uidv ls'')
    show ?thesis
    proof (rule step_wf)
      show "S' ~~ (i, fst a) \<leadsto> S''"
        using newId by (auto simp add:  step.simps)
    qed
  next
    case (beginAtomic ls f ls' t S' vis vis')
    thus ?thesis by simp
  next
    case (endAtomic ls f ls' t valid)
    show ?thesis
      by (rule step_wf, auto simp add: endAtomic step.simps)
  next
    case (dbop ls f Op ls' t c res vis)
    show ?thesis
    proof (rule step_wf)
      show "S' ~~ (i, fst a) \<leadsto> S''"
        using dbop by (auto simp add:  step.simps)
    qed
  next
    case (invocation proc initState impl Sx valid)
    have "Sx ~~ (i, AInvoc proc) \<leadsto> S''"
      using invocation apply (auto simp add: step.simps)
      using wf_localState_to_invocOp apply blast
      using wf_localState_needs_invocOp by blast


    thus ?thesis
      using `state_wellFormed Sx` state_wellFormed_combine_step by fastforce
  next
    case (return ls f res valid)
    show ?thesis
      by (rule step_wf, auto simp add: return step.simps)
  qed
qed


definition initialStates :: "('proc::valueType, 'ls, 'op, 'any::valueType) prog \<Rightarrow> invocId \<Rightarrow> ('proc, 'ls, 'op, 'any) state set"   where
  "initialStates progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocOp := (invocOp S)(i \<mapsto> proc)\<rparr>) 
 | S proc initState impl.
    prog S = progr
  \<and> procedure progr proc = (initState, impl)  
  \<and> uniqueIds proc \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> state_wellFormed S 
  \<and> invocOp S i = None
  \<and> (\<forall>tx. txStatus S tx \<noteq> Some Uncommitted)
  \<and> (\<forall>tx. txOrigin S tx \<noteq> Some i)
}"


lemma initialStates_wellFormed:
"state_wellFormed S" if "S \<in> initialStates progr i"
  using that proof (auto simp add: initialStates_def)
  fix Sa proc initState impl
  assume S_def: "S = Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),
                 invocOp := invocOp Sa(i \<mapsto> proc)\<rparr>"
    and "progr = prog Sa"
    and "procedure (prog Sa) proc = (initState, impl)"
    and "uniqueIds proc \<subseteq> knownIds Sa"
    and "invariant_all Sa"
    and "state_wellFormed Sa"
    and "invocOp Sa i = None"
    and "\<forall>tx. txStatus Sa tx \<noteq> Some Uncommitted"

  have step: "Sa ~~ (i, AInvoc proc) \<leadsto> S"
    apply (auto simp add: step.simps S_def)
    by (metis \<open>invocOp Sa i = None\<close> \<open>procedure (prog Sa) proc = (initState, impl)\<close> \<open>state_wellFormed Sa\<close> \<open>uniqueIds proc \<subseteq> knownIds Sa\<close> state.surjective state.unfold_congs(12) state.update_convs(1) wf_localState_to_invocOp)

  with \<open>state_wellFormed Sa\<close>
  have "state_wellFormed S"
    using state_wellFormed_combine_step by fastforce

  then show " state_wellFormed
            (Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),
                  invocOp := invocOp Sa(i \<mapsto> proc)\<rparr>)"
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

lemma state_wellFormed_s_to_wf:
  assumes "state_wellFormed_s S i"
  shows "state_wellFormed S"
  using assms state_wellFormed_init state_wellFormed_s_def state_wellFormed_s_steps by blast


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



lemma wf_s_localState_to_invocOp:
  "\<lbrakk>state_wellFormed_s S i; localState S i \<noteq> None\<rbrakk> \<Longrightarrow> invocOp S i \<noteq> None"
  by (meson state_wellFormed_s_to_wf wellFormed_invoc_notStarted(2))

lemma wf_s_localState_to_invocOp2:
  "\<lbrakk>state_wellFormed_s S i; localState S i \<triangleq> x\<rbrakk> \<Longrightarrow> \<exists>p. invocOp S i \<triangleq> p"
  using wf_s_localState_to_invocOp by fastforce

lemma wellFormed_s_invoc_notStarted1:
  assumes "state_wellFormed_s S i"
    and "invocOp S i = None"
  shows "currentTx S i = None"
  using assms state_wellFormed_s_to_wf wellFormed_invoc_notStarted(1) by auto     


lemma wellFormed_s_invoc_notStarted2:
  assumes "state_wellFormed_s S i"
    and "invocOp S i = None"
  shows  "localState S i = None"
  using assms wf_s_localState_to_invocOp by blast


lemma unchangedProg1:
  assumes steps: "S ~~ (i, tr) \<leadsto>\<^sub>S S'"
  shows "prog S' = prog S"
  using assms by (auto simp add: step_s.simps)

lemma unchangedProg:
  assumes steps: "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
  shows "prog S' = prog S"
  using assms by (induct rule: step_s_induct) (auto simp add: unchangedProg1)

lemma state_wellFormed_s_currentTxsOnlyInCurrent:
  assumes wf: "state_wellFormed_s S i" 
    and other: "i' \<noteq> i"
  shows "currentTx S i' = None"
  using assms proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  show ?case 
    by (auto simp add: initialState_def)
next
  case (step tr S a S' progr)
  then show ?case 
    apply (auto simp add: step_s.simps)
     apply (metis not_None_eq wellFormed_currentTx_unique wellFormed_currentTx_unique_h(2))
    by (meson option.exhaust wellFormed_currentTx_unique_h(2))
qed

lemma state_wellFormed_s_currentTxs_iff_uncommitted:
  assumes wf: "state_wellFormed_s S i" 
  shows "currentTx S i \<triangleq> tx \<longleftrightarrow> (txStatus S tx \<triangleq> Uncommitted)"
  using local.wf state_wellFormed_s_currentTxsOnlyInCurrent state_wellFormed_s_to_wf wellFormed_currentTxUncommitted wellFormed_currentTx_back3 by fastforce






end