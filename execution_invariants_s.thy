theory execution_invariants_s
imports replissSem_singleSession execution_invariants
begin


definition initialStates :: "('localState, 'any) prog \<Rightarrow> invocation \<Rightarrow> ('localState, 'any) state set"  where
"initialStates progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocationOp := (invocationOp S)(i \<mapsto> (procName, args))\<rparr>) 
 | S procName args initState impl.
    prog S = progr
  \<and> procedure progr procName args \<triangleq> (initState, impl)  
  \<and> uniqueIdsInList args \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> state_wellFormed S (*  TODO add wellformed? *)
  \<and> invocationOp S i = None
}"


definition state_wellFormed_s where
"state_wellFormed_s S i \<equiv> \<exists>prog tr. initialState prog ~~ (i,tr) \<leadsto>\<^sub>S* S"


lemma initialStates_reachable_from_initialState:
assumes "init\<in>initialStates progr i"
shows "\<exists>p args invr. initialState progr ~~ (i, AInvoc p args, invr) \<leadsto>\<^sub>S init" 
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
    thus ?case
      using step_P by blast
  qed      
qed
  

lemma wf_s_localState_to_invocationOp:
"\<lbrakk>state_wellFormed_s S i; localState S i \<noteq> None\<rbrakk> \<Longrightarrow> invocationOp S i \<noteq> None"
proof (induct rule: state_wellFormed_s_induct)
  case (initial progr)
  then show ?case by (auto simp add: initialStates_def wf_localState_to_invocationOp)
next
  case (step tr S a S' progr)
  then show ?case 
    by (auto simp add: step_s.simps wf_localState_to_invocationOp dest!: wf_localState_to_invocationOp)
qed

lemma wf_s_localState_to_invocationOp2:
"\<lbrakk>state_wellFormed_s S i; localState S i \<triangleq> x\<rbrakk> \<Longrightarrow> \<exists>x y. invocationOp S i \<triangleq> (x,y)"
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



end