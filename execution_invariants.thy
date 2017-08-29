theory execution_invariants
  imports replissSem1
begin


definition state_wellFormed :: "('localState, 'any) state \<Rightarrow> bool" where
"state_wellFormed state \<equiv> \<exists>tr. initialState (prog state) ~~ tr \<leadsto>* state"

lemma state_wellFormed_init[simp]:
"state_wellFormed (initialState program)"
  by (metis distributed_state.select_convs(1) initialState_def state_wellFormed_def steps_refl)

lemma steps_do_not_change_prog: 
assumes "S ~~ tr \<leadsto>* S'"
shows "prog S' = prog S"
using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')
  hence [simp]: "prog S' = prog S" by simp
  from `S' ~~ a \<leadsto> S''`
  show ?case 
    apply (rule step.cases)
    apply auto
    done
qed
  
lemma state_wellFormed_combine:
assumes wf: "state_wellFormed S"
and steps: "S ~~ tr \<leadsto>* S'"
shows "state_wellFormed S'"
proof -
  from steps 
  have "prog S' = prog S"
    using steps_do_not_change_prog by auto

 from wf obtain tr1 where "initialState (prog S) ~~ tr1 \<leadsto>* S"
   using state_wellFormed_def by blast 
 with steps
 have "initialState (prog S) ~~ tr1@tr \<leadsto>* S'"
   using steps_append by blast
 with `prog S' = prog S`
 have "initialState (prog S') ~~ tr1@tr \<leadsto>* S'" by simp
 thus "state_wellFormed S'"
  using state_wellFormed_def by auto 
qed  

lemma step_prog_invariant:
"S ~~ tr \<leadsto>* S' \<Longrightarrow> prog S' = prog S"
apply (induct rule: steps.induct)
apply auto
apply (erule step.cases)
apply auto
done

thm full_nat_induct


lemma steps_induct[consumes 1, case_names initial step[steps IH step]]:
assumes a1: "init ~~ tr \<leadsto>*  S"
    and a2: "P [] init"
    and a3: "\<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''"
shows "P tr S"
proof -
  have h: "\<lbrakk>S ~~ tr \<leadsto>* s; P [] init; S = init; 
      \<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''\<rbrakk> \<Longrightarrow> P tr s" for S tr s
    proof (induct rule: steps.induct)
      case (steps_refl S)                        
      then show ?case by simp
    next
      case (steps_step S tr S' a S'')
      have "P tr S'"
        apply (rule steps_step(2))
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(1) steps_step.prems(2) apply auto[1]
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(2) apply auto[1]
        by (simp add: steps_step.prems(3))
      show ?case
      proof (rule a3)
        show "init ~~ tr \<leadsto>* S'"
          using steps_step.hyps(1) steps_step.prems(2) by auto
        show "P tr S'" using `P tr S'` .
        show "S' ~~ a \<leadsto> S''"
          by (simp add: steps_step.hyps(3)) 
      qed
    qed
  show ?thesis
  using a1 a2
  proof (rule h)
    show "init = init" ..
    show "\<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>* S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr @ [a]) S''"
      using a3 by auto
  qed  
qed


lemma steps_induct2[consumes 1, case_names initial step[steps IH step]]:
assumes a1: "initialState progr ~~ tr \<leadsto>*  S"
    and a2: "P [] (initialState progr)"
    and a3: "\<And>S' tr a S''. \<lbrakk>initialState progr ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''"
shows "P tr S"
  using a1 a2 a3 steps_induct by blast


lemma wellFormed_induct[consumes 1, case_names initial step]:
"\<lbrakk>state_wellFormed s; P (initialState (prog s)); \<And>t a s. \<lbrakk>state_wellFormed t; P t; t ~~ a \<leadsto> s\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P s"
apply (auto simp add: state_wellFormed_def)
apply (erule(1) steps_induct)
by (metis prod.collapse state_wellFormed_def state_wellFormed_init step_prog_invariant steps_append)



lemma wellFormed_callOrigin_dom:
assumes a1: "state_wellFormed S"
shows "dom (callOrigin S) = dom (calls S)"
using a1 apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  by blast

lemma wellFormed_callOrigin_dom2[simp]: 
"\<lbrakk>calls S c = None; state_wellFormed S\<rbrakk> \<Longrightarrow>  callOrigin S c = None"
  using wellFormed_callOrigin_dom by force


lemma wellFormed_visibleCallsSubsetCalls_h:
assumes a1: "state_wellFormed S"
shows "happensBefore S \<subseteq> dom (calls S) \<times> dom (calls S)"
   and "\<And>vis s. visibleCalls S s \<triangleq> vis \<Longrightarrow> state_wellFormed S \<Longrightarrow> vis \<subseteq> dom (calls S)" 
using a1 apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  apply blast
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  apply blast
  apply blast
  apply (auto simp add: callsInTransactionH_contains downwardsClosure_in split: option.splits)[1]
  apply (metis not_None_eq wellFormed_callOrigin_dom2)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
done  
  

    
lemma wellFormed_visibleCallsSubsetCalls:
assumes a1: "state_wellFormed A"
    and a2: "visibleCalls A s \<triangleq> vis"
shows "vis \<subseteq> dom (calls A)"
  using a1 a2 wellFormed_visibleCallsSubsetCalls_h(2) by blast

lemma wellFormed_currentTransaction_unique_h:
assumes a1: "state_wellFormed S"
shows "\<forall>sa sb t. currentTransaction S sa \<triangleq> t \<longrightarrow> currentTransaction S sb \<triangleq> t \<longrightarrow>  sa = sb"
  and "\<forall>sa t. currentTransaction S sa \<triangleq> t \<longrightarrow> transactionStatus S t \<triangleq> Uncommited"
using a1 apply (induct  rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
apply (erule step.cases)
apply (auto split: if_splits)
done   
  
lemmas wellFormed_currentTransaction_unique = wellFormed_currentTransaction_unique_h(1)[rule_format]
lemmas wellFormed_currentTransactionUncommited[simp] = wellFormed_currentTransaction_unique_h(2)[rule_format]
    

lemma commitedCalls_unchanged_callOrigin[simp]:
assumes a1: "ts t \<triangleq> Uncommited"
    and a2: "co c = None"
shows "commitedCallsH (co(c \<mapsto> t)) ts = commitedCallsH co ts"
using a1 a2 by (auto simp add: commitedCallsH_def)

lemma callOrigin_same_committed: 
assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Commited "
shows "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx"     
    using exec apply (rule step.cases)
    using wellFormed committed by auto  


end