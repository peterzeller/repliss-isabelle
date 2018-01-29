theory execution_invariants
  imports repliss_sem
begin

section {* Execution Invariants *}

text {* This theory includes proof for invariants that hold for all executions. *}


definition state_wellFormed :: "('localState, 'any) state \<Rightarrow> bool" where
  "state_wellFormed state \<equiv> \<exists>tr. (\<forall>i. (i, AFail) \<notin> set tr) \<and>  initialState (prog state) ~~ tr \<leadsto>* state"

lemma state_wellFormed_init[simp]:
  "state_wellFormed (initialState program)"
  unfolding state_wellFormed_def by (rule exI[where x="[]"], auto simp add: initialState_def)

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

lemma state_wellFormed_combine_step:
  assumes wf: "state_wellFormed S"
    and step: "S ~~ a \<leadsto> S'"
    and noFails: "snd a \<noteq> AFail"
  shows "state_wellFormed S'"
  using wf step noFails  apply (auto simp add: state_wellFormed_def)
  apply (rule_tac x="tr@[a]" in exI)
  apply auto
  by (metis steps_do_not_change_prog steps_step)


lemma state_wellFormed_combine:
  assumes wf: "state_wellFormed S"
    and steps: "S ~~ tr \<leadsto>* S'"
    and noFails: "\<And>i. (i, AFail) \<notin> set tr"
  shows "state_wellFormed S'"
proof -
  from steps 
  have "prog S' = prog S"
    using steps_do_not_change_prog by auto

  from wf obtain tr1 where "initialState (prog S) ~~ tr1 \<leadsto>* S" and "(\<forall>i. (i, AFail) \<notin> set tr1)"
    using state_wellFormed_def by blast 
  with steps
  have "initialState (prog S) ~~ tr1@tr \<leadsto>* S'"
    using steps_append by blast
  with `prog S' = prog S`
  have "initialState (prog S') ~~ tr1@tr \<leadsto>* S'" by simp
  moreover have "(\<forall>i. (i, AFail) \<notin> set (tr1@tr))"
    by (simp add: \<open>\<forall>i. (i, AFail) \<notin> set tr1\<close> noFails)
  ultimately show "state_wellFormed S'"
    using state_wellFormed_def by blast
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
  assumes wf: "state_wellFormed s"
    and P_initial: "P (initialState (prog s))"
    and P_step: "\<And>t a s. \<lbrakk>state_wellFormed t; P t; t ~~ a \<leadsto> s; snd a \<noteq> AFail\<rbrakk> \<Longrightarrow> P s"
  shows "P s"
  using wf proof (auto simp add: state_wellFormed_def)
  fix tr 
  assume noFail: "\<forall>i. (i, AFail) \<notin> set tr"
  and steps: "initialState (prog s) ~~ tr \<leadsto>* s"

  from steps noFail
  show "P s"
  proof (induct rule: steps_induct)
    case initial
    then show ?case
      using P_initial by auto 
  next
    case (step S' tr a S'')
    show ?case 
    proof (rule P_step)
      show "S' ~~ a \<leadsto> S''" using `S' ~~ a \<leadsto> S''` .
      show "state_wellFormed S'"
        by (metis butlast_snoc in_set_butlastD state_wellFormed_combine state_wellFormed_init step.prems step.steps) 
      show "P S'"
        using step.IH step.prems by auto 
      show "snd a \<noteq> AFail"
        by (metis append_is_Nil_conv last_in_set last_snoc list.distinct(1) step.prems surjective_pairing)
    qed
  qed
qed



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


lemma wellFormed_callOrigin_dom3:
  assumes a1: "state_wellFormed S"
  shows "(calls S c = None) \<longleftrightarrow> (callOrigin S c = None)"
  using assms wellFormed_callOrigin_dom by force

lemma range_empty[simp]: "range Map.empty = {None}"
  by auto



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



lemma wellFormed_currentTransaction_back:
  assumes steps: "steps  S_init tr S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted: "\<And>tx. transactionStatus S_init tx \<noteq> Some Uncommited"
    and wf: "state_wellFormed S_init"
  shows "transactionStatus S t \<triangleq> Uncommited \<longrightarrow> (\<exists>!i. currentTransaction S i \<triangleq> t)"
  using steps noFail proof (induct  rule: steps_induct)
  case initial
  then show ?case by (simp add: initialState_def noUncommitted)
next
  case (step S' tr a S'')
  then show ?case 
  proof clarsimp
    assume a0: "S_init ~~ tr \<leadsto>* S'"
      and a1: "transactionStatus S' t \<triangleq> Uncommited \<longrightarrow> (\<exists>!i. currentTransaction S' i \<triangleq> t)"
      and a2: "S' ~~ a \<leadsto> S''"
      and a3: "transactionStatus S'' t \<triangleq> Uncommited"

    have "state_wellFormed S'"
      using state_wellFormed_combine state_wellFormed_init step.steps local.wf step.prems by fastforce 

    have "state_wellFormed S''"
      using state_wellFormed_combine state_wellFormed_init step.step step.steps steps_step local.wf step.prems by blast

    from a2
    show "\<exists>!i. currentTransaction S'' i \<triangleq> t"
    proof (cases rule: step.cases)
      case (local ls f ls')
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (newId ls f ls' uid)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (beginAtomic ls f ls' t vis newTxns newCalls snapshot)
      then show ?thesis using a0 a1 a3 \<open>state_wellFormed S'\<close> apply (auto split: if_splits )
        by (metis option.simps(3))

    next
      case (endAtomic ls f ls' t)
      then show ?thesis using a1 a3 a0 apply (auto split: if_splits)
        by force

    next
      case (dbop ls f Op args ls' t c res vis)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (invocation procName args initialState impl)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (return ls f res)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (fail ls)
      then show ?thesis
        using step.prems by force 
    next
      case (invCheck txns res)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    qed
  qed
qed


lemma wellFormed_currentTransaction_back2:
  assumes steps: "steps  (initialState progr) tr S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
  shows "transactionStatus S t \<triangleq> Uncommited \<longrightarrow> (\<exists>!i. currentTransaction S i \<triangleq> t)"
  using steps noFail  apply (rule wellFormed_currentTransaction_back)
   apply (simp add: initialState_def)
  apply simp
done

lemma wellFormed_currentTransaction_back3:
  assumes wf: "state_wellFormed S"
    and uncommitted: "transactionStatus S t \<triangleq> Uncommited"
  shows "\<exists>!i. currentTransaction S i \<triangleq> t"
  using local.wf state_wellFormed_def uncommitted wellFormed_currentTransaction_back2 by blast



lemma commitedCalls_unchanged_callOrigin[simp]:
  assumes a1: "ts t \<triangleq> Uncommited"
    and a2: "co c = None"
  shows "commitedCallsH (co(c \<mapsto> t)) ts = commitedCallsH co ts"
  using a1 a2 by (auto simp add: commitedCallsH_def isCommittedH_def)

lemma callOrigin_same_committed: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Commited "
  shows "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx"     
  using exec apply (rule step.cases)
  using wellFormed committed by auto  


lemma wf_localState_to_invocationOp:
  "\<lbrakk>state_wellFormed S; localState S i \<noteq> None\<rbrakk> \<Longrightarrow> invocationOp S i \<noteq> None"    
proof (induct  rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case 
    by (auto simp add: step.simps split: if_splits)
qed

lemma wellFormed_invoc_notStarted:
  assumes "state_wellFormed S"
    and "invocationOp S s = None"
  shows "currentTransaction S s = None"  
    and "localState S s = None"
  using assms apply (induct rule: wellFormed_induct)
     apply (auto simp add: initialState_def)
   apply (erule step.cases)
           apply (auto split: if_splits)
  apply (erule step.cases)
          apply (auto split: if_splits)
  done

lemma steps_do_not_change_invocationOp:
  assumes steps:"S ~~ tr \<leadsto>* S'"
    and "invocationOp S i \<triangleq> x"
  shows "invocationOp S' i \<triangleq> x"
  using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')
  then show ?case by (auto simp add: step.simps)
qed

lemma wf_no_transactionStatus_origin_for_nothing:
  assumes wf: "state_wellFormed S"
    and txStatusNone: "transactionStatus S txId = None"
  shows "callOrigin S c \<noteq> Some txId"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps split: if_splits)
qed

lemma wf_callOrigin_implies_transactionStatus_defined:
  assumes wf: "state_wellFormed S"
    and co:  "callOrigin S c = Some txId"
  shows "transactionStatus S txId \<noteq> None" 
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps split: if_splits)
qed

lemma finite_dom_spit:
  assumes "finite (dom A \<inter> {x. P x})" and "finite (dom B \<inter> {x. \<not>P x})"
  shows "finite (dom (\<lambda>x. if P x then A x else B x))"
  apply (rule_tac B="(dom A \<inter> {x. P x}) \<union> (dom B \<inter> {x. \<not>P x})" in finite_subset)
  using assms by (auto split: if_splits)


lemma wf_finite_calls:
  assumes wf: "state_wellFormed S"
  shows "finite (dom (calls S))" 
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps intro!: finite_dom_spit split: if_splits)
qed


lemma inTransaction_trace:
  assumes  steps: "S ~~ trace \<leadsto>* S'"
and beginPos: "trace ! beginPos = (invoc, ABeginAtomic tx txns)"
and beginPosBound: "beginPos < length trace"
and noEnd: "\<And>k. \<lbrakk>k < length trace; beginPos < k\<rbrakk> \<Longrightarrow> trace ! k \<noteq> (invoc, AEndAtomic)"

and noFail: "\<And>i. (i, AFail)\<notin>set trace"
shows "currentTransaction S' invoc \<noteq> None"
  using steps beginPos beginPosBound noEnd noFail proof (induct rule: steps_induct)
case initial
then show ?case by auto
next
  case (step S' tr a S'')
  {
    assume a1:"beginPos < length tr"
    from a1 have a2: "tr ! beginPos = (invoc, ABeginAtomic tx txns)"
      by (metis nth_append step.prems(1)) 


    from a1 
    have a3: "\<And>k. \<lbrakk>k < length tr; beginPos < k\<rbrakk> \<Longrightarrow> tr ! k \<noteq> (invoc, AEndAtomic)"
      by (metis butlast_snoc length_append_singleton lessI less_imp_le less_le_trans nth_butlast step.prems(3))

    from a1 a2 a3 
    have IH: "currentTransaction S' invoc \<noteq> None"
      using step.IH step.prems(4) by auto 

    from this obtain y where [simp]: "currentTransaction S' invoc \<triangleq> y"
      by blast


    from step.prems(3)[where k="length tr"] 
    have [simp]: "a \<noteq> (invoc, AEndAtomic)"
      by (auto simp add: a1)


    with `S' ~~ a \<leadsto> S''`
    have ?case 
      apply (auto simp add: step.simps)
      using step.prems(4) by force
  }
  moreover
  {
    assume "beginPos = length tr"
    hence "a = (invoc, ABeginAtomic tx txns)"
      using step.prems(1) by auto

    with `S' ~~ a \<leadsto> S''`
    have ?case 
      by (auto simp add: step.simps)
  }
  ultimately show ?case
    using less_SucE step.prems(2) by auto
qed


end