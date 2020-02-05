section \<open>Execution Invariants\<close>

theory execution_invariants
  imports repliss_sem utils prefix
begin


text \<open>This theory includes proofs for invariants that hold for all executions.\<close>


definition state_wellFormed :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> bool" where
  "state_wellFormed state \<equiv> \<exists>tr. (\<forall>i. (i, ACrash) \<notin> set tr) \<and>  initialState (prog state) ~~ tr \<leadsto>* state"

lemma state_wellFormed_init:
  "state_wellFormed (initialState program)"
  unfolding state_wellFormed_def by (rule exI[where x="[]"], auto simp add: initialState_def  steps_empty)
  

lemma steps_do_not_change_prog: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "prog S' = prog S"
  using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')
  then have [simp]: "prog S' = prog S" by simp
  from \<open>S' ~~ a \<leadsto> S''\<close>
  show ?case 
    by (rule step.cases, auto)
qed

lemma state_wellFormed_combine_step:
  assumes wf: "state_wellFormed S"
    and step: "S ~~ a \<leadsto> S'"
    and noFails: "get_action a \<noteq> ACrash"
  shows "state_wellFormed S'"
  using wf step noFails  proof (auto simp add: state_wellFormed_def)

  show "\<exists>tr. (\<forall>i. (i, ACrash) \<notin> set tr) \<and> initialState (prog S') ~~ tr \<leadsto>* S'"
    if c0: "S ~~ a \<leadsto> S'"
      and c1: "get_action a \<noteq> ACrash"
      and c2: "\<forall>i. (i, ACrash) \<notin> set tr"
      and c3: "initialState (prog S) ~~ tr \<leadsto>* S"
    for  tr
  proof (rule exI[where x="tr@[a]"], auto)
    show "\<And>i. a = (i, ACrash) \<Longrightarrow> False" using noFails by auto
    show "\<And>i. (i, ACrash) \<in> set tr \<Longrightarrow> False" using c2 by auto 
    show "initialState (prog S') ~~ tr @ [a] \<leadsto>* S'"
      by (metis c3 local.step steps_do_not_change_prog steps_step)
  qed
qed


lemma state_wellFormed_combine:
  assumes wf: "state_wellFormed S"
    and steps: "S ~~ tr \<leadsto>* S'"
    and noFails: "\<And>i. (i, ACrash) \<notin> set tr"
  shows "state_wellFormed S'"
proof -
  from steps 
  have "prog S' = prog S"
    using steps_do_not_change_prog by auto

  from wf obtain tr1 where "initialState (prog S) ~~ tr1 \<leadsto>* S" and "(\<forall>i. (i, ACrash) \<notin> set tr1)"
    using state_wellFormed_def by blast 
  with steps
  have "initialState (prog S) ~~ tr1@tr \<leadsto>* S'"
    using steps_append by blast
  with \<open>prog S' = prog S\<close>
  have "initialState (prog S') ~~ tr1@tr \<leadsto>* S'" by simp
  moreover have "(\<forall>i. (i, ACrash) \<notin> set (tr1@tr))"
    by (simp add: \<open>\<forall>i. (i, ACrash) \<notin> set tr1\<close> noFails)
  ultimately show "state_wellFormed S'"
    using state_wellFormed_def by blast
qed  

lemma step_prog_invariant1:
  "S ~~ tr \<leadsto> S' \<Longrightarrow> prog S' = prog S"
  by (auto simp add: step.simps)

lemma step_prog_invariant:
  "S ~~ tr \<leadsto>* S' \<Longrightarrow> prog S' = prog S"
  by (induct rule: steps.induct, auto, erule step.cases, auto)


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
    proof (rule steps_step(2))
      show " P [] init"
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(1) steps_step.prems(2) by auto[1]
      show "S = init"
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(2) by auto[1]
    qed (simp add: steps_step.prems(3))
    show ?case
    proof (rule a3)
      show "init ~~ tr \<leadsto>* S'"
        using steps_step.hyps(1) steps_step.prems(2) by auto
      show "P tr S'" using \<open>P tr S'\<close> .
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
    and P_step: "\<And>t a s. \<lbrakk>state_wellFormed t; P t; t ~~ a \<leadsto> s; get_action a \<noteq> ACrash\<rbrakk> \<Longrightarrow> P s"
  shows "P s"
  using wf proof (auto simp add: state_wellFormed_def)
  fix tr 
  assume noFail: "\<forall>i. (i, ACrash) \<notin> set tr"
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
      show "S' ~~ a \<leadsto> S''" using \<open>S' ~~ a \<leadsto> S''\<close> .
      show "state_wellFormed S'"
        by (metis butlast_snoc in_set_butlastD state_wellFormed_combine state_wellFormed_init step.prems step.steps) 
      show "P S'"
        using step.IH step.prems by auto 
      show "get_action a \<noteq> ACrash"
        by (metis append_is_Nil_conv last_in_set last_snoc list.distinct(1) step.prems surjective_pairing)
    qed
  qed
qed



lemma wellFormed_callOrigin_dom:
  assumes a1: "state_wellFormed S"
  shows "dom (callOrigin S) = dom (calls S)"
  using a1 proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  from `t ~~ a \<leadsto> s`
  show ?case
    by (rule step.cases; insert step.hyps; auto split: if_splits; blast)
qed

lemma wellFormed_callOrigin_dom2:
  "\<lbrakk>calls S c = None; state_wellFormed S\<rbrakk> \<Longrightarrow>  callOrigin S c = None"
  using wellFormed_callOrigin_dom by force


lemma wellFormed_callOrigin_dom3:
  assumes a1: "state_wellFormed S"
  shows "(calls S c = None) \<longleftrightarrow> (callOrigin S c = None)"
  using assms wellFormed_callOrigin_dom by force

lemma range_empty: "range Map.empty = {None}"
  by auto





lemma wellFormed_currentTransaction_unique_h:
  assumes a1: "state_wellFormed S"
  shows "\<forall>sa sb t. currentTransaction S sa \<triangleq> t \<longrightarrow> currentTransaction S sb \<triangleq> t \<longrightarrow>  sa = sb"
    and "\<forall>sa t. currentTransaction S sa \<triangleq> t \<longrightarrow> transactionStatus S t \<triangleq> Uncommitted"
  using a1 by (induct  rule: wellFormed_induct, auto simp add: initialState_def elim!: step.cases split: if_splits)



lemmas wellFormed_currentTransaction_unique = wellFormed_currentTransaction_unique_h(1)[rule_format]
lemmas wellFormed_currentTransactionUncommitted = wellFormed_currentTransaction_unique_h(2)[rule_format]



lemma wellFormed_currentTransaction_back:
  assumes steps: "steps  S_init tr S"
    and noFail: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommitted: "\<And>tx. transactionStatus S_init tx \<noteq> Some Uncommitted"
    and wf: "state_wellFormed S_init"
  shows "transactionStatus S t \<triangleq> Uncommitted \<longrightarrow> (\<exists>!i. currentTransaction S i \<triangleq> t)"
  using steps noFail proof (induct  rule: steps_induct)
  case initial
  then show ?case by (simp add: initialState_def noUncommitted)
next
  case (step S' tr a S'')
  then show ?case 
  proof clarsimp
    assume a0: "S_init ~~ tr \<leadsto>* S'"
      and a1: "transactionStatus S' t \<triangleq> Uncommitted \<longrightarrow> (\<exists>!i. currentTransaction S' i \<triangleq> t)"
      and a2: "S' ~~ a \<leadsto> S''"
      and a3: "transactionStatus S'' t \<triangleq> Uncommitted"

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
      case (beginAtomic ls f ls' t vis snapshot)
      then show ?thesis using a0 a1 a3 \<open>state_wellFormed S'\<close> by (auto simp add: wellFormed_currentTransactionUncommitted split: if_splits, force)

    next
      case (endAtomic ls f ls' t)
      then show ?thesis using a1 a3 a0 by (auto split: if_splits, force)

    next
      case (dbop ls f Op args ls' t c res vis)
      then show ?thesis using a1 a3 by (auto split: if_splits)
    next
      case (invocation proc initialState impl)
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
    and noFail: "\<And>s. (s, ACrash) \<notin> set tr"
  shows "transactionStatus S t \<triangleq> Uncommitted \<longrightarrow> (\<exists>!i. currentTransaction S i \<triangleq> t)"
  using steps noFail  by (rule wellFormed_currentTransaction_back, simp add: initialState_def, simp add: state_wellFormed_init)

lemma wellFormed_currentTransaction_back3:
  assumes wf: "state_wellFormed S"
    and uncommitted: "transactionStatus S t \<triangleq> Uncommitted"
  shows "\<exists>!i. currentTransaction S i \<triangleq> t"
  using local.wf state_wellFormed_def uncommitted wellFormed_currentTransaction_back2 by blast

lemma wellFormed_currentTransaction_back4:
  assumes wf: "state_wellFormed S"
    and uncommitted: "\<And>i. currentTransaction S i \<noteq> Some t"
  shows "transactionStatus S t \<noteq> Some Uncommitted"
  using local.wf state_wellFormed_def uncommitted wellFormed_currentTransaction_back2 by blast



lemma callOrigin_same_committed: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Committed "
  shows "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx"     
  using exec by (rule step.cases; insert  wellFormed committed, auto simp add: wellFormed_callOrigin_dom2 wellFormed_currentTransaction_unique_h)



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
  using assms proof (induct rule: wellFormed_induct)
  case initial
  show "currentTransaction (initialState (prog S)) s = None" 
    and "localState (initialState (prog S)) s = None"
    by (auto simp add: initialState_def)

next
  case (step S a S')

  show "localState S' s = None"  if "invocationOp S' s = None"
    by (rule step.cases[OF `S ~~ a \<leadsto> S'`]; insert step that, auto split: if_splits)

  show "currentTransaction S' s = None" if "invocationOp S' s = None"
     by (rule step.cases[OF `S ~~ a \<leadsto> S'`]; insert step that, auto split: if_splits)
 qed

lemma wf_no_invocation_no_origin:
  assumes "state_wellFormed S"
    and "invocationOp S i = None"
  shows "transactionOrigin S tx \<noteq> Some i"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step S a S')
  show ?case 
    by (rule step.cases[OF `S ~~ a \<leadsto> S'`], insert step, (auto simp add: wf_localState_to_invocationOp split: if_splits ))
qed


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
  then show ?case by (auto simp add: step.simps wellFormed_currentTransaction_unique_h split: if_splits)
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
  then show ?case by (auto simp add: step.simps wellFormed_currentTransaction_unique_h split: if_splits)

qed

lemma finite_dom_spit:
  assumes "finite (dom A \<inter> {x. P x})" and "finite (dom B \<inter> {x. \<not>P x})"
  shows "finite (dom (\<lambda>x. if P x then A x else B x))"
proof (rule finite_subset[where  B="(dom A \<inter> {x. P x}) \<union> (dom B \<inter> {x. \<not>P x})"])
  show " dom (\<lambda>x. if P x then A x else B x) \<subseteq> dom A \<inter> {x. P x} \<union> dom B \<inter> {x. \<not> P x}"
    using assms by (auto split: if_splits)
  show "finite (dom A \<inter> {x. P x} \<union> dom B \<inter> {x. \<not> P x})"
    using assms by auto
qed

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

and noFail: "\<And>i. (i, ACrash)\<notin>set trace"
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
      by (metis length_append_singleton less_SucI nth_append_first step.prems(3))

    from a1 a2 a3 
    have IH: "currentTransaction S' invoc \<noteq> None"
      using step.IH step.prems(4) by auto 

    from this obtain y where [simp]: "currentTransaction S' invoc \<triangleq> y"
      by blast


    from step.prems(3)[where k="length tr"] 
    have [simp]: "a \<noteq> (invoc, AEndAtomic)"
      by (auto simp add: a1)


    with \<open>S' ~~ a \<leadsto> S''\<close>
    have ?case 
      using step.prems(4) by (auto simp add: step.simps)
  }
  moreover
  {
    assume "beginPos = length tr"
    then have "a = (invoc, ABeginAtomic tx txns)"
      using step.prems(1) by auto

    with \<open>S' ~~ a \<leadsto> S''\<close>
    have ?case 
      by (auto simp add: step.simps)
  }
  ultimately show ?case
    using less_SucE step.prems(2) by auto
qed


lemma no_new_calls_before_existing_h:
  assumes "S ~~ tr \<leadsto>* S'"
    and "c2\<in>dom (calls S)"
  shows "c2\<in>dom (calls S') \<and> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S')"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: step.simps split: if_splits)
qed

lemma no_new_calls_before_existing:
  assumes "S ~~ tr \<leadsto>* S'"
    and "c2\<in>dom (calls S)"
  shows "(c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'"
  using assms no_new_calls_before_existing_h by blast

lemma transactionStatus_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "transactionStatus S tx \<le> transactionStatus S' tx"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  then show ?case 
    using less_eq_option_None_is_None by (auto simp add: step.simps  split: if_splits, 
    force,
    smt linear onlyCommittedGreater)
qed

lemma transactionStatus_mono1: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "transactionStatus S tx \<triangleq> Committed \<Longrightarrow> transactionStatus S' tx \<triangleq> Committed"
  by (metis assms onlyCommittedGreater transactionStatus_mono)

lemma calls_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "calls S c \<triangleq> info \<Longrightarrow> calls S' c \<triangleq> info"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: step.simps )
qed


lemma no_new_calls_in_committed_transactions: 
  assumes "S ~~ tr \<leadsto>* S'"
    and "callOrigin S' c \<triangleq> tx"
    and "calls S c = None"
    and "state_wellFormed S"
    and "(\<forall>i. (i, ACrash) \<notin> set tr)"
  shows "transactionStatus S tx \<noteq> Some Committed"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by (auto simp add: wellFormed_callOrigin_dom2)

next
  case (step S' tr a S'')
  have "state_wellFormed S'"
    using \<open>S ~~ tr \<leadsto>* S'\<close> and \<open>state_wellFormed S\<close>
     state_wellFormed_combine \<open>\<forall>i. (i, ACrash) \<notin> set (tr @ [a])\<close> by fastforce

  have [simp]: "(i, ACrash) \<notin> set tr" for i
    using step.prems(4) by auto



  from \<open>S' ~~ a \<leadsto> S''\<close> \<open>callOrigin S'' c \<triangleq> tx\<close>
    \<open>calls S c = None\<close> step.IH \<open>state_wellFormed S\<close>
  show ?case 
    by (auto simp add: step.simps split: if_splits,
          insert \<open>state_wellFormed S'\<close> callOrigin_same_committed step.prems(1) step.step step.steps transactionStatus_mono1, 
         blast)

qed

lemma wf_transactionOrigin_and_status:
  assumes "state_wellFormed S"
  shows "transactionOrigin S tx = None \<longleftrightarrow> transactionStatus S tx = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps wellFormed_currentTransactionUncommitted split: if_splits)

qed

lemma wf_callOrigin_and_calls:
  assumes "state_wellFormed S"
  shows "callOrigin S c = None \<longleftrightarrow> calls S c = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps  split: if_splits)
qed

lemma callOrigin_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
    and "state_wellFormed S"
    and "(\<forall>i. (i, ACrash) \<notin> set tr)"
  shows "callOrigin S c \<triangleq> tx \<Longrightarrow> callOrigin S' c \<triangleq> tx"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')

  have [simp]: "(i, ACrash) \<notin> set tr" for i
    using step by auto

  have "state_wellFormed S'"
    using \<open>\<And>i. (i, ACrash) \<notin> set tr\<close> state_wellFormed_combine step.prems(2) step.steps by blast

  from step.IH \<open>S ~~ tr \<leadsto>* S'\<close> \<open>S' ~~ a \<leadsto> S''\<close>
    \<open>callOrigin S c \<triangleq> tx\<close> \<open>state_wellFormed S\<close>  \<open>state_wellFormed S'\<close>
  show ?case 
    by (auto simp add: step.simps wellFormed_callOrigin_dom2)


qed

lemma generatedIds_mono1: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "generatedIds S uid \<triangleq> i \<Longrightarrow> generatedIds S' uid \<triangleq> i"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  from step
  show ?case 
    by (auto simp add: step.simps )
qed

lemma generatedIds_mono1_self: 
  assumes "S ~~ tr \<leadsto>* S'"
and "\<And>a. (i,a)\<notin>set tr"
  shows "generatedIds S uid \<triangleq> i \<longleftrightarrow> generatedIds S' uid \<triangleq> i"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  from step
  show ?case 
    by (auto simp add: step.simps split: if_splits, blast)

qed

lemma knownIds_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "knownIds S \<subseteq> knownIds S'"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  from step
  show ?case 
    by (auto simp add: step.simps )
qed

lemma knownIds_mono2: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "x \<in> knownIds S \<Longrightarrow> x\<in> knownIds S'"
  using assms knownIds_mono by auto

lemma invocationOp_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
  shows "invocationOp S i \<triangleq> ops \<Longrightarrow> invocationOp S' i \<triangleq> ops"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')
  from step
  show ?case 
    by (auto simp add: step.simps )
qed

lemma wf_localState_needs_invocationOp:
  assumes "state_wellFormed S"
  shows "invocationOp S i = None \<Longrightarrow> localState S i = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps  split: if_splits)
qed

lemma wf_result_after_invocation:
  assumes "state_wellFormed S"
  shows "invocationOp S i = None \<Longrightarrow> invocationRes S i = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps wellFormed_invoc_notStarted  split: if_splits)
qed

lemma wf_localState_noReturn:
  assumes "state_wellFormed S"
  shows "localState S i \<triangleq> ls \<Longrightarrow> invocationRes S i = None"
  using assms proof (induct arbitrary: ls rule: wellFormed_induct )
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: step.simps  split: if_splits,
        insert wf_result_after_invocation, blast)
qed

lemma invocationRes_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
    and "state_wellFormed S"
    and "(\<forall>i. (i, ACrash) \<notin> set tr)"
  shows "invocationRes S i \<triangleq> ops \<Longrightarrow> invocationRes S' i \<triangleq> ops"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')

  have [simp]: "(i, ACrash) \<notin> set tr" for i
    using step by auto

  have "state_wellFormed S'"
    using \<open>\<And>i. (i, ACrash) \<notin> set tr\<close> state_wellFormed_combine step.prems(2) step.steps by blast

  from \<open>S ~~ tr \<leadsto>* S'\<close> step.IH
    \<open>S' ~~ a \<leadsto> S''\<close>
    \<open>invocationRes S i \<triangleq> ops\<close>
    \<open>state_wellFormed S\<close>
    \<open>state_wellFormed S'\<close>
  show ?case 
    by (auto simp add: step.simps wf_localState_noReturn)

qed

lemma transactionOrigin_mono: 
  assumes "S ~~ tr \<leadsto>* S'"
    and "transactionOrigin S t \<triangleq> i"
    and "state_wellFormed S"
    and "(\<forall>i. (i, ACrash) \<notin> set tr)"
  shows "transactionOrigin S' t \<triangleq> i"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case 
    by auto
next
  case (step S' tr a S'')

  have [simp]: "(i, ACrash) \<notin> set tr" for i
    using step by auto

  have "state_wellFormed S'"
    using \<open>\<And>i. (i, ACrash) \<notin> set tr\<close> state_wellFormed_combine step.prems(2) step.steps by blast


  from \<open>S' ~~ a \<leadsto> S''\<close> step.IH \<open>transactionOrigin S t \<triangleq> i\<close> \<open>state_wellFormed S\<close>
  show ?case 
    by (auto simp add: step.simps split: if_splits,
        metis \<open>state_wellFormed S'\<close> option.simps(3) wf_transactionOrigin_and_status)

qed

lemma steps_transactions_stable:
  assumes "S ~~ tr \<leadsto>* S'"
    and "callOrigin S' c \<triangleq> tx"
    and "transactionStatus S tx \<triangleq> Committed"
    and "state_wellFormed S"
    and "(\<forall>i. (i, ACrash) \<notin> set tr)"
  shows "callOrigin S c \<triangleq> tx"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'')

  have [simp]: "(i, ACrash) \<notin> set tr" for i
    using step by auto

  have "state_wellFormed S'"
    using state_wellFormed_combine step.prems(3) step.prems(4) step.steps by fastforce 


  from step.IH 
    \<open>S ~~ tr \<leadsto>* S'\<close>
    \<open>S' ~~ a \<leadsto> S''\<close>
    \<open>callOrigin S'' c \<triangleq> tx\<close>
    \<open>transactionStatus S tx \<triangleq> Committed\<close>
    \<open>state_wellFormed S\<close>
  show ?case by (auto simp add: step.simps split: if_splits,
         insert \<open>state_wellFormed S'\<close> callOrigin_same_committed step.prems(1) step.step transactionStatus_mono1, 
         blast)

qed

lemma exists_implementation:
  assumes "state_wellFormed S"
    and "currentProc S i \<triangleq> impl"
    and "progr = prog S"
  shows "\<exists>p lsInit. procedure progr p = (lsInit, impl)"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step t a s)
  then show ?case
    by (auto simp add: step.simps wellFormed_invoc_notStarted  split: if_splits, auto)
qed


lemma chooseSnapshot_subsetOfCalls:
  assumes  a1: "state_wellFormed S"
      and a2: "chooseSnapshot snapshot vis S"
      and a3: "happensBefore S \<subseteq> dom (calls S) \<times> dom (calls S)"
      and a4: "vis \<subseteq> dom (calls S)"
  shows "snapshot \<subseteq> dom (calls S)"
  using a2 proof (auto simp add: chooseSnapshot_def)
    fix x newTxns
    assume b1: "newTxns \<subseteq> committedTransactions S"
       and b2: "snapshot = vis \<union> callsInTransaction S newTxns \<down> happensBefore S"
    
    show "\<exists>y. calls S x \<triangleq> y" if b3: "x \<in> vis"
      using a4 that by blast

    show "\<exists>y. calls S x \<triangleq> y" if " x \<in> callsInTransaction S newTxns \<down> happensBefore S"
      using that proof (auto simp add: downwardsClosure_in)

      show "\<exists>y. calls S x \<triangleq> y"
        if c0: "x \<in> callsInTransaction S newTxns"
        using a1 callsInTransactionH_contains that wellFormed_callOrigin_dom2 by fastforce


      show "\<exists>y. calls S x \<triangleq> y"
        if c0: "y \<in> callsInTransaction S newTxns"
          and c1: "(x, y) \<in> happensBefore S"
        for  y
        using a3 c1 by blast
    qed
  qed





lemma wellFormed_visibleCallsSubsetCalls_h:
  assumes a1: "state_wellFormed S"
  shows "happensBefore S \<subseteq> dom (calls S) \<times> dom (calls S)"
    and "\<And>vis s. visibleCalls S s \<triangleq> vis \<Longrightarrow>  vis \<subseteq> dom (calls S)"
  using a1 proof (induct rule: wellFormed_induct)
  case initial
  show " happensBefore (initialState (prog S))
    \<subseteq> dom (calls (initialState (prog S))) \<times> dom (calls (initialState (prog S)))"
    by  (simp add: initialState_def)

  show "vis \<subseteq> dom (calls (initialState (prog S)))"
    if c0: "visibleCalls (initialState (prog S)) s \<triangleq> vis"
    for  vis s
    using that  by  (simp add: initialState_def)

next
  case (step S a S')

  show "happensBefore S' \<subseteq> dom (calls S') \<times> dom (calls S')"
    by (rule step.cases[OF `S ~~ a \<leadsto> S'`],
      insert step,
      auto split: if_splits, 
      blast+)

  from step
  have IH: "\<exists>y. calls S c \<triangleq> y"
    if "visibleCalls S i \<triangleq> vis"
      and "c\<in>vis"
    for i vis c
    using that by blast


  show "vis \<subseteq> dom (calls S')"
      if c0: "visibleCalls S' i \<triangleq> vis"
   for vis i
    by (rule step.cases[OF `S ~~ a \<leadsto> S'`];
      insert that IH step.hyps(2),
      auto split: if_splits dest: chooseSnapshot_subsetOfCalls[OF `state_wellFormed S`])
qed


lemma wellFormed_visibleCallsSubsetCalls2: "\<lbrakk>
      state_wellFormed S;
      visibleCalls S sb \<triangleq> visa;
      calls S c = None
    \<rbrakk> \<Longrightarrow> c\<notin>visa"
  by (meson domIff set_mp wellFormed_visibleCallsSubsetCalls_h(2))


lemma wellFormed_committedCallsExist:
  assumes a1: "calls S c = None"
    and a2: "state_wellFormed S"
  shows "c \<notin> committedCalls S"
  using a1 a2
  by (smt committedCallsH_def isCommittedH_def domIff mem_Collect_eq option.simps(3) wellFormed_callOrigin_dom) 

lemma noOrigin_notCommitted:
  "callOrigin S c = None \<Longrightarrow> c \<notin> committedCalls S"  
  by (auto simp add: committedCallsH_def isCommittedH_def)


text \<open>
 The invocId info is set iff there was an invocId in the trace
\<close>
lemma invation_info_set_iff_invocation_happened:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
  shows "(invocationOp S s = None) \<longleftrightarrow> (\<forall>proc. (s, AInvoc proc)\<notin> set tr )"
    and "\<forall>proc. (invocationOp S s = Some proc) \<longleftrightarrow> ((s, AInvoc proc) \<in> set tr )"
  using steps proof (induct rule: steps_induct)
  case initial
  show "(invocationOp (initialState program) s = None) \<longleftrightarrow> (\<forall>proc. (s, AInvoc proc) \<notin> set [])"
    by (auto simp add: initialState_def)
  show "\<forall>proc. invocationOp (initialState program) s \<triangleq> proc = ((s, AInvoc proc ) \<in> set [])"
    by (auto simp add: initialState_def)
next
  case (step S' tr a S'')

  show "(invocationOp S'' s = None) = (\<forall>proc. (s, AInvoc proc) \<notin> set (tr @ [a]))"
    using \<open>S' ~~ a \<leadsto> S''\<close> by (induct rule: step.cases, auto simp add: step.IH(1))

  show "\<forall>proc. invocationOp S'' s \<triangleq> proc = ((s, AInvoc proc) \<in> set (tr @ [a]))"
    using \<open>S' ~~ a \<leadsto> S''\<close> using step.IH(2) by (induct rule: step.cases, auto)
qed

lemma invocation_ops_if_localstate_nonempty:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and loc: "localState S s \<noteq> None"
  shows "invocationOp S s \<noteq> None" 
  using assms proof (induct arbitrary:   rule: steps_induct)
  case initial
  then show ?case
    by (simp add: initialState_def) 
next
  case (step S' tr a S'')

  show ?case
  proof (cases "get_invoc a = s")
    case True
    from this obtain action where [simp]: "a = (s, action)"
      using surjective_pairing by blast 
    show ?thesis 
      using \<open>S' ~~ a \<leadsto> S''\<close> proof (induct rule: step.cases)
      case (local C s ls f ls')
      then show ?case using step.IH by (auto simp add: True)
    next
      case (newId C s ls f ls' uid)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (beginAtomic C s ls f ls' t)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (endAtomic C s ls f ls' t)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (dbop C s ls f Op ls' t c res vis)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (invocation C s procName initialState impl)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (return C s ls f res)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (fail C s')
      with \<open>localState S'' s \<noteq> None\<close> have False
        by auto
      then show ?case ..
    next
      case (invCheck C res s')
      then show ?case  using step.IH
        using step.prems by blast 
    qed
  next
    case False then have [simp]: "get_invoc a \<noteq> s" .
    from \<open>S' ~~ a \<leadsto> S''\<close>
    have "localState S'' s = localState S' s" and "invocationOp S'' s = invocationOp S' s"
      using False by (induct rule: step.cases, auto)

    then show ?thesis
      using step.IH step.prems by auto 
  qed
qed


text \<open>
 After a fail or return the local state is None
\<close>
lemma everything_starts_with_an_invocation:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and fail_or_return: "tr!i = (s, ACrash) \<or> tr!i = (s, AReturn res)"
    and i_in_range: "i < length tr"
  shows "localState S s = None \<and> invocationOp S s \<noteq> None" 
  using steps fail_or_return i_in_range
proof (induct rule: steps_induct)
  case initial
  then show ?case
    by simp 
next
  case (step S' tr a S'')

  then have steps'': "initialState program ~~ (tr@[a]) \<leadsto>* S''"
    using steps_step by blast



  show ?case 
  proof (cases "i < length tr")
    case True
    then have "tr ! i = (s, ACrash) \<or> tr ! i = (s, AReturn res)"
      using \<open>(tr @ [a]) ! i = (s, ACrash) \<or> (tr @ [a]) ! i = (s, AReturn res)\<close>
      by (auto simp add: nth_append)
    then have "localState S' s = None"
      by (simp add: True step.IH) 

    show ?thesis 
      using \<open>S' ~~ a \<leadsto> S''\<close> 
      by (induct rule: step.cases;
          insert True \<open>tr ! i = (s, ACrash) \<or> tr ! i = (s, AReturn res)\<close> step.IH,
          auto)
  next
    case False
    show ?thesis 
    proof (cases "i = length tr")
      case True
      with \<open>(tr @ [a]) ! i = (s, ACrash) \<or> (tr @ [a]) ! i = (s, AReturn res)\<close>
      have cases: "a = (s, ACrash) \<or> a = (s, AReturn res)"
        by simp


      then show ?thesis 
      proof (rule; intro conjI)
        assume "a = (s, ACrash)"
        then have "S' ~~ (s, ACrash) \<leadsto> S''"
          using step.step by auto


        then show "localState S'' s = None"
          by (auto simp add: step_simp_ACrash)
            (*
        hence "invocationOp S'' s \<noteq> None" 
          using invocation_ops_if_localstate_nonempty[OF steps'']
          *)

        have "localState S' s \<noteq> None"
          using \<open>S' ~~ (s, ACrash) \<leadsto> S''\<close> 
          by (induct rule: step.cases, auto)

        then have "invocationOp S' s \<noteq> None"
          using invocation_ops_if_localstate_nonempty step.steps by blast
        then show "invocationOp S'' s \<noteq> None"  
          using \<open>S' ~~ (s, ACrash) \<leadsto> S''\<close> invation_info_set_iff_invocation_happened(1) step.steps steps''
          by (metis butlast_snoc in_set_butlastD)  
      next 
        assume "a = (s, AReturn res)"
        then have "S' ~~ (s, AReturn res) \<leadsto> S''"
          using step.step by auto
        then show "localState S'' s = None"
          by (auto simp add: step_simp_AReturn)

        from \<open>S' ~~ (s, AReturn res) \<leadsto> S''\<close>  
        show "invocationOp S'' s \<noteq> None"
          using invocation_ops_if_localstate_nonempty step.steps step_simp_AReturn
          by (metis butlast_snoc in_set_butlastD invation_info_set_iff_invocation_happened(1) option.distinct(1) steps'') 
      qed    

    next
      case False
      with \<open>\<not> (i < length tr)\<close> have "i > length tr" by arith
      then show ?thesis
        using step.prems(2) by auto 
    qed
  qed
qed  



lemma chooseSnapshot_unchanged:
  assumes
  a0: "chooseSnapshot snapshot vis S1"
  and a2: "happensBefore S2 = happensBefore S1 "
  and a4: "transactionStatus S2 = transactionStatus S1 "
  and a5: "callOrigin S2 = callOrigin S1 "
shows "chooseSnapshot snapshot vis S2"
  using a0 a2 a4 a5 by (auto simp add: chooseSnapshot_def)

lemma chooseSnapshot_unchanged_precise:
  assumes
  a0: "chooseSnapshot_h snapshot vis txStatus1 cOrigin1 hb1"
  and a2: "\<And>tx. txStatus1 tx \<triangleq> Committed \<Longrightarrow> txStatus2 tx \<triangleq> Committed "
  and a3: "\<And>tx. txStatus1 tx \<triangleq> Committed \<Longrightarrow> (\<forall>c. cOrigin1 c \<triangleq> tx \<longleftrightarrow> cOrigin2 c \<triangleq> tx)"
  and a4: "\<And>tx c. \<lbrakk>txStatus1 tx \<triangleq> Committed; cOrigin1 c \<triangleq> tx\<rbrakk> \<Longrightarrow> (\<forall>c'. (c',c)\<in>hb1 \<longleftrightarrow> (c',c)\<in>hb2)"
shows "chooseSnapshot_h snapshot vis txStatus2 cOrigin2 hb2"
proof -
  from a0 obtain newTxns newCalls
    where "\<forall>txn\<in>newTxns. txStatus1 txn \<triangleq> Committed"
      and "newCalls = callsInTransactionH cOrigin1 newTxns \<down> hb1"
      and "snapshot = vis \<union> newCalls"
    by (metis chooseSnapshot_h_def)

  show "chooseSnapshot_h snapshot vis txStatus2 cOrigin2 hb2"
    unfolding chooseSnapshot_h_def
  proof (intro exI conjI)
    show "snapshot = vis \<union> newCalls" using \<open>snapshot = vis \<union> newCalls\<close>.
    show "\<forall>txn\<in>newTxns. txStatus2 txn \<triangleq> Committed"
      using `\<forall>txn\<in>newTxns. txStatus1 txn \<triangleq> Committed` a2 by auto
    show "newCalls = callsInTransactionH cOrigin2 newTxns \<down> hb2"
      using \<open>\<forall>txn\<in>newTxns. txStatus1 txn \<triangleq> Committed\<close> a3 a4
      unfolding  callsInTransactionH_def downwardsClosure_def
      by (simp add: callsInTransactionH_def downwardsClosure_def \<open>newCalls = callsInTransactionH cOrigin1 newTxns \<down> hb1\<close>, blast)

  qed
qed


lemma generatedIds_mono:
  "\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> generatedIds A \<subseteq>\<^sub>m generatedIds B"
  by (erule step.cases, auto simp add: map_le_def)

lemma generatedIds_mono2:
  assumes "generatedIds A x \<triangleq> i"
and "A ~~ a \<leadsto> B" 
shows"generatedIds B x \<triangleq> i"
  using generatedIds_mono[OF \<open>A ~~ a \<leadsto> B\<close>] assms by (auto simp add: map_le_def, force)


lemma generatedIds_mono2_rev:
  assumes  "generatedIds B x = None"
    and "A ~~ a \<leadsto> B"
  shows "generatedIds A x = None"
  using generatedIds_mono[OF \<open>A ~~ a \<leadsto> B\<close>] assms by (auto simp add: map_le_def, force)


lemma transactionStatus_mono':
  "\<lbrakk>transactionStatus B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> transactionStatus A tx = None"
  by (erule step.cases, auto split: if_splits)

lemma transactionStatus_mono2:
  "\<lbrakk>transactionStatus B tx \<triangleq> Committed; A ~~ a \<leadsto> B; get_action a\<noteq>AEndAtomic\<rbrakk> \<Longrightarrow> transactionStatus A tx \<triangleq> Committed"
  by (erule step.cases, auto split: if_splits)


lemma calls_mono':
  "\<lbrakk>calls B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> calls A tx = None"
  by (erule step.cases, auto split: if_splits)

lemma prog_inv:
  "\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> prog B = prog A"
  by (erule step.cases, auto split: if_splits)




lemma committed_same: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
  shows "transactionStatus A t \<triangleq> Committed \<longleftrightarrow> transactionStatus B t \<triangleq> Committed" 
  using exec by (rule step.cases, auto simp add: aIsNotCommit)    

lemma happensBefore_same_committed2: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Committed " 
    and orig_y: "callOrigin A y \<triangleq> tx"
  shows "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
  using exec by (rule step.cases,
      insert wellFormed committed orig_y,
      auto simp add: wellFormed_callOrigin_dom2 )


lemma invContextSame_h: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Committed"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
  shows "(callsInTransaction A txns \<down> happensBefore A) = (callsInTransaction B txns \<down> happensBefore B)"
  by (auto simp add: callsInTransactionH_def downwardsClosure_in,
      (metis (mono_tags, lifting) "1" aIsNotCommit callOrigin_same_committed exec snd_conv happensBefore_same_committed2 transactionStatus_mono2 wellFormed)+)

 
lemma inTransaction_localState:
  assumes wf: "state_wellFormed A"
    and tx: "currentTransaction A s \<triangleq> tx"
  shows "localState A s \<noteq> None"
  using wf tx proof (induct arbitrary: s tx rule: wellFormed_induct )
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step S a S')
  show ?case 
    by (rule step.cases[OF ` S ~~ a \<leadsto> S'`],
        insert step, 
        auto split: if_splits)
qed



lemma invContextSnapshot_same: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Committed"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommitted: "transactionStatus A tx \<triangleq> Uncommitted"
  shows "(invContext A) = (invContext B)"
proof (auto simp add: invContextH_def invContextSame_h[OF exec wellFormed 1 aIsNotCommit])
  have committed_same: "committedCalls B = committedCalls A"
    using exec by (rule step.cases, auto simp add:  aIsInTransaction txIsUncommitted committedCallsH_def  isCommittedH_def aIsNotCommit wellFormed wellFormed_callOrigin_dom2)

  have committed_subset: "committedCalls A \<subseteq> dom (calls A)"
    using wellFormed wellFormed_callOrigin_dom
    by (auto simp add: committedCallsH_def isCommittedH_def aIsNotCommit wellFormed, fastforce+)



  show "calls A |` committedCalls A = calls B |` committedCalls B"
    using exec by (rule step.cases, 
      auto simp add: committedCallsH_def isCommittedH_def aIsInTransaction aIsNotCommit,
      metis option.inject transactionStatus.distinct(1) txIsUncommitted,
      metis (no_types, lifting) option.distinct(1) wellFormed wellFormed_callOrigin_dom2)

  show "\<And>a b. (a, b) \<in> happensBefore A |r committedCalls A \<Longrightarrow> (a, b) \<in> happensBefore B |r committedCalls B"
    by (simp add: committed_same,
        rule step.cases[OF exec],
        auto simp add: restrict_relation_def)


  show "\<And>a b. (a, b) \<in> happensBefore B |r committedCalls B \<Longrightarrow> (a, b) \<in> happensBefore A |r committedCalls A"
    by (simp add: committed_same,
        rule step.cases[OF exec],
        auto simp add: wellFormed_callOrigin_dom2 restrict_relation_def committedCallsH_def isCommittedH_def wellFormed)


  show "callOrigin A |` committedCalls A = callOrigin B |` committedCalls B"
    by (simp add: committed_same, 
        rule step.cases[OF exec],
        auto simp add:  committedCallsH_def isCommittedH_def,
        meson domI domIff wellFormed wellFormed_callOrigin_dom2)


  show "\<And>x. x \<in> knownIds A \<Longrightarrow> x \<in> knownIds B"
    using exec by (rule step.cases, auto)

  show "\<And>x. x \<in> knownIds B \<Longrightarrow> x \<in> knownIds A"
    using exec by (rule step.cases, auto simp add: aIsInTransaction)

  from wellFormed and aIsInTransaction
  have "localState A sa \<noteq> None"
    by (simp add: inTransaction_localState)


  show "invocationOp A = invocationOp B"
    using exec by (rule step.cases, auto, insert \<open>localState A sa \<noteq> None\<close>, blast)

  show "invocationRes A = invocationRes B"
    using exec by (rule step.cases, auto simp add: aIsInTransaction)


  have "transactionOrigin A t = transactionOrigin B t"  for t
    using exec by (rule step.cases, auto simp add: aIsInTransaction)


  show "transactionOrigin A |` committedTransactions A = transactionOrigin B |` committedTransactions B"
    using exec by (rule step.cases,
            auto simp add: restrict_map_def aIsInTransaction  aIsNotCommit exec committed_same)



qed    


lemma committedCalls_uncommittedNotIn:
  assumes "callOrigin S c \<triangleq> t"
    and "transactionStatus S t \<triangleq> Uncommitted"
  shows  "c \<notin> committedCalls S"
  using assms by (auto simp add: committedCallsH_def isCommittedH_def)




lemma unchanged_in_step:
  assumes differentSessions[simp]: "sa \<noteq> sb"
    and exec: "A ~~ (sa, a) \<leadsto> B"
  shows
    "localState A sb = localState B sb"
    and "currentProc A sb = currentProc B sb"
    and "currentTransaction A sb = currentTransaction B sb"
    and "visibleCalls A sb = visibleCalls B sb"
    and "invocationOp A sb = invocationOp B sb"
    and "invocationRes A sb = invocationRes B sb"
  using exec by (auto simp add: differentSessions[symmetric] elim!: step_elim_general)

lemma unchangedInTransaction_knownIds:
  assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
  shows "knownIds A = knownIds B"
  using exec by (cases a, auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims)

lemmas unchangedInTransaction = unchanged_in_step unchangedInTransaction_knownIds

lemma getContext_happensBefore:
  "getContext (A\<lparr>happensBefore := hb\<rparr>) s = (
    case visibleCalls A s of 
      None \<Rightarrow> emptyOperationContext 
    | Some vis \<Rightarrow> \<lparr>calls = calls A |` vis, happensBefore = hb |r vis\<rparr>)"
  by (auto simp add: getContextH_def split: option.splits)

\<comment> \<open>getContext is not changed by actions in other transactions\<close>
lemma unchangedInTransaction_getContext:
  assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
  shows
    "getContext A sb = getContext B sb"
proof (cases a)
  case ALocal
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ANewId x2)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ABeginAtomic x3)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AEndAtomic
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ADbOp callId operation res)
  from this
  obtain ls f ls' vis 
    where 1: "localState A sa \<triangleq> ls"
      and 2: "currentProc A sa \<triangleq> f"
      and 3: "f ls = DbOperation operation ls'"
      and 4: "querySpec (prog A) operation (getContext A sa) res"
      and 5: "visibleCalls A sa \<triangleq> vis"
      and 6: "B = A\<lparr>localState := localState A(sa \<mapsto> ls' res), calls := calls A(callId \<mapsto> Call operation res), callOrigin := callOrigin A(callId \<mapsto> tx), visibleCalls := visibleCalls A(sa \<mapsto> {callId} \<union> vis),
                happensBefore := happensBefore A \<union> vis \<times> {callId}\<rparr>"
    using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
  have case1: "getContext B sb = getContext A sb" if "visibleCalls A sb = None"
    by (auto simp add: that getContextH_def split: option.splits,
        insert aIsInTransaction differentSessions exec that unchangedInTransaction(4), fastforce+)

  have case2: "getContext B sb = getContext A sb" if visi_def[simp]: "visibleCalls A sb \<triangleq> visi" for visi
  proof -
    from visi_def
    have [simp]: "visibleCalls B sb \<triangleq> visi"
      using aIsInTransaction differentSessions exec unchangedInTransaction(4) by fastforce

    then have "visi \<subseteq> dom (calls A)"  
      using visibleCalls_inv  using visi_def by blast 
    show "getContext B sb = getContext A sb"
    proof (simp add:  getContextH_def split: option.splits, intro conjI)
      have "(calls B |` visi) c = (calls A |` visi) c" for c
        by (auto simp add: restrict_map_def 6,
          smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD domIff exec step_elim_ADbOp)
      then show "calls B |` visi = calls A |` visi" ..
    next
      show "happensBefore B |r visi = happensBefore A |r visi"
        by (auto simp add: restrict_relation_def 6,
          smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD domIff exec step_elim_ADbOp)
    qed    
  qed 
  from case1 case2 show ?thesis by fastforce 
next
  case (AInvoc x71 )
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AReturn x8)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case ACrash
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvcheck x10)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
qed



lemma getContextH_visUpdate:
  assumes "c \<notin> vis"
  shows "getContextH cs (hb \<union> v \<times> {c}) (Some vis)
     = getContextH cs hb (Some vis)"
  using assms by (auto simp add: getContextH_def restrict_relation_def split: option.splits)

lemma getContextH_callsUpdate:
  assumes "c \<notin> vis"
  shows "getContextH (cs(c\<mapsto>newCall)) hb (Some vis)
     = getContextH cs hb (Some vis)"
  using assms by (auto simp add: getContextH_def split: option.splits)



lemma  callsInTransactionH_originUpdate_unchanged:
  assumes a1: "currentTransaction S sa \<triangleq> t"
    and a2: "state_wellFormed S"
    and a3: "calls S c = None"
    and a4: "txns \<subseteq> committedTransactions S"
  shows "callsInTransactionH (callOrigin S(c \<mapsto> t)) txns
           = callsInTransactionH (callOrigin S) txns"
  using a1 a2 a4 wellFormed_currentTransaction_unique_h(2) 
  by (auto simp add: callsInTransactionH_def a2 a3 wellFormed_callOrigin_dom2, fastforce)


lemma callsInTransaction_down_hb_unchanged:"
\<lbrakk> calls S c = None;
 state_wellFormed S\<rbrakk>
 \<Longrightarrow> callsInTransaction S txns \<down> (happensBefore S \<union> visa \<times> {c})
   = callsInTransaction S txns \<down> (happensBefore S)"
  by (auto simp add: downwardsClosure_def callsInTransactionH_def wellFormed_callOrigin_dom2)




lemma currentTransaction_unchangedInternalSteps:
  assumes "S ~~ tr \<leadsto>* S'"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> get_action a \<noteq> AEndAtomic"
    and "\<And>a tx ntxns.  a \<in> set tr \<Longrightarrow> get_action a \<noteq> ABeginAtomic tx ntxns"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> get_action a \<noteq> ACrash"
  shows "currentTransaction S' s = currentTransaction S s"  
  using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by auto
next
  case (steps_step S tr S' a S'')
  then show ?case 
  proof (cases "get_action a")
    case ALocal
    then show ?thesis using steps_step by (cases a, auto simp add: step_simps)
  next
    case (ANewId x2)
    then show ?thesis using steps_step by (cases a, auto simp add: step_simps)
  next
    case (ABeginAtomic x3)
    then show ?thesis using steps_step by auto 
  next
    case AEndAtomic
    then show ?thesis using steps_step by auto
  next
    case (ADbOp)
    then show ?thesis using steps_step by (cases a, auto simp add: step_simps)
  next
    case (AInvoc )
    then show ?thesis using steps_step by (cases a, auto simp add: step_simps)
  next
    case (AReturn x8)
    then show ?thesis using steps_step by (cases a, cases "currentTransaction S s", auto elim: step_elims)
  next
    case ACrash
    then show ?thesis using steps_step
      by auto
  next
    case (AInvcheck x10)
    then show ?thesis using steps_step by (cases a, cases "currentTransaction S s", auto elim: step_elims)
  qed
qed






lemma currentTransaction_unchangedInternalSteps2:
  assumes "S ~~ tr \<leadsto>* S'"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> get_action a \<noteq> AEndAtomic"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> get_action a \<noteq> ACrash"
    and "currentTransaction S s = Some t"  
    and wf: "state_wellFormed S"
  shows "currentTransaction S' s = Some t"  and "a \<in> set tr \<Longrightarrow> a \<noteq> (s, ABeginAtomic tx ntxn)" 
  using assms by (induct arbitrary: a tx ntxn rule: steps.induct, 
      auto simp add: currentTransaction_unchangedInternalSteps step_simps_all split: if_splits, blast+)

lemma currentTransaction_unchangedInternalSteps4:
  assumes "S ~~ tr \<leadsto>* S'"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> a \<noteq> (s, AEndAtomic)"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> a \<noteq> (s, ACrash)"
    and "currentTransaction S s = Some t"  
    and wf: "state_wellFormed S"
  shows "currentTransaction S' s = Some t"  and "a \<in> set tr \<Longrightarrow> a \<noteq> (s, ABeginAtomic tx ntxn)" 
  using assms by (induct arbitrary: a tx ntxn rule: steps.induct,
    auto simp add: currentTransaction_unchangedInternalSteps  step_simps_all split: if_splits, blast+)





lemma currentTransaction_unchangedInternalSteps3:
  assumes a1: "s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S'"
    and a2: "\<And>st act.  (st, act) \<in> set as \<Longrightarrow> st = s \<and> act \<noteq> AEndAtomic \<and> act \<noteq> ACrash"
    and wf: "state_wellFormed s_init"
  shows "currentTransaction S' s \<triangleq> tx"
proof -
  from a1 
  obtain S where 1: "s_init ~~ (s, ABeginAtomic tx ntxns) \<leadsto> S" and 2: "S ~~ as \<leadsto>* S'"
    using steps_appendFront by blast
  from 2
  show "currentTransaction S' s \<triangleq> tx"
  proof (rule currentTransaction_unchangedInternalSteps2)
    from a2
    show "\<And>a. a \<in> set as \<Longrightarrow> get_action a \<noteq> AEndAtomic" and "\<And>a. a \<in> set as \<Longrightarrow> get_action a \<noteq> ACrash"
      by auto    
    from 1
    show "currentTransaction S s \<triangleq> tx"
      by (auto simp add: step_simps)

    from wf 1
    show "state_wellFormed S"
      using state_wellFormed_combine  
      by (metis action.distinct(39) empty_iff insert_iff list.set(1) list.simps(15) snd_conv steps_single)
  qed
qed


lemma beginAtomicInTrace_to_transactionStatus:
  assumes "S ~~ tr \<leadsto>* S'" 
    and "(s, ABeginAtomic tx ntxns) \<in> set tr"
  shows "tx \<in> dom (transactionStatus S')"
  using assms by (induct rule: steps.induct, auto simp add: step_simps_all)


lemma transactionIdsUnique:
  assumes "S ~~ tr \<leadsto>* S'" 
    and "i < length tr" 
    and "tr!i = (s, ABeginAtomic tx ntxns)"
    and "j < length tr" 
    and "tr!j = (s', ABeginAtomic tx ntxns')"
  shows "i = j"    
  using assms by (induct rule: steps.induct,
    auto simp add: step_simps Pair_inject  less_Suc_eq nth_append  ,
    metis beginAtomicInTrace_to_transactionStatus domIff nth_mem,
    metis beginAtomicInTrace_to_transactionStatus domIff nth_mem)

lemma transactionIdsUnique2:
  assumes "S ~~ tr \<leadsto>* S'" 
    and "(s, ABeginAtomic tx ntxns)\<in>set tr" 
    and "(s', ABeginAtomic tx ntxns')\<in>set tr" 
  shows "s' = s"
  by (metis Pair_inject assms(1) assms(2) assms(3) in_set_conv_nth transactionIdsUnique)


lemma currentTransaction:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "i < length tr"
    and "tr!i = (s, ABeginAtomic txi ntxns)"
  shows "(\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (s, AEndAtomic) \<and> tr!j \<noteq> (s, ACrash)) \<longleftrightarrow> currentTransaction S' s \<triangleq> txi"
  using assms proof (induct arbitrary: txi i ntxns rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')


  {
  assume "i < length tr"

  have IH: "(\<forall>j. i < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic) \<and> tr ! j \<noteq> (s, ACrash)) =
        currentTransaction S' s \<triangleq> txi"
    by (metis \<open>i < length tr\<close> nth_append steps_step.hyps(2) steps_step.prems(2))

  have IH2: "(\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow>
         (tr @ [a]) ! j \<noteq> (s, AEndAtomic) \<and> (tr @ [a]) ! j \<noteq> (s, ACrash)) =
    currentTransaction S'' s \<triangleq> txi"
    if "a \<noteq> (s, AEndAtomic)"
      and "a \<noteq> (s, ACrash)"
      and "currentTransaction S'' s = currentTransaction S' s"
    using IH that by (auto simp add: nth_append)

  have cannot_start_again: "a \<noteq> (s, ABeginAtomic txi newTxns)" for newTxns
    by (metis \<open>i < length tr\<close> beginAtomicInTrace_to_transactionStatus domD nth_append nth_mem option.simps(3) step_simps(3) steps_step.hyps(1) steps_step.hyps(3) steps_step.prems(2))


  have IH4: "(\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow>
         (tr @ [a]) ! j \<noteq> (s, AEndAtomic) \<and> (tr @ [a]) ! j \<noteq> (s, ACrash)) =
    currentTransaction S'' s \<triangleq> txi"
    if "a = (s, AEndAtomic)"
    using `S' ~~ a \<leadsto> S''`
    using  that \<open>i < length tr\<close> by (auto simp add: nth_append step_simps)

  have IH5: "(\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow>
         (tr @ [a]) ! j \<noteq> (s, AEndAtomic) \<and> (tr @ [a]) ! j \<noteq> (s, ACrash)) =
    currentTransaction S'' s \<triangleq> txi"
    if "a = (s, ACrash)"
    using `S' ~~ a \<leadsto> S''`
    using IH that \<open>i < length tr\<close> by (auto simp add: nth_append step_simps)

  have IH6: "(\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow>
         (tr @ [a]) ! j \<noteq> (s, AEndAtomic) \<and> (tr @ [a]) ! j \<noteq> (s, ACrash)) =
    currentTransaction S'' s \<triangleq> txi"
    if "a = (s, ABeginAtomic t nt)" for t nt
    using `S' ~~ a \<leadsto> S''`
    using IH that \<open>i < length tr\<close> cannot_start_again by (auto simp add: nth_append step_simps, blast+)

  have "a = (s, ACrash) \<or> a = (s, AEndAtomic) \<or> (\<exists>t nt. a = (s, ABeginAtomic t nt)) \<or> currentTransaction S'' s = currentTransaction S' s"
    by (rule step.cases[OF `S' ~~ a \<leadsto> S''`], auto)

  hence ?case
    using IH2 IH4 IH5 IH6 by blast
}
  moreover
  {
    assume "i = length tr"

    have ?case
      using  steps_step.prems(2) by (induct rule: step.cases[OF `S' ~~ a \<leadsto> S''`],
         auto simp add: nth_append `i = length tr`)
  }
  ultimately
  show ?case
    using `i < length (tr @ [a])` by force
qed


lemma currentTransaction2:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "i < length tr"
    and "tr!i = (s, ABeginAtomic txi ntxns)"
    and "\<And>j. \<lbrakk>i<j; j<length tr\<rbrakk> \<Longrightarrow> tr!j \<noteq> (s, ACrash)"
    and "\<And>j. \<lbrakk>i<j; j<length tr\<rbrakk> \<Longrightarrow> tr!j \<noteq> (s, AEndAtomic)"
  shows "currentTransaction S' s \<triangleq> txi"
  using assms currentTransaction by blast


lemma noNestedTransactions:
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and "tr!i = (s, ABeginAtomic txi ntxnsi)"
    and "i<j"
    and "j < length tr" 
    and "tr!j = (s, ABeginAtomic txj ntxnsj)"
  shows "\<exists>k. i<k \<and> k < j \<and> (tr!k = (s, AEndAtomic) \<or> tr!k = (s, ACrash))"  
  using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')
  then show ?case 
  proof (cases "j < length tr")
    case True
    then show ?thesis
      using steps_step by (auto simp add: nth_append dest: less_trans)
  next
    case False
    then have [simp]: "j = length tr"
      using steps_step by auto


    have "S ~~ tr@[a] \<leadsto>* S''"
      using steps.steps_step steps_step.hyps(1) steps_step.hyps(3) by blast
    have "(tr @ [a]) ! i = (s, ABeginAtomic txi ntxnsi)"
      by (simp add: steps_step.prems(1))  
    have "i < j"
      using steps_step.prems(2) by blast
    have "j < length (tr @ [a])"
      by simp
    have "(tr @ [a]) ! j = (s, ABeginAtomic txj ntxnsj)"
      using steps_step.prems(4) by blast  
    then have "a =  (s, ABeginAtomic txj ntxnsj)"
      by simp

    have "i < length tr"
      using \<open>j = length tr\<close> steps_step.prems(2) by blast  

    have "tr ! i = (s, ABeginAtomic txi ntxnsi)"
      by (metis \<open>i < length tr\<close> nth_append steps_step.prems(1))  


    from `(tr @ [a]) ! j = (s, ABeginAtomic txj ntxnsj)` and \<open>j = length tr\<close>
    have " a = (s, ABeginAtomic txj ntxnsj)"
      by auto

    have "\<exists>k>i. k < j \<and> ((tr) ! k = (s, AEndAtomic) \<or> (tr) ! k = (s, ACrash))"
      using currentTransaction[OF \<open>S ~~ tr \<leadsto>* S'\<close> \<open>i < length tr\<close> \<open>tr ! i = (s, ABeginAtomic txi ntxnsi)\<close>] 
      using `S' ~~ a \<leadsto> S''` ` a = (s, ABeginAtomic txj ntxnsj)`
      by (auto simp add: step_simps)

    thus "\<exists>k>i. k < j \<and> ((tr @ [a]) ! k = (s, AEndAtomic) \<or> (tr @ [a]) ! k = (s, ACrash))"
      by (metis \<open>j = length tr\<close> butlast_snoc nth_butlast)

  qed      
qed  



lemma noNestedTransactions':
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and "tr!i = (s, ABeginAtomic txi ntxnsi)"
    and "i<j"
    and "j < length tr" 
    and "tr!j = (s, ABeginAtomic txj ntxnsj)"
    and "(s, ACrash) \<notin> set tr"
  shows "\<exists>k. i<k \<and> k < j \<and> tr!k = (s, AEndAtomic) "
  using noNestedTransactions[OF steps assms(2) assms(3) assms(4) assms(5) ] assms(6)
  by (metis assms(4) dual_order.strict_trans nth_mem)


lemma localState_iff_exists_invoc:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
  shows "localState C s \<noteq> None \<longrightarrow> (\<exists>p. (s, AInvoc p) \<in> set tr)"
  using invation_info_set_iff_invocation_happened(1) invocation_ops_if_localstate_nonempty steps by blast

lemma exists_invoc:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and "i < length tr"
    and "get_invoc(tr!i) = s"
    and "\<And>p. get_action(tr!i) \<noteq> AInvoc p"
    and "\<not>is_AInvcheck (get_action(tr!i))"
  shows "\<exists>j. j<i \<and> get_invoc(tr!j) = s \<and> (\<exists>p. get_action(tr!j) = AInvoc p)"    
  using assms proof (induct arbitrary: i rule: steps_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step S' tr a S'')

  from \<open>initialState program ~~ tr \<leadsto>* S'\<close>
  have "\<exists>p. (s, AInvoc p) \<in> set tr" if "localState S' s \<noteq> None" for s
    using that
    using localState_iff_exists_invoc by blast 

  then have getI: "\<exists>j p. j<length tr \<and> tr!j =(s, AInvoc p)" if "localState S' s \<triangleq> x" for s x
    by (metis in_set_conv_nth option.distinct(1) that)


  show ?case 
  proof (cases "i = length tr")
    case True
    then show ?thesis 
      using \<open>S' ~~ a \<leadsto> S''\<close> 
        \<open>get_invoc ((tr @ [a]) ! i) = s\<close>
      using step.prems(3) is_AInvcheck_def[where a="(get_action ((tr @ [a]) ! i))"] step.prems(4)
      by (auto simp add: step_simps_all nth_append_first  dest!: getI split: if_splits, fastforce)
  next
    case False
    then have "i < length tr"
      using step.prems(1) by auto

    then show ?thesis
      by (smt less_imp_le less_le_trans nth_append_first step.IH step.prems(2) step.prems(3) step.prems(4)) 
  qed
qed


lemma uid_used_only_once:
  assumes steps:  "S_start ~~ tr \<leadsto>* S_end"
    and alreadyGenerated: "generatedIds S_start (to_nat uid) \<triangleq> i'"
  shows "(i, ANewId uid) \<notin> set tr"
proof -
  have "(i, ANewId uid) \<notin> set tr \<and> generatedIds S_end  (to_nat uid) \<triangleq> i'"
    using steps alreadyGenerated proof (induct rule: steps_induct)
    case initial
    then show ?case by simp
  next
    case (step S' tr a S'')
    then show ?case using generatedIds_mono2 by (auto simp add: step_simps, blast)
  qed
  then show ?thesis by simp
qed

lemma wf_transaction_status_iff_origin:
  assumes wf: "state_wellFormed S"
  shows "(transactionStatus S t = None) \<longleftrightarrow> (transactionOrigin S t = None)"
  using wf by (induct  rule: wellFormed_induct,
   auto simp add: initialState_def step.simps wellFormed_currentTransaction_unique_h(2)  split: if_splits)



lemma callIds_unique:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "calls S cId \<noteq> None"
  shows "(s, ADbOp cId Op res) \<notin> set tr" and "calls S' cId \<noteq> None"
using steps proof (induct rule: steps_induct)
  case initial
  then show "calls S cId \<noteq> None" using \<open>calls S cId \<noteq> None\<close> .
  show "(s, ADbOp cId Op res) \<notin> set []" by simp
next
  case (step S' tr a S'')
  from step
  show "(s, ADbOp cId Op res) \<notin> set (tr @ [a])" and "calls S'' cId \<noteq> None"
    by (auto simp add: step.simps)
qed

lemma callIds_unique2:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "tr ! i = (s, ADbOp cId Op res)"
    and "i<j"
    and "j < length tr"
  shows  "tr ! j  \<noteq> (s', ADbOp cId Op' res')"
  using assms 
proof -
  have "i < length tr"
    using assms(3) assms(4) order.strict_trans by blast


  have "tr = take (Suc i) tr @ drop (Suc i) tr"
    by simp
  from this
  obtain Si 
    where "S ~~ take (Suc i) tr \<leadsto>* Si"
      and "Si ~~ drop (Suc i) tr \<leadsto>* S'"
    using steps steps_append by fastforce
  from \<open>S ~~ take (Suc i) tr \<leadsto>* Si\<close>
  obtain Si_pre where "Si_pre ~~ (s, ADbOp cId Op res) \<leadsto> Si"
    using steps_appendBack[where A=S and tr="take (Suc i) tr" and a="(s, ADbOp cId Op res)"]
      `tr ! i = (s, ADbOp cId Op res)`
      take_Suc_conv_app_nth[OF `i < length tr`]
    by (auto, insert steps_appendBack, blast)

  then have "calls Si cId \<noteq> None"
    by (auto simp add: step_simps)
  with callIds_unique[OF \<open>Si ~~ drop (Suc i) tr \<leadsto>* S'\<close>]
  have "(s', ADbOp cId Op' res') \<notin> set (drop (Suc i) tr)"
    by blast
  then show "tr ! j  \<noteq> (s', ADbOp cId Op' res')"
    by (smt Suc_leI \<open>tr = take (Suc i) tr @ drop (Suc i) tr\<close> assms(3) assms(4) in_set_conv_nth le_add_diff_inverse2 length_drop length_take less_diff_conv min_def min_less_iff_conj not_less_eq nth_append)
    
qed

lemma chooseSnapshot_committed:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a5: "\<forall>x. (c, x) \<notin> happensBefore S"
    and a2': "c \<notin> vis"
  shows "transactionStatus S tx \<triangleq> Committed"
  using a1 a2 a2' a3 a5 by (auto simp add: chooseSnapshot_def,
   auto simp add: callsInTransactionH_def downwardsClosure_def)



lemma wellFormed_state_callOrigin_transactionStatus:
assumes wf: "state_wellFormed C"
    and "callOrigin C c \<triangleq> tx"
shows "transactionStatus C tx \<noteq> None"   
using assms by (induct  rule: wellFormed_induct,
  auto simp add: initialState_def step_simps_all wellFormed_currentTransaction_unique_h split: if_splits)


lemma wellFormed_state_calls_from_current_transaction_in_vis:
assumes wf: "state_wellFormed C"
    and "callOrigin C c \<triangleq> tx"
    and "currentTransaction C s \<triangleq> tx"
    and "visibleCalls C s \<triangleq> vis"
shows "c\<in>vis"   
using assms proof (induct arbitrary: vis rule: wellFormed_induct)
  case initial
  then show ?case
    by (simp add: initialState_def) 
next
  case (step t a s)
  then show ?case
    using wellFormed_currentTransaction_unique_h(1)[OF ` state_wellFormed t`] by (auto simp add: inTransaction_localState initialState_def step_simps_all wellFormed_state_callOrigin_transactionStatus split: if_splits)
qed

lemma wellFormed_happensBefore_calls_r:
assumes wf: "state_wellFormed C"
    and "(x,c)\<in>happensBefore C"
shows "calls C c \<noteq> None"   
using wellFormed_visibleCallsSubsetCalls_h(1)[OF wf] assms by auto


lemma wellFormed_happensBefore_calls_l:
assumes wf: "state_wellFormed C"
    and "(c,x)\<in>happensBefore C"
shows "calls C c \<noteq> None"   
using wellFormed_visibleCallsSubsetCalls_h(1)[OF wf] assms by auto

lemma wellFormed_happensBefore_vis:
assumes wf: "state_wellFormed C"
    and "visibleCalls C s \<triangleq> vis"
    and "callOrigin C c1 \<noteq> Some t"
    and "c1 \<in> vis"
    and "currentTransaction C s \<triangleq> t"
    and "callOrigin C c2 \<triangleq> t"
shows "(c1,c2) \<in> happensBefore C"
using assms 
  by (induct arbitrary: c1 c2 vis t rule: wellFormed_induct,
      auto simp add: initialState_def step_simps_all wellFormed_state_callOrigin_transactionStatus wellFormed_visibleCallsSubsetCalls2  wellFormed_currentTransaction_unique  split: if_splits)

lemma wellFormed_happensBefore_Field:
assumes wf: "state_wellFormed C"
    and "calls C c = None"
  shows "c \<notin> Field (happensBefore C)"   
  using wellFormed_happensBefore_calls_l[OF wf]
 wellFormed_happensBefore_calls_r[OF wf]
assms  by (auto simp add: Field_def, blast+)


lemma chooseSnapshot_committed2:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a5: "\<And>c c' tx tx'. \<lbrakk>(c', c) \<in> happensBefore S; callOrigin S c \<triangleq> tx; callOrigin S c' \<triangleq> tx'; transactionStatus S tx \<triangleq> Committed\<rbrakk> \<Longrightarrow> transactionStatus S tx' \<triangleq> Committed"
    and a2': "c \<notin> vis"
  shows "transactionStatus S tx \<triangleq> Committed"
  using a1 a2 a2' a3 a5 by (auto simp add: chooseSnapshot_def callsInTransactionH_def downwardsClosure_def)

lemma chooseSnapshot_transactionConsistent:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a4: "callOrigin S c' \<triangleq> tx"
    and a5: "\<And>c c'. \<lbrakk>c\<in>vis; callOrigin S c \<triangleq> tx; callOrigin S c' \<triangleq> tx\<rbrakk> \<Longrightarrow> c' \<in> vis "
    and a6: "\<And>c ca cb tx tx'. \<lbrakk>(ca,c)\<in>happensBefore S; callOrigin S c \<triangleq> tx; callOrigin S ca \<triangleq> tx'; callOrigin S cb \<triangleq> tx'; tx\<noteq>tx' \<rbrakk> \<Longrightarrow> (cb,c)\<in>happensBefore S"
  shows "c' \<in> snapshot"
  using a1 a2 a3 a4 a5 
  by (auto simp add: chooseSnapshot_def callsInTransactionH_def downwardsClosure_def,
      insert a6, blast)


declare length_dropWhile_le[simp]  


lemma state_wellFormed_ls_visibleCalls:     
  assumes "state_wellFormed S"
  shows "localState S s = None \<longleftrightarrow> visibleCalls S s = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S')
  show ?case 
    by (rule step.cases[OF `S ~~ a \<leadsto> S'`],
        insert `(localState S s = None) = (visibleCalls S s = None)` `get_action a \<noteq> ACrash`,
        auto)

qed


lemma state_wellFormed_ls_to_visibleCalls:     
  assumes "state_wellFormed S"
    and "currentTransaction S s \<triangleq> tx"
  shows "localState S s \<noteq> None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S')


  from `S ~~ a \<leadsto> S'`
  show ?case
    by (rule step.cases, 
        insert  `currentTransaction S' s \<triangleq> tx` ` get_action a \<noteq> ACrash` `currentTransaction S s \<triangleq> tx \<Longrightarrow> localState S s \<noteq> None`,
        auto split: if_splits)
qed

lemma state_wellFormed_tx_to_visibleCalls:     
  assumes wf: "state_wellFormed S"
    and "currentTransaction S s \<triangleq> tx"
  shows "visibleCalls S s \<noteq> None"
  using assms state_wellFormed_ls_to_visibleCalls[OF wf] state_wellFormed_ls_visibleCalls[OF wf] by auto

lemma state_wellFormed_invocation_before_result:
  assumes "state_wellFormed C"
    and "invocationOp C s = None"
  shows "invocationRes C s = None"    
  using assms by (induct arbitrary:  rule: wellFormed_induct,
      auto simp add: initialState_def step_simps_all wellFormed_invoc_notStarted(2) split: if_splits)


lemma state_wellFormed_no_result_when_running:     
  assumes "state_wellFormed C"
    and "localState C s \<triangleq> ls" 
  shows "invocationRes C s = None"   
  using assms by (induct arbitrary: ls rule: wellFormed_induct,
      auto simp add: initialState_def step_simps_all state_wellFormed_invocation_before_result split: if_splits)



lemma not_uncommitted_cases:
  shows "(x \<noteq> Some Uncommitted) \<longleftrightarrow> (\<forall>y. x = Some y \<longrightarrow> x = Some Committed)"
  using transactionStatus.exhaust by auto





lemma happensBefore_in_calls_left:
assumes wf: "state_wellFormed S"
    and "(x,y)\<in>happensBefore S"
shows "x\<in>dom (calls S)"
using assms  by (induct rule: wellFormed_induct, 
  auto simp add: initialState_def step_simps_all,
  meson domD domIff wellFormed_visibleCallsSubsetCalls2)

lemma happensBefore_in_calls_right:
assumes wf: "state_wellFormed S"
    and "(x,y)\<in>happensBefore S"
shows "y\<in>dom (calls S)"
using assms  by (induct rule: wellFormed_induct,
 auto simp add: initialState_def step_simps_all)




lemma currentTransaction_exists_beginAtomic:
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and inTx: "currentTransaction S' i \<triangleq> tx"
    and noTx: "currentTransaction S i = None"
    and wf: "state_wellFormed S"
    and noFails: "\<And>i. (i, ACrash) \<notin> set tr"
  shows "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
  using steps inTx noFails proof (induct arbitrary: tx rule: steps_induct)
  case initial
  then show ?case
    by (simp add: noTx)

next
  case (step S' tr a S'')

  from step 
  have IH: "\<lbrakk>currentTransaction S' i \<triangleq> tx\<rbrakk> \<Longrightarrow> \<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))" for tx
    by auto


  from \<open> S' ~~ a \<leadsto> S''\<close>
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ok ls')
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  local)
      show "\<And>i. (i, ACrash) \<notin> set tr"
        using step.prems(2) by auto

    qed

    then show ?thesis
      using \<open>a = (s, ALocal ok)\<close> by (auto simp add: nth_append)

  next
    case (newId s ls f ls' uidv uid)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  newId)
      show "\<And>i. (i, ACrash) \<notin> set tr"
        using step.prems(2) by auto
    qed

    then show ?thesis
      using \<open>a = (s, ANewId uid)\<close> by (auto simp add: nth_append)
  next
    case (beginAtomic s ls f ls' t vis snapshot)
    show ?thesis 
    proof (cases "t=tx")
      case True
      then have "s = i"
        using local.beginAtomic(1) local.beginAtomic(7) local.wf state_wellFormed_combine step.prems step.step step.steps unchangedInTransaction(3)
        by (metis Un_insert_right append_Nil2 insert_iff list.simps(15) not_None_eq set_append wellFormed_currentTransaction_unique_h(2))

      show ?thesis 
        using beginAtomic by (auto simp add: nth_append True \<open>s = i\<close>)
    next
      case False

      have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
      proof (rule step)
        show "currentTransaction S' i \<triangleq> tx"
          using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: False  beginAtomic split: if_splits)
        show " \<And>i. (i, ACrash) \<notin> set tr"
          using step.prems(2) by auto

      qed

      then show ?thesis
        using \<open>a = (s, ABeginAtomic t snapshot)\<close> by (auto simp add: nth_append split: if_splits)
    qed
  next
    case (endAtomic s ls f ls' t)

    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: endAtomic split: if_splits)
    qed

    then show ?thesis 
      using endAtomic \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: nth_append)

  next
    case (dbop s ls f Op  ls' t c res vis)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  dbop)
    qed

    then show ?thesis
      using \<open>a = (s, ADbOp c Op  res)\<close> by (auto simp add: nth_append)
  next
    case (invocation s procName initialState impl)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  invocation)
    qed

    then show ?thesis
      using invocation by (auto simp add: nth_append)
  next
    case (return s ls f res)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  return)
    qed

    then show ?thesis
      using return by (auto simp add: nth_append)
  next
    case (fail s ls)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> 
        by (auto simp add:  fail split: if_splits)
    qed

    then show ?thesis
      using fail by (auto simp add: nth_append)
  next
    case (invCheck res s)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  invCheck)
    qed

    then show ?thesis
      using invCheck by (auto simp add: nth_append)
  qed
qed


lemma no_steps_in_i:
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and no_invoc: "invocationOp S' i = None"
    and a_from_tr: "a \<in> set tr"
and wf: "state_wellFormed S"
and noCrash: "\<And>i. (i, ACrash) \<notin> set tr"
and noInvcheck: "\<And>i r. (i, AInvcheck r) \<notin> set tr" 
shows "get_invoc a \<noteq> i"
 using assms proof (induct  rule: steps_induct)
case initial
  then show ?case 
    by simp
next
  case (step S' tr a S'')
  then show ?case
    by (auto simp add: step.simps state_wellFormed_combine wf_localState_to_invocationOp split: if_splits)

qed

end
