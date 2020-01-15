theory state_monotonicGrowth_invariants
imports commutativity
    repliss_sem_single_invocation
    consistency
    packed_nofails_noinvchecks
    single_invocation_reduction_helper
begin


lemma state_monotonicGrowth_localState:
  assumes "state_monotonicGrowth i S S'"
  shows "localState S i = localState S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)

  show "localState S i = localState S' i"
    if c0: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps no_i by (induct rule: steps.induct, auto simp add: step.simps)
qed



lemma state_monotonicGrowth_currentProc:
  assumes "state_monotonicGrowth i S S'"
  shows "currentProc S i = currentProc S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)

  show "currentProc S i = currentProc S' i"
    if c0: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps no_i by (induct rule: steps.induct, auto simp add: step.simps)
qed


lemma state_monotonicGrowth_currentTransaction:
  assumes "state_monotonicGrowth i S S'"
  shows "currentTransaction S i = currentTransaction S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)

  show "currentTransaction S i = currentTransaction S' i"
    if c0: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps no_i by (induct rule: steps.induct, auto simp add: step.simps)
qed


lemma state_monotonicGrowth_visibleCalls:
  assumes "state_monotonicGrowth i S S'"
  shows "visibleCalls S i = visibleCalls S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)

  show "visibleCalls S i = visibleCalls S' i"
    if c0: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps no_i by (induct rule: steps.induct, auto simp add: step.simps)
qed


lemma state_monotonicGrowth_transactionOrigin_i:
  assumes "state_monotonicGrowth i S S'"
  shows "transactionOrigin S' t \<triangleq> i \<longleftrightarrow> transactionOrigin S t \<triangleq> i"
  using assms proof (simp add: state_monotonicGrowth_def, elim conjE exE)

  show "transactionOrigin S' t \<triangleq> i \<longleftrightarrow> transactionOrigin S t \<triangleq> i"
    if wf: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps wf no_i by (induct rule: steps.induct, 
        auto simp add: step.simps split: if_splits,
        metis less_eq_option_None_is_None option.distinct(1) transactionStatus_mono wf_transaction_status_iff_origin)


qed


lemma state_monotonicGrowth_refl: "state_wellFormed S \<Longrightarrow> state_monotonicGrowth i S S"
  by (auto simp add: state_monotonicGrowth_def exI[where x="[]"] steps_empty)


lemma state_monotonicGrowth_step: 
  assumes "state_wellFormed S"
    and "state_monotonicGrowth i S S'"
    and "S' ~~ (i',a) \<leadsto> S''"
    and "i' \<noteq> i"
    and "a \<noteq> ACrash"
  shows "state_monotonicGrowth i S S''"
  using assms proof (auto simp add: state_monotonicGrowth_def, goal_cases G )
  case (G tr)
  then show ?case
    by (auto simp add: steps_step intro!: exI[where x="tr@[(i',a)]"])
qed
  


lemma state_monotonicGrowth_wf1: 
  assumes "state_monotonicGrowth i S' S"
  shows "state_wellFormed S'"
    using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_wf2: 
  assumes "state_monotonicGrowth i  S' S"
  shows "state_wellFormed S"
  using assms state_wellFormed_combine by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_no_new_calls_before_existing1:
  assumes "state_monotonicGrowth i S' S"
    and "c2\<in>dom (calls S')"
  shows "(c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'"
  using assms no_new_calls_before_existing_h state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_no_new_calls_before_existing: 
  assumes "state_monotonicGrowth i S' S"
    and "calls S' c = None"
    and "calls S c \<triangleq> x"
    and "calls S' c' \<triangleq> y"
  shows "(c,c') \<notin> happensBefore S'"
  using assms
  by (meson domIff mem_Sigma_iff rev_subsetD state_monotonicGrowth_wf1 wellFormed_visibleCallsSubsetCalls_h(1)) 

lemma state_monotonicGrowth_no_new_calls_in_committed_transactions: 
  assumes "state_monotonicGrowth i S' S"
    and "callOrigin S c \<triangleq> tx"
    and "calls S' c = None"
  shows "transactionStatus S' tx \<noteq> Some Committed"
  using assms by (auto simp add: state_monotonicGrowth_def no_new_calls_in_committed_transactions)

lemma state_monotonicGrowth_transactionOrigin: 
  assumes "state_monotonicGrowth i S' S" 
    and "transactionOrigin S' t \<triangleq> i'"
  shows "transactionOrigin S t \<triangleq> i'"
  using assms by (auto simp add: state_monotonicGrowth_def transactionOrigin_mono)


lemma state_monotonicGrowth_calls:
  assumes "state_monotonicGrowth i S' S"
  shows "calls S' c \<triangleq> info \<Longrightarrow> calls S c \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def calls_mono)

lemma state_monotonicGrowth_happensBefore:
  assumes "state_monotonicGrowth i S' S"
  shows "c2\<in>dom (calls S') \<Longrightarrow> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S')"
  using assms by (auto simp add: state_monotonicGrowth_def domIff no_new_calls_before_existing)

lemma state_monotonicGrowth_callOrigin:
  assumes "state_monotonicGrowth i S' S"
  shows "callOrigin S' c \<triangleq> t \<Longrightarrow> callOrigin S c \<triangleq> t"
  using assms by (auto simp add: state_monotonicGrowth_def callOrigin_mono)

lemma state_monotonicGrowth_callOrigin2:
  assumes "state_monotonicGrowth i S' S"
  shows "callOrigin S c = None \<Longrightarrow> callOrigin S' c = None"
  using assms domIff state_monotonicGrowth_callOrigin by fastforce 

lemma state_monotonicGrowth_generatedIds:
  assumes "state_monotonicGrowth i S' S"
  shows "generatedIds S' uid \<triangleq> j \<Longrightarrow> generatedIds S uid \<triangleq> j"
  using assms generatedIds_mono1 state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_generatedIds_same1:
  assumes "state_monotonicGrowth i S' S"
  shows "generatedIds S' uid \<triangleq> i \<longleftrightarrow> generatedIds S uid \<triangleq> i"
  using assms generatedIds_mono1_self state_monotonicGrowth_def by fastforce
  

lemma state_monotonicGrowth_knownIds:
  assumes "state_monotonicGrowth i S' S"
  shows "knownIds S' \<subseteq> knownIds S"
  using assms by (auto simp add: state_monotonicGrowth_def knownIds_mono2)


lemma state_monotonicGrowth_invocationOp:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationOp S' s \<triangleq> info \<Longrightarrow> invocationOp S s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_invocationOp)

lemma state_monotonicGrowth_invocationOp_i:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationOp S i = invocationOp S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)
  fix tr
  assume a0: "state_wellFormed S'"
    and steps: "S' ~~ tr \<leadsto>* S"
    and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
    and a3: "\<forall>i. (i, ACrash) \<notin> set tr"

  from steps no_i
  show "invocationOp S i = invocationOp S' i"
    by (induct rule: steps.induct, auto simp add: step.simps)
qed

lemma state_monotonicGrowth_invocationRes:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationRes S' s \<triangleq> info \<Longrightarrow> invocationRes S s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def invocationRes_mono)

lemma state_monotonicGrowth_transactionStatus:
  assumes "state_monotonicGrowth i S' S"
  shows "transactionStatus S' tx \<le> transactionStatus S tx"
  using assms by (auto simp add: state_monotonicGrowth_def transactionStatus_mono)

lemma state_monotonicGrowth_transactionStatus2:
  assumes "state_monotonicGrowth i S' S"
  shows "transactionStatus S' tx \<triangleq> Committed \<Longrightarrow>  transactionStatus S tx \<triangleq> Committed"
  using assms by (auto simp add: state_monotonicGrowth_def transactionStatus_mono1)


lemma state_monotonicGrowth_prog:
  assumes "state_monotonicGrowth i S' S"
  shows "prog S = prog S'"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_prog)

lemma state_monotonicGrowth_invocationOp2:
  assumes "state_monotonicGrowth i S' S"
  shows "(invocationOp S' \<subseteq>\<^sub>m invocationOp S) "
  using assms by (auto simp add: map_le_def state_monotonicGrowth_def invocationOp_mono)

lemma state_monotonicGrowth_committed_transactions_fixed:
  assumes "state_monotonicGrowth i S' S"
and "transactionStatus S' tx \<triangleq> Committed"
and "callOrigin S x \<triangleq> tx"
shows "callOrigin S' x \<triangleq> tx"
proof -
  have "x \<in> dom (callOrigin S')"
    by (meson assms(1) assms(2) assms(3) domIff state_monotonicGrowth_no_new_calls_in_committed_transactions state_monotonicGrowth_wf1 wellFormed_callOrigin_dom3)
  then show ?thesis
    by (metis (no_types) assms(1) assms(3) domD state_monotonicGrowth_callOrigin)
qed 
  

lemma state_monotonicGrowth_committed_transactions_fixed1:
  assumes "state_monotonicGrowth i S' S"
  shows "state_monotonicGrowth_txStable (callOrigin S) (callOrigin S') (transactionStatus S')"
  using assms  apply (auto simp add: state_monotonicGrowth_def state_monotonicGrowth_txStable_def)
  using assms state_monotonicGrowth_committed_transactions_fixed by blast


lemma state_monotonicGrowth_committed_transactions_fixed2:
  assumes "state_monotonicGrowth i S' S"
and "transactionStatus S' tx \<triangleq> Committed"
shows "{c. callOrigin S' c \<triangleq> tx} = {c. callOrigin S c \<triangleq> tx}"
  using assms state_monotonicGrowth_callOrigin state_monotonicGrowth_committed_transactions_fixed by blast


schematic_goal show_state_monotonicGrowth: "?X \<Longrightarrow> state_monotonicGrowth i S S'"
  apply (unfold state_monotonicGrowth_def)
  apply assumption
  done



lemmas state_monotonicGrowth_lemmas = 
state_monotonicGrowth_calls
state_monotonicGrowth_happensBefore
state_monotonicGrowth_callOrigin
state_monotonicGrowth_callOrigin2
state_monotonicGrowth_generatedIds
state_monotonicGrowth_knownIds
state_monotonicGrowth_invocationOp
state_monotonicGrowth_invocationRes
state_monotonicGrowth_transactionStatus
state_monotonicGrowth_prog
state_monotonicGrowth_invocationOp2
state_monotonicGrowth_committed_transactions_fixed
state_monotonicGrowth_committed_transactions_fixed1
state_monotonicGrowth_committed_transactions_fixed2
state_monotonicGrowth_wf1 
state_monotonicGrowth_wf2
state_monotonicGrowth_no_new_calls_before_existing
state_monotonicGrowth_no_new_calls_in_committed_transactions
state_monotonicGrowth_transactionOrigin
state_monotonicGrowth_localState
state_monotonicGrowth_currentProc
state_monotonicGrowth_currentTransaction
state_monotonicGrowth_visibleCalls
state_monotonicGrowth_transactionOrigin_i

end