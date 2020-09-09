theory state_monotonicGrowth_invariants
  imports commutativity
    repliss_sem_single_invocation
    consistency
    (*    packed_nofails_noinvchecks*)
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


lemma state_monotonicGrowth_currentTx:
  assumes "state_monotonicGrowth i S S'"
  shows "currentTx S i = currentTx S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)

  show "currentTx S i = currentTx S' i"
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


lemma state_monotonicGrowth_txOrigin_i:
  assumes "state_monotonicGrowth i S S'"
  shows "txOrigin S' t \<triangleq> i \<longleftrightarrow> txOrigin S t \<triangleq> i"
  using assms proof (simp add: state_monotonicGrowth_def, elim conjE exE)

  show "txOrigin S' t \<triangleq> i \<longleftrightarrow> txOrigin S t \<triangleq> i"
    if wf: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and c3: "\<forall>i. (i, ACrash) \<notin> set tr"
    for  tr
    using steps wf no_i by (induct rule: steps.induct, 
        auto simp add: step.simps split: if_splits,
        metis less_eq_option_None_is_None option.distinct(1) txStatus_mono wf_transaction_status_iff_origin)


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
  using assms proof (auto simp add: state_monotonicGrowth_def, fuzzy_goal_cases G )
  case (G tr)
  then show ?case
    by (auto simp add: steps_step intro!: exI[where x="tr@[(i',a)]"])
qed



lemma state_monotonicGrowth_wf1: 
  assumes "state_monotonicGrowth i S S'"
  shows "state_wellFormed S"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_wf2: 
  assumes "state_monotonicGrowth i  S' S"
  shows "state_wellFormed S"
  using assms state_wellFormed_combine by (auto simp add: state_monotonicGrowth_def)


text_raw \<open>\DefineSnippet{state_monotonicGrowth_no_new_calls_before_existing1}{\<close>
lemma state_monotonicGrowth_no_new_calls_before_existing1:
  assumes "state_monotonicGrowth i S S'"
    and "c2\<in>dom (calls S)"
  shows "(c1,c2)\<in>happensBefore S' \<longleftrightarrow> (c1,c2)\<in>happensBefore S"
  text_raw \<open>}%EndSnippet\<close>
  using assms no_new_calls_before_existing_h state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_no_new_calls_before_existing: 
  assumes "state_monotonicGrowth i S S'"
    and "calls S c = None"
    and "calls S' c \<triangleq> x"
    and "calls S c' \<triangleq> y"
  shows "(c,c') \<notin> happensBefore S"
  using assms
  by (meson domIff mem_Sigma_iff rev_subsetD state_monotonicGrowth_wf1 wellFormed_visibleCallsSubsetCalls_h(1)) 

text_raw \<open>\DefineSnippet{state_monotonicGrowth_no_new_calls_in_committed_transactions}{\<close>
lemma state_monotonicGrowth_no_new_calls_in_committed_transactions: 
  assumes "state_monotonicGrowth i S S'"
    and "callOrigin S' c \<triangleq> tx"
    and "calls S c = None"
  shows "txStatus S tx \<noteq> Some Committed"
  text_raw \<open>}%EndSnippet\<close>

  using assms by (auto simp add: state_monotonicGrowth_def no_new_calls_in_committed_transactions)

lemma state_monotonicGrowth_txOrigin: 
  assumes "state_monotonicGrowth i S S'" 
    and "txOrigin S t \<triangleq> i'"
  shows "txOrigin S' t \<triangleq> i'"
  using assms by (auto simp add: state_monotonicGrowth_def txOrigin_mono)


text_raw \<open>\DefineSnippet{state_monotonicGrowth_calls}{\<close>
lemma state_monotonicGrowth_calls:
  assumes "state_monotonicGrowth i S S'"
shows "calls S c \<triangleq> info \<Longrightarrow> calls S' c \<triangleq> info"
  text_raw \<open>}%EndSnippet\<close>
  using assms by (auto simp add: state_monotonicGrowth_def calls_mono)

text_raw \<open>\DefineSnippet{state_monotonicGrowth_calls2}{\<close>
lemma state_monotonicGrowth_calls2:
  assumes "state_monotonicGrowth i S S'"
  shows "calls S' c = None \<Longrightarrow> calls S c = None"
  text_raw \<open>}%EndSnippet\<close>
  using assms callIds_unique(2) state_monotonicGrowth_def by blast 

text_raw \<open>\DefineSnippet{state_monotonicGrowth_happensBefore}{\<close>
lemma state_monotonicGrowth_happensBefore:
  assumes "state_monotonicGrowth i S S'"
  shows "c2\<in>dom (calls S) \<Longrightarrow> ((c1,c2)\<in>happensBefore S' \<longleftrightarrow> (c1,c2)\<in>happensBefore S)"
  text_raw \<open>}%EndSnippet\<close>
  using assms by (auto simp add: state_monotonicGrowth_def domIff no_new_calls_before_existing)

text_raw \<open>\DefineSnippet{state_monotonicGrowth_callOrigin}{\<close>
lemma state_monotonicGrowth_callOrigin:
  assumes "state_monotonicGrowth i S S'"
    and "callOrigin S c \<triangleq> t" 
  shows "callOrigin S' c \<triangleq> t"
  text_raw \<open>}%EndSnippet\<close>
  using assms by (auto simp add: state_monotonicGrowth_def callOrigin_mono)

lemma state_monotonicGrowth_callOrigin2:
  assumes "state_monotonicGrowth i S S'"
  shows "callOrigin S' c = None \<Longrightarrow> callOrigin S c = None"
  using assms domIff state_monotonicGrowth_callOrigin by fastforce 

lemma state_monotonicGrowth_generatedIds:
  assumes "state_monotonicGrowth i S S'"
  shows "generatedIds S uid \<triangleq> j \<Longrightarrow> generatedIds S' uid \<triangleq> j"
  using assms generatedIds_mono1 state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_generatedIds_same1:
  assumes "state_monotonicGrowth i S S'"
  shows "generatedIds S uid \<triangleq> i \<longleftrightarrow> generatedIds S' uid \<triangleq> i"
  using assms generatedIds_mono1_self state_monotonicGrowth_def
  by (smt case_prodD)


lemma state_monotonicGrowth_knownIds:
  assumes "state_monotonicGrowth i S S'"
  shows "knownIds S \<subseteq> knownIds S'"
  using assms by (auto simp add: state_monotonicGrowth_def knownIds_mono2)


lemma state_monotonicGrowth_invocOp:
  assumes "state_monotonicGrowth i S S'"
  shows "invocOp S s \<triangleq> info \<Longrightarrow> invocOp S' s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_invocOp)

lemma state_monotonicGrowth_invocOp_i:
  assumes "state_monotonicGrowth i S S'"
  shows "invocOp S' i = invocOp S i"
  using assms proof (auto simp add: state_monotonicGrowth_def)
  fix tr
  assume a0: "state_wellFormed S"
    and steps: "S ~~ tr \<leadsto>* S'"
    and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
    and a3: "\<forall>i. (i, ACrash) \<notin> set tr"

  from steps no_i
  show "invocOp S' i = invocOp S i"
    by (induct rule: steps.induct, auto simp add: step.simps)
qed

lemma state_monotonicGrowth_invocRes:
  assumes "state_monotonicGrowth i S S'"
  shows "invocRes S s \<triangleq> info \<Longrightarrow> invocRes S' s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def invocRes_mono)

lemma state_monotonicGrowth_invocRes_i:
  assumes "state_monotonicGrowth i S S'"
  shows "invocRes S i = invocRes S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)
  fix tr
  assume a0: "state_wellFormed S"
    and steps: "S ~~ tr \<leadsto>* S'"
    and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
    and a3: "\<forall>i. (i, ACrash) \<notin> set tr"

  from steps no_i
  show "invocRes S i = invocRes S' i"
    by (induct rule: steps.induct, auto simp add: step.simps)
qed



lemma state_monotonicGrowth_txStatus:
  assumes "state_monotonicGrowth i S S'"
  shows "txStatus S tx \<le> txStatus S' tx"
  using assms by (auto simp add: state_monotonicGrowth_def txStatus_mono)

lemma state_monotonicGrowth_txStatus2:
  assumes "state_monotonicGrowth i S S'"
  shows "txStatus S tx \<triangleq> Committed \<Longrightarrow>  txStatus S' tx \<triangleq> Committed"
  using assms by (auto simp add: state_monotonicGrowth_def txStatus_mono1)


lemma state_monotonicGrowth_prog:
  assumes "state_monotonicGrowth i S S'"
  shows "prog S' = prog S"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_prog)

lemma state_monotonicGrowth_invocOp2:
  assumes "state_monotonicGrowth i S S'"
  shows "(invocOp S \<subseteq>\<^sub>m invocOp S') "
  using assms by (auto simp add: map_le_def state_monotonicGrowth_def invocOp_mono)

lemma state_monotonicGrowth_committed_transactions_fixed:
  assumes "state_monotonicGrowth i S S'"
    and "txStatus S tx \<triangleq> Committed"
    and "callOrigin S' x \<triangleq> tx"
  shows "callOrigin S x \<triangleq> tx"
proof -
  have "x \<in> dom (callOrigin S)"
    by (meson assms(1) assms(2) assms(3) domIff state_monotonicGrowth_no_new_calls_in_committed_transactions state_monotonicGrowth_wf1 wellFormed_callOrigin_dom3)
  then show ?thesis
    by (metis (no_types) assms(1) assms(3) domD state_monotonicGrowth_callOrigin)
qed 


lemma state_monotonicGrowth_committed_transactions_fixed1:
  assumes "state_monotonicGrowth i S S'"
  shows "state_monotonicGrowth_txStable (callOrigin S') (callOrigin S) (txStatus S)"
  using assms  apply (auto simp add: state_monotonicGrowth_def state_monotonicGrowth_txStable_def)
  using assms state_monotonicGrowth_committed_transactions_fixed by blast


lemma state_monotonicGrowth_committed_transactions_fixed2:
  assumes "state_monotonicGrowth i S S'"
    and "txStatus S tx \<triangleq> Committed"
  shows "{c. callOrigin S c \<triangleq> tx} = {c. callOrigin S' c \<triangleq> tx}"
  using assms state_monotonicGrowth_callOrigin state_monotonicGrowth_committed_transactions_fixed by blast

lemma state_monotonicGrowth_current_transactions_fixed:
  assumes "state_monotonicGrowth i S S'"
    and "currentTx S' i \<triangleq> tx"
  shows "callOrigin S' c \<triangleq> tx \<longleftrightarrow> callOrigin S c \<triangleq> tx"
proof
  show "callOrigin S c \<triangleq> tx \<Longrightarrow> callOrigin S' c \<triangleq> tx"
    using assms(1) state_monotonicGrowth_callOrigin by blast
  show "callOrigin S c \<triangleq> tx" if "callOrigin S' c \<triangleq> tx"
    using `state_monotonicGrowth i S S'` proof (clarsimp simp add: state_monotonicGrowth_def)
    fix tr
    assume a0: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and a3: "\<forall>i. (i, ACrash) \<notin> set tr"


    from steps no_i `callOrigin S' c \<triangleq> tx`
    show "callOrigin S c \<triangleq> tx"
    proof (induct rule: steps_induct)
      case initial
      then show ?case
        by simp
    next
      case (step Sa tr' action Sb)

      show ?case
      proof (rule classical)
        assume "callOrigin S c \<noteq> Some tx"

        have "callOrigin Sa c \<noteq> Some tx"
          using \<open>callOrigin S c \<noteq> Some tx\<close> step.IH step.prems(1) by auto


        from `Sa ~~ action \<leadsto> Sb`
        have "callOrigin Sb c \<noteq> Some tx"
        proof (cases rule: step.cases)
          case (dbop i' ls f Op ls' t c' res vis)
          then show ?thesis  using \<open>callOrigin Sa c \<noteq> Some tx\<close> proof (auto, fuzzy_goal_cases)
            case 1
            show "?case"
              by (metis \<open>callOrigin S c \<noteq> Some tx\<close> a0 assms(1) assms(2) not_Some_eq state_monotonicGrowth_callOrigin state_monotonicGrowth_currentTx state_monotonicGrowth_visibleCalls state_monotonicGrowth_wf2 state_wellFormed_tx_to_visibleCalls that wellFormed_callOrigin_dom3 wellFormed_state_calls_from_current_transaction_in_vis wellFormed_visibleCallsSubsetCalls2)
          qed
        qed (insert \<open>callOrigin Sa c \<noteq> Some tx\<close>, auto)
        thus ?thesis
          using `callOrigin Sb c \<triangleq> tx` by blast
      qed
    qed
  qed
qed


text_raw \<open>\DefineSnippet{state_monotonicGrowth_callOrigin_unchanged}{\<close>
lemma state_monotonicGrowth_callOrigin_unchanged:
  assumes "state_monotonicGrowth i S S'"
    and "calls S c \<noteq> None"
  shows "callOrigin S c \<triangleq> tx \<longleftrightarrow> callOrigin S' c \<triangleq> tx"
  text_raw \<open>}%EndSnippet\<close>
  using assms by (metis domD domIff state_monotonicGrowth_callOrigin state_monotonicGrowth_wf1 wellFormed_callOrigin_dom3)

text_raw \<open>\DefineSnippet{state_monotonicGrowth_transactionOrigin}{\<close>
lemma state_monotonicGrowth_transactionOrigin:
  assumes "state_monotonicGrowth i S S'"
    and "txOrigin S t \<noteq> None"
  shows "txOrigin S t \<triangleq> i' \<longleftrightarrow> txOrigin S' t \<triangleq> i'"
  text_raw \<open>}%EndSnippet\<close>
  using assms state_monotonicGrowth_txOrigin by fastforce

text_raw \<open>\DefineSnippet{state_monotonicGrowth_invocOp_unchanged}{\<close>
lemma state_monotonicGrowth_invocOp_unchanged:
  assumes "state_monotonicGrowth i S S'"
    and "invocOp S i' \<noteq> None"
  shows "invocOp S i' = invocOp S' i'"
  text_raw \<open>}%EndSnippet\<close>
  using assms state_monotonicGrowth_invocOp by fastforce

text_raw \<open>\DefineSnippet{state_monotonicGrowth_invocRes_unchanged}{\<close>
lemma state_monotonicGrowth_invocRes_unchanged:
  assumes "state_monotonicGrowth i S S'"
    and "invocRes S i' \<noteq> None"
  shows "invocRes S i' = invocRes S' i'"
  text_raw \<open>}%EndSnippet\<close>
  using assms state_monotonicGrowth_invocRes by fastforce




lemma show_state_monotonicGrowth:
  assumes "S ~~ tr \<leadsto>* S'"
    and "state_wellFormed S"
    and "\<And>a. (i, a) \<notin> set tr"
    and "\<And>i. (i, ACrash) \<notin> set tr"
  shows "state_monotonicGrowth i S S'"
  using assms  unfolding state_monotonicGrowth_def by auto


lemmas state_monotonicGrowth_lemmas = 
  state_monotonicGrowth_calls
  state_monotonicGrowth_happensBefore
  state_monotonicGrowth_callOrigin
  state_monotonicGrowth_callOrigin2
  state_monotonicGrowth_generatedIds
  state_monotonicGrowth_knownIds
  state_monotonicGrowth_invocOp
  state_monotonicGrowth_invocRes
  state_monotonicGrowth_txStatus
  state_monotonicGrowth_prog
  state_monotonicGrowth_invocOp2
  state_monotonicGrowth_committed_transactions_fixed
  state_monotonicGrowth_committed_transactions_fixed1
  state_monotonicGrowth_committed_transactions_fixed2
  state_monotonicGrowth_wf1 
  state_monotonicGrowth_wf2
  state_monotonicGrowth_no_new_calls_before_existing
  state_monotonicGrowth_no_new_calls_in_committed_transactions
  state_monotonicGrowth_txOrigin
  state_monotonicGrowth_localState
  state_monotonicGrowth_currentProc
  state_monotonicGrowth_currentTx
  state_monotonicGrowth_visibleCalls
  state_monotonicGrowth_txOrigin_i


find_theorems state_monotonicGrowth calls

end