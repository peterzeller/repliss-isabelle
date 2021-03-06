section "Execution Invariants (Part 3)"
theory execution_invariants_unused
  imports repliss_sem execution_invariants consistency commutativity  invariant_simps
begin


text "These are execution invariants not needed for the soundness proof, but which still
 might be useful for verifying some applications."




lemma causallyConsistent_downwards_closure:
assumes wf: "state_wellFormed S"
shows "causallyConsistent (happensBefore S) (cs \<down> happensBefore S)"
apply (auto simp add: causallyConsistent_def downwardsClosure_def)
  by (meson local.wf transD wellFormed_state_causality(2))



lemma consistentSnapshot_txns:
assumes wf: "state_wellFormed S"
  and comitted: "txns \<subseteq> committedTransactions S"
shows "consistentSnapshot S (callsInTransaction S txns \<down> happensBefore S)"
unfolding consistentSnapshotH_def proof (intro conjI)
 
  show "callsInTransaction S txns \<down> happensBefore S \<subseteq> dom (calls S)"
    apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
    using local.wf wellFormed_callOrigin_dom2 apply fastforce
    by (simp add: domD happensBefore_in_calls_left local.wf)
    
  show "causallyConsistent (happensBefore S) (callsInTransaction S txns \<down> happensBefore S)"
    apply (auto simp add: callsInTransactionH_def downwardsClosure_def causallyConsistent_def)
    by (meson happensBefore_transitive local.wf transD)
    
  show "transactionConsistent (callOrigin S) (txStatus S) (callsInTransaction S txns \<down> happensBefore S)"
  proof (induct rule: show_transactionConsistent)
    case (only_committed c tx)
    then show ?case 
      apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
      using comitted apply blast
      using comitted local.wf wellFormed_state_transaction_consistent(4) by fastforce
  next
    case (all_from_same c1 c2)
    then show ?case 
      apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
      by (metis local.wf wellFormed_state_transaction_consistent(3))
  qed
qed    





lemma wellFormed_visibleCallsSubsetCalls:
  assumes a1: "state_wellFormed A"
    and a2: "visibleCalls A s \<triangleq> vis"
  shows "vis \<subseteq> dom (calls A)"
  using a1 a2 wellFormed_visibleCallsSubsetCalls_h(2) by blast



lemma wf_current_tx_not_before_others: 
  assumes wf: "state_wellFormed S"
    and "visibleCalls S i \<triangleq> Vis"
    and "currentTx S i \<triangleq> tx"
    and "callOrigin S x \<triangleq> tx"
    and "callOrigin S y \<noteq> Some tx"
  shows "(x,y) \<notin> happensBefore S"
proof -
  obtain tt :: "(callId \<Rightarrow> txId option) \<Rightarrow> callId \<Rightarrow> txId" where
    "\<forall>x0 x1. (\<exists>v2. x0 x1 \<triangleq> v2) = x0 x1 \<triangleq> tt x0 x1"
    by moura
  then have "\<forall>c f. c \<notin> dom f \<or> f c \<triangleq> tt f c"
    by blast
  then have "(x, y) \<notin> happensBefore S \<or> y \<notin> dom (callOrigin S)"
    by (metis (no_types) assms(3) assms(4) assms(5) local.wf option.inject txStatus.distinct(1) wellFormed_currentTx_unique_h(2) wellFormed_state_transaction_consistent(4))
  then show ?thesis
    by (meson domIff local.wf wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_r)
qed



lemma downwardsClosure_subset2:
  "x \<in> S \<down> R \<Longrightarrow> x \<in> S \<union> fst ` R"
  by (meson downwardsClosure_subset subsetCE)


text \<open>
 There can be no action on a invocId after a fail or return:
 (except for invariant checks)
\<close>
lemma nothing_after_fail_or_return:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and fail_or_return: "tr!i = (s, ACrash) \<or> tr!i = (s, AReturn res)"
    and i_in_range: "i < length tr"
  shows "\<nexists>j. j>i \<and> j<length tr \<and> get_invoc(tr!j) = s \<and> \<not>is_AInvcheck (get_action (tr!j))" 
  using steps fail_or_return i_in_range proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'')
  show "\<not> (\<exists>j>i. j < length (tr @ [a]) \<and> get_invoc ((tr @ [a]) ! j) = s \<and> \<not> is_AInvcheck (get_action ((tr @ [a]) ! j)))"
  proof (rule ccontr, auto)
    fix j
    assume a1: "j < Suc (length tr)"
      and a2: "i < j"
      and a3: "s = get_invoc ((tr @ [a]) ! j)"
      and a4: "\<not> is_AInvcheck (get_action ((tr @ [a]) ! j))"

    have j_def: "j = length tr"
    proof (rule ccontr)
      assume "j \<noteq> length tr"
      then have "j < length tr" using a1 by simp
      then have "s \<noteq> get_invoc ((tr @ [a]) ! j)"
        by (metis a2 a4 length_append_singleton less_Suc_eq nth_append order.asym step.IH step.prems(1) step.prems(2))
      with a3 show False by simp
    qed

    obtain a_op where a_def: "a = (s, a_op)" using j_def a3
      by (metis nth_append_length prod.collapse) 



    from \<open>(tr @ [a]) ! i = (s, ACrash) \<or> (tr @ [a]) ! i = (s, AReturn res)\<close>
    have no_ls: "localState S' s = None" 
      and op: "invocOp S' s \<noteq> None"  
       apply (metis a2 everything_starts_with_an_invocation j_def nth_append step.steps)
      by (metis a2 everything_starts_with_an_invocation j_def nth_append step.prems(1) step.steps)

    have fst_a: "get_invoc a = s" using a_def by simp  

    from \<open>S' ~~ a \<leadsto> S''\<close> a_def
    have "S' ~~ (s, a_op) \<leadsto> S''" by simp  

    then show False
      apply (rule step.cases)
              apply (auto simp add: no_ls a3 op j_def)
              apply (auto simp add: fst_a no_ls op)
      using a4 a_def is_AInvcheck_def j_def by auto 
  qed
qed



text \<open>
 We have visible calls iff we have some local state.
\<close>
lemma visibleCalls_iff_localState:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
  shows "localState S s = None \<longleftrightarrow> visibleCalls S s = None" 
  using steps
proof (induct rule: steps_induct)
  case initial
  then show ?case
    by (simp add: initialState_def)
next
  case (step S' tr a S'')
  from \<open>S' ~~ a \<leadsto> S''\<close>
  show ?case 
    apply (rule step.cases)
    using step.IH  by (auto simp add: step)
qed

lemma i_callOriginI_notI1:
  assumes "state_wellFormed S_pre" 
    and "invocOp S_pre i = None" 
  shows "i_callOriginI S_pre c \<noteq> Some i"
  by (simp add: assms(1) assms(2) i_callOriginI_h_def option.case_eq_if wf_no_invocation_no_origin)

lemma i_callOriginI_notI2:
  assumes "state_wellFormed S_pre" 
    and "i_callOriginI S_pre c = Some i" 
  shows "invocOp S_pre i \<noteq> None"
  using assms(1) assms(2) i_callOriginI_notI1 by blast

text \<open>
Updating the invocId happens-before in the first transaction of an invocId.

\<close>
lemma invocation_happensBeforeH_update:
  assumes  Orig'_def: "\<And>c. Orig' c = (case Orig c of Some i \<Rightarrow> Some i | None \<Rightarrow> if c\<in>set cs then Some i else None)"
    and cs_no_orig: "\<And>c. c \<in> set cs \<Longrightarrow> Orig c = None"
    and cs_notin_vis: "\<And>c. c \<in> set cs \<Longrightarrow> c \<notin> vis"
    and cs_notin_hb1: "\<And>c x. c \<in> set cs \<Longrightarrow> (x,c) \<notin> Hb"
    and cs_notin_hb2: "\<And>c x. c \<in> set cs \<Longrightarrow> (c,x) \<notin> Hb"
    and invoc_fresh: "\<And>c. Orig c \<noteq> Some i"
    and cs_nonempty: "cs \<noteq> []"
  shows
    "invocation_happensBeforeH Orig' (updateHb Hb vis cs)
   = invocation_happensBeforeH Orig Hb \<union> {i'. (\<forall>c. Orig c \<triangleq> i' \<longrightarrow> c \<in> vis) \<and> (\<exists>c. Orig c \<triangleq> i') }  \<times>  {i} "
  using invoc_fresh  apply (auto simp add: invocation_happensBeforeH_def  in_img_simp updateHb_cases)
                apply (auto simp add: Orig'_def cs_notin_hb1  cs_notin_hb2 cs_notin_vis cs_no_orig  split: option.splits if_splits)
  using cs_no_orig in_sequence_in2 apply fastforce
  using cs_no_orig in_sequence_in1 apply fastforce
        apply (metis cs_no_orig in_sequence_in2 option.simps(3))
       apply (metis cs_no_orig in_sequence_in2 option.distinct(1))
  using cs_no_orig in_sequence_in2 apply fastforce
     apply (metis cs_no_orig option.distinct(1) option.sel)
    apply (metis cs_no_orig option.distinct(1) option.sel)
  using cs_notin_vis option.simps(3) apply fastforce
  using cs_nonempty last_in_set by blast



lemma state_wellFormed_txStatus_callOrigin:     
  assumes "state_wellFormed S"
and "callOrigin S c \<triangleq> tx"
shows "txStatus S tx \<noteq> None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S')
  thus ?case 
    by (auto simp add: step.simps inTransaction_localState split: if_splits dest:  wellFormed_currentTx_unique_h(2) )
qed

lemma state_wellFormed_txStatus_txOrigin:     
  assumes "state_wellFormed S"
and "txOrigin S tx \<triangleq> i"
shows "txStatus S tx \<noteq> None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S')
  thus ?case 
    by (auto simp add: step.simps inTransaction_localState split: if_splits dest:  wellFormed_currentTx_unique_h(2) )
qed

lemma state_wellFormed_current_transaction_origin:     
  assumes "state_wellFormed S"
and "currentTx S i \<triangleq> tx"
shows "txOrigin S tx \<triangleq> i"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S')
  thus ?case 
    by (auto simp add: step.simps  split: if_splits dest: state_wellFormed_txStatus_txOrigin)

qed


lemma state_wellFormed_ls_visibleCalls_callOrigin:     
  assumes "state_wellFormed S"
and "callOrigin S c \<triangleq> tx"
and "txOrigin S tx \<triangleq> i"
and "visibleCalls S i \<triangleq> vis"
  shows "c \<in> vis"
  using assms proof (induct  arbitrary: vis rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S a S' vis')
  thus ?case 
    by (auto simp add: step.simps inTransaction_localState chooseSnapshot_def state_wellFormed_current_transaction_origin  split: if_splits 
          dest: wf_no_txStatus_origin_for_nothing  wf_no_invocation_no_origin )

qed



text_raw \<open>\DefineSnippet{state_wellFormed_same_invocation_sequential}{\<close>
lemma state_wellFormed_same_invocation_sequential:     
  assumes "state_wellFormed S"
    and "callOrigin S c1 \<triangleq> tx1" 
    and "txOrigin S tx1 \<triangleq> i"
    and "callOrigin S c2 \<triangleq> tx2"
    and "txOrigin S tx2 \<triangleq> i"
    and "c1 \<noteq> c2"
shows "(c1,c2)\<in>happensBefore S \<or> (c2,c1)\<in>happensBefore S"
text_raw \<open>}%EndSnippet\<close>
 using assms proof (induct  arbitrary:  rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  then show ?case 
    using state_wellFormed_txStatus_callOrigin[OF \<open>state_wellFormed t\<close>]
          wf_no_txStatus_origin_for_nothing[OF \<open>state_wellFormed t\<close>]
          state_wellFormed_current_transaction_origin[OF \<open>state_wellFormed t\<close>]
          state_wellFormed_ls_visibleCalls_callOrigin[OF \<open>state_wellFormed t\<close>]
    by  (auto simp add: step.simps split: if_splits)
qed

text_raw \<open>\DefineSnippet{state_wellFormed_vis_subset_calls}{\<close>
lemma state_wellFormed_vis_subset_calls:     
  assumes "state_wellFormed S"
    and "visibleCalls S i \<triangleq> vis"
    and "c \<in> vis"
shows "c \<in> dom (calls S)"
text_raw \<open>}%EndSnippet\<close>
  by (meson assms subset_h1 wellFormed_visibleCallsSubsetCalls_h(2))

text_raw \<open>\DefineSnippet{state_wellFormed_hb_antisym}{\<close>
lemma state_wellFormed_hb_antisym:     
  assumes "state_wellFormed S"
  assumes "(x,y) \<in> happensBefore S"
  shows "(y,x) \<notin> happensBefore S"
  text_raw \<open>}%EndSnippet\<close>
  by (meson assms happensBefore_irrefl happensBefore_transitive irrefl_def transE)

text_raw \<open>\DefineSnippet{state_wellFormed_hb_antisym2}{\<close>
lemma state_wellFormed_hb_antisym2:     
  assumes "state_wellFormed S"
  shows "antisym (happensBefore S)"
  text_raw \<open>}%EndSnippet\<close>
using antisym_def assms state_wellFormed_hb_antisym by auto


text_raw \<open>\DefineSnippet{state_wellFormed_transactionOrigin_callOrigin}{\<close>
lemma state_wellFormed_transactionOrigin_callOrigin:     
  assumes "state_wellFormed S"
    and "txOrigin S tx = None"
  shows "callOrigin S c \<noteq> Some tx"
text_raw \<open>}%EndSnippet\<close>
  using assms state_wellFormed_txStatus_callOrigin wf_txOrigin_and_status by blast



text_raw \<open>\DefineSnippet{wf_transaction_consistent_l}{\<close>
lemma wf_transaction_consistent_l:     
  assumes "state_wellFormed S"
    and "callOrigin S y1 = callOrigin S y2"
    and "callOrigin S x \<noteq> callOrigin S y1"
    and "(y1, x)\<in>happensBefore S"
  shows "(y2, x)\<in>happensBefore S"
text_raw \<open>}%EndSnippet\<close>
  by (metis assms wellFormed_state_transaction_consistent(3))

text_raw \<open>\DefineSnippet{wf_transaction_consistent_r}{\<close>
lemma wf_transaction_consistent_r:     
  assumes "state_wellFormed S"
    and "callOrigin S y1 = callOrigin S y2"
    and "callOrigin S x \<noteq> callOrigin S y1"
    and "(x, y1)\<in>happensBefore S"
  shows "(x, y2)\<in>happensBefore S"
text_raw \<open>}%EndSnippet\<close>
 by (metis assms wellFormed_state_transaction_consistent(3))


lemma growth_callOrigin:
  assumes "state_monotonicGrowth i S S'"
    and "callOrigin S c \<triangleq> tx"
  shows "callOrigin S' c \<triangleq> tx"
  using assms(1) assms(2) state_monotonicGrowth_callOrigin by blast



end