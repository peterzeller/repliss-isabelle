theory execution_invariants_unused
  imports repliss_sem execution_invariants consistency commutativity
begin

text "These are currently unused execution invariants"




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
    
  show "transactionConsistent (callOrigin S) (transactionStatus S) (callsInTransaction S txns \<down> happensBefore S)"
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
    and "currentTransaction S i \<triangleq> tx"
    and "callOrigin S x \<triangleq> tx"
    and "callOrigin S y \<noteq> Some tx"
  shows "(x,y) \<notin> happensBefore S"
proof -
  obtain tt :: "(callId \<Rightarrow> txid option) \<Rightarrow> callId \<Rightarrow> txid" where
    "\<forall>x0 x1. (\<exists>v2. x0 x1 \<triangleq> v2) = x0 x1 \<triangleq> tt x0 x1"
    by moura
  then have "\<forall>c f. c \<notin> dom f \<or> f c \<triangleq> tt f c"
    by blast
  then have "(x, y) \<notin> happensBefore S \<or> y \<notin> dom (callOrigin S)"
    by (metis (no_types) assms(3) assms(4) assms(5) local.wf option.inject transactionStatus.distinct(1) wellFormed_currentTransaction_unique_h(2) wellFormed_state_transaction_consistent(4))
  then show ?thesis
    by (meson domIff local.wf wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_r)
qed


(*
lemma wf_happensBefore_trans: 
  assumes  wf: "state_wellFormed S"
  shows "trans (happensBefore S)"
  using assms apply (induct rule: wellFormed_induct)
   apply (simp add: initialState_def)
  apply (auto simp add: step.simps)
  apply (subst trans_def)
  apply (auto dest: transD)
proof -

show "(x, c) \<in> happensBefore t"
    if c0: "state_wellFormed t"
   and c1: "trans (happensBefore t)"
   and c2: "localState t sa \<triangleq> ls"
   and c3: "currentProc t sa \<triangleq> f"
   and c4: "f ls = DbOperation Op args ls'"
   and c5: "currentTransaction t sa \<triangleq> ta"
   and c6: "calls t c = None"
   and c7: "querySpec (prog t) Op args (getContextH (calls t) (happensBefore t) (Some vis)) res"
   and c8: "visibleCalls t sa \<triangleq> vis"
   and c9: "(x, y) \<in> happensBefore t"
   and c10: "y \<in> vis"
   and c11: "x \<notin> vis"
   for  t sa ls f Op args ls' ta c res vis x y
  using wellFormed_visibleCallsSubsetCalls[OF c0 c8] wellFormed_visibleCallsSubsetCalls_h(1)[OF c0]
that 
*)


lemma downwardsClosure_subset2:
  "x \<in> S \<down> R \<Longrightarrow> x \<in> S \<union> fst ` R"
  by (meson downwardsClosure_subset subsetCE)


text \<open>
 There can be no action on a invocId after a fail or return:
 (except for invariant checks)
\<close>
lemma nothing_after_fail_or_return:
  assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and fail_or_return: "tr!i = (s, AFail) \<or> tr!i = (s, AReturn res)"
    and i_in_range: "i < length tr"
  shows "\<nexists>j. j>i \<and> j<length tr \<and> fst(tr!j) = s \<and> \<not>is_AInvcheck (snd (tr!j))" 
  using steps fail_or_return i_in_range proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'')
  show "\<not> (\<exists>j>i. j < length (tr @ [a]) \<and> fst ((tr @ [a]) ! j) = s \<and> \<not> is_AInvcheck (snd ((tr @ [a]) ! j)))"
  proof (rule ccontr, auto)
    fix j
    assume a1: "j < Suc (length tr)"
      and a2: "i < j"
      and a3: "s = fst ((tr @ [a]) ! j)"
      and a4: "\<not> is_AInvcheck (snd ((tr @ [a]) ! j))"

    have j_def: "j = length tr"
    proof (rule ccontr)
      assume "j \<noteq> length tr"
      then have "j < length tr" using a1 by simp
      then have "s \<noteq> fst ((tr @ [a]) ! j)"
        by (metis a2 a4 length_append_singleton less_Suc_eq nth_append order.asym step.IH step.prems(1) step.prems(2))
      with a3 show False by simp
    qed

    obtain a_op where a_def: "a = (s, a_op)" using j_def a3
      by (metis nth_append_length prod.collapse) 



    from \<open>(tr @ [a]) ! i = (s, AFail) \<or> (tr @ [a]) ! i = (s, AReturn res)\<close>
    have no_ls: "localState S' s = None" 
      and op: "invocationOp S' s \<noteq> None"  
       apply (metis a2 everything_starts_with_an_invocation j_def nth_append step.steps)
      by (metis a2 everything_starts_with_an_invocation j_def nth_append step.prems(1) step.steps)

    have fst_a: "fst a = s" using a_def by simp  

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


end