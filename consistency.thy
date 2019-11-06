theory consistency
imports repliss_sem execution_invariants
begin



definition
"causallyConsistent hb vis \<equiv>
  (\<forall>c1 c2. c1\<in>vis \<and> (c2,c1)\<in> hb \<longrightarrow> c2\<in>vis)"

definition
"transactionConsistent origin txStatus vis \<equiv>
    (\<forall>c tx. c\<in>vis \<and> origin c \<triangleq> tx \<longrightarrow> txStatus tx \<triangleq> Committed)
  \<and> (\<forall>c1 c2. c1\<in>vis \<and> origin c1 = origin c2 \<longrightarrow> c2\<in>vis)"

lemma transactionConsistent_Committed:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c\<in>vis; origin c \<triangleq> tx; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus tx \<triangleq> Committed"
by (auto simp add:  transactionConsistent_def) 

lemma transactionConsistent_all_from_same:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
by (auto simp add:  transactionConsistent_def) 

definition consistentSnapshotH where
"consistentSnapshotH s_calls s_happensBefore s_callOrigin s_transactionStatus vis \<equiv>
  vis \<subseteq> dom s_calls
 \<comment> \<open>  causally consistent  \<close> 
 \<and> (causallyConsistent s_happensBefore vis)
 \<comment> \<open> transaction consistent  \<close>
 \<and> (transactionConsistent s_callOrigin s_transactionStatus vis)
"

abbreviation consistentSnapshot where
"consistentSnapshot state vis \<equiv>
consistentSnapshotH (calls state) (happensBefore state) (callOrigin state) (transactionStatus state) vis"

abbreviation consistentSnapshotI where
"consistentSnapshotI state vis \<equiv>
consistentSnapshotH (calls state) (happensBefore state) (callOrigin state) (\<lambda>t. Some Committed) vis"


lemma show_consistentSnapshot:
  assumes "vis \<subseteq> dom s_calls"
and "causallyConsistent s_happensBefore vis"
and "transactionConsistent s_callOrigin s_transactionStatus vis"
  shows "consistentSnapshotH s_calls s_happensBefore s_callOrigin s_transactionStatus vis"
  using assms by (auto simp add: consistentSnapshotH_def)



lemma chooseSnapshot_causallyConsistent_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2': "trans (happensBefore S)"
    and a3: "causallyConsistent (happensBefore S) vis"
  shows "causallyConsistent (happensBefore S) snapshot"
  using a1 a3 apply (auto simp add: chooseSnapshot_def downwardsClosure_def causallyConsistent_def)
   apply (rule_tac x=y in exI)
  apply auto
  by (meson a2' transE)



lemma wellFormed_state_causality:
assumes wf: "state_wellFormed S"
shows "\<And>s vis. visibleCalls S s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore S) vis"
  and "trans (happensBefore S)"
using assms  proof (induct rule: wellFormed_induct)
  case initial
  show "visibleCalls (initialState (prog S)) s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore (initialState (prog S))) vis" for s vis
    by (auto simp add: initialState_def)
  show "trans (happensBefore (initialState (prog S)))"
    by (auto simp add: initialState_def)
next
  case (step C a C')

  have causal: "causallyConsistent (happensBefore C) vis" if "visibleCalls C s \<triangleq> vis" for s vis
    using step.hyps(2) that by auto
    
  
    
  show "trans (happensBefore C')"
    using \<open>trans (happensBefore C)\<close> \<open>C ~~ a \<leadsto> C'\<close> apply (auto simp add: step_simps_all)
    using causal apply (auto simp add: causallyConsistent_def)
    by (smt Un_iff domIff empty_iff insert_iff mem_Sigma_iff step.hyps(1) subset_eq trans_def wellFormed_visibleCallsSubsetCalls_h(1))
    
  show "visibleCalls C' s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore C') vis" for s vis
    using causal \<open>C ~~ a \<leadsto> C'\<close> apply (auto simp add: step_simps_all)
        apply (auto simp add: causallyConsistent_def split: if_splits)
    apply (meson causallyConsistent_def chooseSnapshot_causallyConsistent_preserve step.hyps(3))
    apply (metis (no_types, lifting) SigmaD2 domIff step.hyps(1) subsetCE wellFormed_visibleCallsSubsetCalls_h(1))
    using step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast
    
qed



end


