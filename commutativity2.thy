theory commutativity2
imports commutativity
begin

lemma move_outside_transaction:
  assumes b_is_a_different_session[simp]: "sa \<noteq> sb"
    and wf[simp]: "state_wellFormed S"
    and no_end_atomic: "b \<noteq> AEndAtomic"
  shows "(S ~~ [(sa,ABeginAtomic t newTxns),(sb,b)] \<leadsto>* T)
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,ABeginAtomic t newTxns)] \<leadsto>* T)"
proof (rule useCommutativeS)
  show "commutativeS S (sa, ABeginAtomic t newTxns) (sb, b)"
    using assms by (rule commutative_beginAtomic_other)
qed


end