theory execution_invariants2
  imports repliss_sem execution_invariants consistency commutativity
begin


lemma wf_transaction_status_iff_origin_dom:
  assumes wf: "state_wellFormed S"
  shows "dom (transactionOrigin S) = dom (transactionStatus S)"
  by (smt Collect_cong dom_def local.wf wf_transaction_status_iff_origin)

lemma wf_generated_ids_invocation_exists:
  assumes wf: "state_wellFormed S"
and "invocationOp S i = None"
shows "generatedIds S uid \<noteq> Some i"
  find_theorems name: induct state_wellFormed
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: initialState_def step.simps wf_localState_to_invocationOp split: if_splits)
qed




end