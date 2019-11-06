theory execution_invariants2
  imports repliss_sem execution_invariants consistency commutativity
begin


lemma wf_transaction_status_iff_origin_dom:
  assumes wf: "state_wellFormed S"
  shows "dom (transactionOrigin S) = dom (transactionStatus S)"
  by (smt Collect_cong dom_def local.wf wf_transaction_status_iff_origin)



end