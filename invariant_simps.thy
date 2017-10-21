theory invariant_simps
  imports approach single_invocation_correctness
begin

section {* Invariant simplifications *}

text {* 
 This theory includes helpers for working with invariants.
*}


definition 
  "i_callOriginI ctxt c \<equiv> 
  case i_callOrigin ctxt c of Some t \<Rightarrow> i_transactionOrigin ctxt t | None \<Rightarrow> None"

text {* lifting the happensBefore relation on database-calls to the level of invocations. *}
definition 
  "invocation_happensBefore ctxt \<equiv> 
  {(x,y). (\<exists>c. i_callOriginI ctxt c \<triangleq> x) 
        \<and> (\<exists>c. i_callOriginI ctxt c \<triangleq> y) 
        \<and> (\<forall>cx cy. i_callOriginI ctxt cx \<triangleq> x
                 \<and> i_callOriginI ctxt cy \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>happensBefore ctxt)}"


lemma i_invocationOp_simps:
  "(i_invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis) r \<triangleq> Op) \<longleftrightarrow> (state_invocationOp r \<triangleq> Op)"
  by (auto simp add: invContextH_def)

lemma invocation_happensBefore_simps:
  "((x,y) \<in> invocation_happensBefore (invContextH state_callOrigin state_transactionOrigin ts state_happensBefore cs ki io ir vis)) 
\<longleftrightarrow> ((\<exists>c t. state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> x) 
        \<and> (\<exists>c t.  state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> y) 
        \<and> (\<forall>cx tx cy ty. state_callOrigin cx \<triangleq> tx \<and> state_transactionOrigin tx \<triangleq> x
                 \<and> state_callOrigin cy \<triangleq> ty \<and> state_transactionOrigin ty \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>state_happensBefore))"
  apply auto                 
     apply (auto simp add: invContextH_def invocation_happensBefore_def 
      i_callOriginI_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
    apply (auto simp add: invContextH_def invocation_happensBefore_def 
      i_callOriginI_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
   apply (auto simp add: invContextH_def invocation_happensBefore_def 
      i_callOriginI_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]   
    apply (drule_tac x=cx in spec)
    apply auto[1]
  oops


lemmas invariant_simps = 
  i_invocationOp_simps

(*

  i_visibleCalls :: "callId set"
  i_callOrigin :: "callId \<rightharpoonup> txid"
  i_transactionOrigin :: "txid \<rightharpoonup> invocation"
  i_knownIds :: "'any set"
  i_invocationOp :: "invocation \<rightharpoonup> (procedureName \<times> 'any list)"
  i_invocationRes :: "invocation \<rightharpoonup> 'any"
*)

end