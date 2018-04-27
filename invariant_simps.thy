theory invariant_simps
  imports approach single_invocation_correctness
begin

section {* Invariant simplifications *}

text {* 
 This theory includes helpers for working with invariants.
*}


definition 
  "i_callOriginI_h callOrig transactionOrig \<equiv> \<lambda>c.
  case callOrig c of Some t \<Rightarrow> transactionOrig t | None \<Rightarrow> None"


abbreviation 
  "i_callOriginI ctxt \<equiv> i_callOriginI_h (i_callOrigin ctxt) (i_transactionOrigin ctxt)"

text {* lifting the happensBefore relation on database-calls to the level of invocations. *}
definition 
  "invocation_happensBeforeH origin hb \<equiv> 
  {(x,y). (\<exists>c. origin c \<triangleq> x) 
        \<and> (\<exists>c. origin c \<triangleq> y) 
        \<and> (\<forall>cx cy. origin cx \<triangleq> x
                 \<and> origin cy \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>hb)}"

abbreviation 
  "invocation_happensBefore ctxt \<equiv> invocation_happensBeforeH (i_callOriginI ctxt) (happensBefore ctxt)"


lemma i_invocationOp_simps:
  "(i_invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes ) r \<triangleq> Op) \<longleftrightarrow> (state_invocationOp r \<triangleq> Op)"
  by (auto simp add: invContextH_def)

lemma invocation_happensBefore_simps:
  "((x,y) \<in> invocation_happensBefore (invContextH state_callOrigin state_transactionOrigin ts state_happensBefore cs ki io ir )) 
\<longleftrightarrow> ((\<exists>c t. state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> x) 
        \<and> (\<exists>c t.  state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> y) 
        \<and> (\<forall>cx tx cy ty. state_callOrigin cx \<triangleq> tx \<and> state_transactionOrigin tx \<triangleq> x
                 \<and> state_callOrigin cy \<triangleq> ty \<and> state_transactionOrigin ty \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>state_happensBefore))"
  apply auto                 
     apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
    apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
   apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def commitedCallsH_def restrict_relation_def split: option.splits if_splits)[1]   
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