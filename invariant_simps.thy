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




lemma new_invocation_cannot_happen_before:
  assumes "state_wellFormed S'"
    and "invocationOp S' i = None"
  shows "(i,g) \<notin> invocation_happensBeforeH (i_callOriginI_h (callOrigin S') (transactionOrigin S')) (happensBefore S')"
proof (auto simp add: invocation_happensBeforeH_def)
  fix c ca
  assume a0: "\<forall>cx. i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> i \<longrightarrow> (\<forall>cy. i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> g \<longrightarrow> (cx, cy) \<in> happensBefore S')"
    and a1: "i_callOriginI_h (callOrigin S') (transactionOrigin S') c \<triangleq> i"
    and a2: "i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> g"

  from `state_wellFormed S'` `invocationOp S' i = None`
  have "transactionOrigin S' tx \<noteq> Some i" for tx
    by (simp add: wf_no_invocation_no_origin)


  with a1
  show "False"
    by (auto simp add:  i_callOriginI_h_def restrict_map_def split: option.splits if_splits)
qed

lemma new_invocation_cannot_happen_after:
  assumes "state_wellFormed S'"
    and "invocationOp S' i = None"
  shows "(g,i) \<notin> invocation_happensBeforeH (i_callOriginI_h (callOrigin S') (transactionOrigin S')) (happensBefore S')"
proof (auto simp add: invocation_happensBeforeH_def)
  fix c ca
  assume a0: "\<forall>cx. i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> g \<longrightarrow> (\<forall>cy. i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> i \<longrightarrow> (cx, cy) \<in> happensBefore S')"
    and a1: "i_callOriginI_h (callOrigin S') (transactionOrigin S') c \<triangleq> g"
    and a2: "i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> i"


  from `state_wellFormed S'` `invocationOp S' i = None`
  have "transactionOrigin S' tx \<noteq> Some i" for tx
    by (simp add: wf_no_invocation_no_origin)


  with a2
  show "False"
    by (auto simp add:  i_callOriginI_h_def restrict_map_def split: option.splits if_splits)
qed

schematic_goal checkCorrect2F_step:
  "\<lbrakk>b>0; ?F (checkCorrect2F ^^ (b - 1)) bot S\<rbrakk> \<Longrightarrow> (checkCorrect2F ^^ b) bot S"
  apply (case_tac b)
   apply simp
  apply (rule_tac t=b and s="Suc nat" in ssubst, assumption)
  apply (subst funpow.simps)
  apply (subst o_apply)
  apply (subst checkCorrect2F_def)
  apply (rule_tac t=nat and s="b - 1" in ssubst)
   apply simp
  apply assumption
  done


(*

  i_visibleCalls :: "callId set"
  i_callOrigin :: "callId \<rightharpoonup> txid"
  i_transactionOrigin :: "txid \<rightharpoonup> invocation"
  i_knownIds :: "'any set"
  i_invocationOp :: "invocation \<rightharpoonup> (procedureName \<times> 'any list)"
  i_invocationRes :: "invocation \<rightharpoonup> 'any"
*)

end