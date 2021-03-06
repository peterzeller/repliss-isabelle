section "Application Verification Helpers"

theory app_verification_helpers
  imports 
    program_verification_tactics
    crdt_specs2
    unique_ids
begin

text "Various Lemmas that can be used when verifying an application."


lemma use_some_wellFormed:
  assumes e: "\<exists>some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus.
       state_wellFormed
        \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
           invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
and R: "\<And>S. state_wellFormed S \<Longrightarrow> P S"
shows "\<exists>some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus. 
  P \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
           invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
proof -
  from e obtain some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus
    where "state_wellFormed
        \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
           invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
    by blast
  hence "P \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
           invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
    by (rule R)
  thus ?thesis
    by blast
qed

lemma get_query_spec:
  assumes wf: "\<exists>some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus.
     state_wellFormed
      \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
         txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
         invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
         generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
         visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
    and upd_call: "s_calls' upd_c \<triangleq> Call oper upd_r"
  shows "\<exists>ctxt. querySpec progr oper ctxt upd_r"
proof -
  from wf
  obtain some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus
    where state_wf: "state_wellFormed
                  \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
                     txOrigin = s_txOrigin', knownIds = s_knownIds', invocOp = s_invocOp',
                     invocRes = s_invocRes', prog = progr, txStatus = some_txStatus,
                     generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
                     visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
    by blast

  from wf_queryspec[OF state_wf] upd_call
  obtain ctxt where "querySpec progr oper ctxt upd_r"
    by auto blast
  thus ?thesis
    by blast
qed




lemma C_out_calls_remove_unaffected:
  assumes "\<And>y. C_out y \<noteq> x"
  shows "C_out_calls C_out (m(c := x)) vis
  = C_out_calls C_out m vis - {c}"
  using assms  by (auto simp add: C_out_calls_def)

lemma C_out_nesting_simp:
  assumes "C_out1 = C_out2 \<circ> f"
  shows
  "C_out_calls C_out1 op (C_out_calls C_out2 op vis)
= C_out_calls C_out1 op vis" 
  by (auto simp add: assms C_out_calls_def)

lemma C_out_nesting_simp2[simp]:
  shows
  "C_out_calls (C_out \<circ> f) op (C_out_calls C_out op vis)
= C_out_calls (C_out \<circ> f) op vis" 
  by (auto simp add:  C_out_calls_def)

lemma C_out_calls_empty[simp]: "C_out_calls C_out op {} = {}"
  by (auto simp add: C_out_calls_def)

lemma C_out_union: 
"C_out_calls C_out op (A \<union> B) = C_out_calls C_out op A \<union> C_out_calls C_out op B"
  by (auto simp add: C_out_calls_def)

lemma C_out_insert: 
"C_out_calls C_out op (insert c A) = (if \<exists>x. op c = C_out x then {c} else {}) \<union> C_out_calls C_out op A"
  by (auto simp add: C_out_calls_def)

lemma C_out_intersection: 
"C_out_calls C_out op (A \<inter> B) = C_out_calls C_out op A \<inter> C_out_calls C_out op B"
  by (auto simp add: C_out_calls_def)

lemma C_out_minus: 
"C_out_calls C_out op (A - B) = C_out_calls C_out op A - C_out_calls C_out op B"
  by (auto simp add: C_out_calls_def)

lemma in_C_out:
"x \<in> C_out_calls C_out op vis
\<longleftrightarrow> x\<in> vis \<and> (\<exists>y. op x = C_out y)"
  by (auto simp add: C_out_calls_def)

lemmas C_out_distrib = C_out_union  C_out_insert C_out_intersection C_out_minus





lemma acyclic_updateHb1:
  assumes "distinct cs"
    and "vis \<inter> set cs = {}"
  shows "acyclic (updateHb {} vis cs)"
  using assms proof (induct cs arbitrary: vis)
  case Nil
  then show ?case by auto
next
  case (Cons a cs vis)
  have "a \<notin> vis"
    using Cons.prems(2) by auto


  show ?case 
  proof (simp add: updateHb_cons, subst updateHb_simp_split, rule acyclic_union_disjoint)
    show "acyclic (vis \<times> {a})"
      by (simp add: acyclic_prod `a \<notin> vis`)
    show " acyclic (updateHb {} (insert a vis) cs)"
    proof (rule Cons.hyps)
      show "distinct cs"
        using Cons.prems(1) by auto
      show "insert a vis \<inter> set cs = {}"
        using Cons.prems(1) Cons.prems(2) by auto
    qed

    show " snd ` updateHb {} (insert a vis) cs \<inter> fst ` (vis \<times> {a}) = {}"
      using Cons.prems(2) snd_updateHb2 by fastforce
  qed
qed

lemma acyclic_updateHb:
  assumes "acyclic hb"
    and "distinct cs"
    and "vis \<inter> set cs = {}"
    and "Field hb \<inter> set cs = {}"
  shows "acyclic (updateHb hb vis cs)"
  using `acyclic hb`
proof (subst  updateHb_simp_split, rule acyclic_union_disjoint)

  show "acyclic (updateHb {} vis cs)"
    by (simp add: acyclic_updateHb1 assms(2) assms(3))

  show "snd ` updateHb {} vis cs \<inter> fst ` hb = {}"
    by (smt Domain_fst Field_def Int_iff assms(4) disjoint_iff_not_equal inf_sup_absorb snd_updateHb2 subset_eq)
qed


declare invContext.defs[simp]




lemma invContextH2_Op:
"Op (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= cOp state_calls"
  by (auto simp add: invContextH2_calls)

lemma cOp_empty[simp]:
"cOp Map.empty = Map.empty"
  by (auto simp add: cOp_def)

lemma cOp_update[simp]: 
"cOp (m(c \<mapsto> cc)) = (cOp m)(c \<mapsto> call_operation cc)"
  by (auto simp add: cOp_def)

lemma cOp_none[simp]: 
  assumes "m c = None"
  shows "cOp m c = None"
  using assms  by (auto simp add: cOp_def)


lemma cOp_Some[simp]: 
  assumes "m c \<triangleq> cc"
  shows "cOp m c \<triangleq> call_operation cc"
  using assms by (auto simp add: cOp_def)



lemma cOp_Some_iff: 
  shows "cOp m c \<triangleq> opr \<longleftrightarrow> (\<exists>r. m c \<triangleq> Call opr r)"
  by (auto simp add: cOp_def)
   (metis call.collapse)



end