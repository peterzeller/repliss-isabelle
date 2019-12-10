theory app_verification_helpers
  imports 
    program_verification_tactics
    impl_language
    crdt_specs2
    unique_ids
    program_proof_rules
begin



lemma use_some_wellFormed:
  assumes e: "\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus.
       state_wellFormed
        \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
           invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
and R: "\<And>S. state_wellFormed S \<Longrightarrow> P S"
shows "\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus. 
  P \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
           invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
proof -
  from e obtain some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus
    where "state_wellFormed
        \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
           invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
    by blast
  hence "P \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
           transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
           invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
    by (rule R)
  thus ?thesis
    by blast
qed

lemma get_query_spec:
  assumes wf: "\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus.
     state_wellFormed
      \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
         transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
         invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
         generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
         visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
    and upd_call: "s_calls' upd_c \<triangleq> Call oper upd_r"
  shows "\<exists>ctxt. querySpec progr oper ctxt upd_r"
proof -
  from wf
  obtain some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus
    where state_wf: "state_wellFormed
                  \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
                     transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
                     invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
                     generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
                     visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
    by blast

  from wf_queryspec[OF state_wf] upd_call
  obtain ctxt where "querySpec progr oper ctxt upd_r"
    apply atomize_elim
    apply auto
    by blast
  thus ?thesis
    by blast
qed


lemma query_result_undef:
  assumes wf: "\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus.
     state_wellFormed
      \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
         transactionOrigin = s_transactionOrigin', knownIds = s_knownIds', invocationOp = s_invocationOp',
         invocationRes = s_invocationRes', prog = progr, transactionStatus = some_transactionStatus,
         generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
         visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
    and upd_call: "s_calls' upd_c \<triangleq> Call (Message (NestedOp (MessageId m) upd_op)) upd_r"
    and upd_is_update: "is_update upd_op"
  shows "upd_r = Undef"
proof -

  obtain ctxt where "querySpec progr (Message (NestedOp (MessageId m) upd_op)) ctxt upd_r"
    using assms(1) get_query_spec upd_call by blast

  thus "upd_r = Undef"
    using upd_is_update
    by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def messageStruct_def register_spec_def split: messageDataOp.splits registerOp.splits if_splits)

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
    apply (simp add: updateHb_cons)
    apply (subst updateHb_simp_split)
  proof (rule acyclic_union_disjoint)
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
  apply (subst  updateHb_simp_split)
  using `acyclic hb`
proof (rule acyclic_union_disjoint)

  show "acyclic (updateHb {} vis cs)"
    by (simp add: acyclic_updateHb1 assms(2) assms(3))

  show "snd ` updateHb {} vis cs \<inter> fst ` hb = {}"
    by (smt Domain_fst Field_def Int_iff assms(4) disjoint_iff_not_equal inf_sup_absorb snd_updateHb2 subset_eq)
qed


end