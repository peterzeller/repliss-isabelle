section "CRDT Specifications For Verification"
theory crdt_specs_v
  imports repliss_sem crdt_specs
begin


text "The previous CRDT are not nice to work with when composed.
The problem is, that the specifications for maps and structs transform the context
passed to embedded CRDTs.
During this transformation the reverse direction is lost, so it is hard to reconstruct the original
calls from the calls in an embedded context.
Therefore, we now use a different composition technique, where the mapping is explicitly passed down
into nested CRDTs."

text "In the following type definition we have three type parameters:

\<^enum> op is the type of operations at the top level
\<^enum> opn is the type of nested operations, on which the specification works
\<^enum> res is the type of results "

type_synonym ('op, 'opn, 'res) cOperationResultSpec = 
        "callId set                  \<comment> \<open>visible calls\<close>
      \<Rightarrow> (callId \<Rightarrow>'op)              \<comment> \<open>call information\<close> 
      \<Rightarrow> callId rel                  \<comment> \<open>happens-before\<close>
      \<Rightarrow> ('opn \<Rightarrow> 'op)               \<comment> \<open>mapping back\<close>
      \<Rightarrow> 'res
      \<Rightarrow> bool"

type_synonym ('op, 'opn, 'res) ccrdtSpec = 
        "'opn \<Rightarrow> ('op, 'opn, 'res) cOperationResultSpec"


definition 
"extract_op c_calls c \<equiv> call_operation (the (c_calls c))"

text "The following function converts "

definition toplevel_spec :: "('op, 'op, 'res) ccrdtSpec \<Rightarrow>  ('op, 'res, 'a) operationContext_scheme \<Rightarrow> callId set \<Rightarrow> 'op \<Rightarrow> 'res  \<Rightarrow> bool" where
"toplevel_spec S ctxt vis op  \<equiv> S op vis (extract_op (calls ctxt)) (happensBefore ctxt) id"




text "There is a mapping between the composable CRDT specs above and the original specifications:"



lemma extract_op_def':
"extract_op (c_calls::('b \<Rightarrow> ('a, 'c) call option)) c 
  = ( case c_calls c of Some (Call op r) \<Rightarrow> op | _ \<Rightarrow> call_operation (the (None :: ('a, 'c) call option)))"
  by (auto simp add: extract_op_def split: option.splits call.splits) 


lemma extract_op_eq:
  assumes "c\<in>dom c_calls"
  shows "extract_op c_calls c = oper \<longleftrightarrow> (\<exists>res. c_calls c \<triangleq> Call oper res)"
  using assms by (auto simp add: extract_op_def' split: option.splits call.splits)




lemma calls_sub_context:
  "calls (sub_context C_in Cs ctxt) = 
(\<lambda>c. (calls ctxt |` Cs) c \<bind> (\<lambda>call. case C_in (call_operation call) of None \<Rightarrow> None | Some op' \<Rightarrow> Some (Call op' (call_res call))))
"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def ctxt_restrict_calls_def 
      option_bind_def 
      split: option.splits call.splits)

lemma happens_before_sub_context:
  "(x,y) \<in> happensBefore (sub_context C_in Cs ctxt) 
\<longleftrightarrow> ((x,y) \<in> happensBefore ctxt \<and> x\<in>dom (calls (sub_context  C_in Cs ctxt)) \<and> y\<in>dom (calls (sub_context  C_in Cs ctxt)))
"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def
 ctxt_restrict_calls_def restrict_map_def restrict_relation_def option_bind_def 
 split: if_splits option.splits call.splits)


lemma dom_calls_sub_context_rewrite: "(dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs)
  = (dom (calls (sub_context C_in Cs ctxt)))"
  by (auto simp add: calls_sub_context option_bind_def map_chain_def restrict_map_def  split: option.splits if_splits)



lemma extract_op_to_call:
  assumes "is_reverse C_in C_out"
and "c\<in>dom (calls (sub_context C_in Cs ctxt))"
shows "extract_op (calls ctxt) c = C_out op
\<longleftrightarrow> (\<exists>r. calls ctxt c \<triangleq> Call (C_out op) r)"
  by (smt IntD2 assms(2) call.collapse call.sel(1) calls_sub_context domExists_simp domIff dom_calls_sub_context_rewrite extract_op_def is_none_bind is_none_simps(1) is_none_simps(2) option.sel restrict_in)

lemma extract_op_into_sub_context:
  assumes is_rev: "is_reverse C_in C_out"
and in_dom: "c\<in>dom (calls (sub_context C_in Cs ctxt))"
shows "extract_op (calls ctxt) c = C_out op
\<longleftrightarrow> (\<exists>r. calls (sub_context C_in Cs ctxt) c \<triangleq> Call op r)"
  using in_dom  apply (auto simp add: calls_sub_context restrict_map_def option_bind_def
 call_operation_def extract_op_def is_rev is_reverse_2
      split: option.splits if_splits call.splits)
  using is_rev is_reverse_1 by fastforce

lemma happens_before_into_sub_context:
  assumes is_rev: "is_reverse C_in C_out"
and in_dom_x: "x\<in>dom (calls (sub_context C_in Cs ctxt))"
and in_dom_y: "y\<in>dom (calls (sub_context C_in Cs ctxt))"
shows "(x,y) \<in> happensBefore ctxt
\<longleftrightarrow> (x,y) \<in> happensBefore (sub_context C_in Cs ctxt)"
  using in_dom_x in_dom_y  by (auto simp add:  restrict_map_def option_bind_def
 call_operation_def extract_op_def is_rev is_reverse_2
 happens_before_sub_context
      split: option.splits if_splits call.splits)



definition crdt_spec_rel :: "('opn, 'res) crdtSpec \<Rightarrow> ('op, 'opn, 'res) ccrdtSpec \<Rightarrow> bool" where
"crdt_spec_rel spec cspec \<equiv>
\<forall>C_in::'op \<rightharpoonup> 'opn. \<forall>C_out::'opn \<Rightarrow> 'op.
  is_reverse C_in C_out
  \<longrightarrow> 
  (\<forall>ctxt (outer_op::'op) (op::'opn) r Cs. 
       C_in outer_op \<triangleq> op
    \<longrightarrow> Cs \<subseteq> (dom ((map_map (calls ctxt) call_operation) \<ggreater> C_in))
    \<longrightarrow> operationContext_wf ctxt
    \<longrightarrow>
       (spec op (sub_context C_in Cs ctxt) r
    \<longleftrightarrow> cspec op Cs (extract_op (calls ctxt))  (happensBefore ctxt) C_out r))

"

lemmas use_crdt_spec_rel = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format]
lemmas use_crdt_spec_rel1 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD1]
lemmas use_crdt_spec_rel2 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD2]

lemma use_crdt_spec_rel_toplevel:
  assumes rel: "crdt_spec_rel spec cspec"
    and hb_wf: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
    and "operationContext_wf ctxt"
  shows "spec op ctxt r 
 =  cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  r"
proof (fuzzy_rule use_crdt_spec_rel[OF rel])
  show "is_reverse Some id"
    by (simp add: is_reverse_def)

  show "Some op \<triangleq> op"
    by simp

  show "dom (calls ctxt) \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> Some)"
    by (auto simp add: dom_map_map dom_map_chain)

  have h1: "calls (sub_context Some UNIV ctxt) =  calls ctxt "
    by (auto simp add: calls_sub_context)

  have h2: "happensBefore (sub_context Some UNIV ctxt) =  happensBefore ctxt "
    apply (auto simp add: happens_before_sub_context calls_sub_context)
     apply (meson FieldI1 domD hb_wf subsetD)
    by (meson FieldI2 domD hb_wf in_mono)


  from h1 h2
  show "sub_context Some (dom (calls ctxt)) ctxt = ctxt"
    by (simp add: ctxt_restrict_calls_def hb_wf restrict_map_noop restrict_relation_noop sub_context_def)

  show "operationContext_wf ctxt" using `operationContext_wf ctxt` .
qed



lemma show_crdt_spec_rel:
  assumes
  a: "\<And>C_in C_out  ctxt outer_op op r Cs.
\<lbrakk>is_reverse C_in C_out; 
operationContext_wf ctxt;
 C_in outer_op \<triangleq> op\<rbrakk> \<Longrightarrow>
     spec op (sub_context C_in Cs ctxt) r
 \<longleftrightarrow> cspec op (dom (calls (sub_context C_in Cs ctxt))) (extract_op (calls ctxt))  (happensBefore ctxt) C_out  r 
"
shows "crdt_spec_rel spec cspec"
  by (simp add: crdt_spec_rel_def assms dom_calls_sub_context_rewrite inf.absorb_iff2)


definition convert_spec ::  "('op, 'op, 'res) ccrdtSpec \<Rightarrow> ('op, 'res) crdtSpec" where
"convert_spec cspec op ctxt res \<equiv> 
  cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  res"


lemma crdt_spec_rel_convert:
  assumes rel: "crdt_spec_rel spec cspec"
    and field: "Field (happensBefore ctxt) \<subseteq> dom (calls (ctxt))"
    and "operationContext_wf ctxt"
  shows "spec op ctxt r = convert_spec cspec op ctxt r"
  unfolding convert_spec_def
proof -
  show "spec op ctxt r = cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  r" 
  proof (fuzzy_rule use_crdt_spec_rel[OF rel])
    show "is_reverse Some id"
      by (simp add: is_reverse_def)
    show "Some op \<triangleq> op"
      by simp
    show "dom (calls ctxt) \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> Some)"
      by (auto simp add: map_chain_def)
    have h1: "calls (sub_context Some UNIV ctxt) = calls ctxt "
      by (auto simp add: calls_sub_context)

    have h2: "happensBefore (sub_context Some UNIV ctxt) = happensBefore ctxt "
      using field by (auto simp add: happens_before_sub_context
          FieldI1 FieldI2 h1 domD subset_h1)

    from h1 h2
    show "sub_context Some (dom (calls ctxt)) ctxt = ctxt"
      by (simp add: ctxt_restrict_calls_def field restrict_map_noop restrict_relation_noop sub_context_def)


    show "operationContext_wf ctxt"
      by (simp add: assms)
  qed
qed



definition ccrdtSpec_wf :: "('op, 'opn, 'res) cOperationResultSpec \<Rightarrow> bool" where
"ccrdtSpec_wf spec  \<equiv> 
\<forall>Cs op op' hb hb' C_out r. 
map_same_on Cs op op'
\<longrightarrow> rel_same_on Cs hb hb'
\<longrightarrow> (     spec Cs op  hb  C_out r 
     \<longleftrightarrow>  spec Cs op' hb' C_out r)"



lemmas use_ccrdtSpec_wf = ccrdtSpec_wf_def[unfolded atomize_eq, THEN iffD1, rule_format]
lemmas use_ccrdtSpec_wf1 = ccrdtSpec_wf_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD1]
lemmas use_ccrdtSpec_wf2 = ccrdtSpec_wf_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD2]


lemma ccrdtSpec_wf_split_ops:
  assumes "\<And>x. ccrdtSpec_wf (\<lambda>i. f x)"
  shows "ccrdtSpec_wf f"
  using assms by (auto simp add: ccrdtSpec_wf_def)


end