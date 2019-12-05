theory crdt_specs2
  imports crdt_specs
 "fuzzyrule.fuzzyrule"
begin

section "CRDT Specifications Part 2"

text "The previous CRDT are not nice to work with when composed.
The problem is, that the specifications for maps and structs transform the context
passed to embedded CRDTs.
During this transformation the reverse direction is lost, so it is hard to reconstruct the original
calls from the calls in an embedded context.
Therefore, we now use a different composition technique, where the mapping is explicitly passed down
into nested CRDTs."

type_synonym ('op, 'opn, 'res) cOperationResultSpec = 
        "callId set                  \<comment> \<open>visible calls\<close>
      \<Rightarrow> (callId \<Rightarrow>'op)              \<comment> \<open>call information\<close> 
      \<Rightarrow> callId rel                  \<comment> \<open>happens-before\<close>
      \<Rightarrow> ('opn \<Rightarrow> 'op)               \<comment> \<open>mapping back\<close>
      \<Rightarrow> 'res
      \<Rightarrow> bool"

type_synonym ('op, 'opn, 'res) ccrdtSpec = 
        "'opn \<Rightarrow> ('op, 'opn, 'res) cOperationResultSpec"

text "There is a mapping between the composable CRDT specs above and the original specifications:"

definition 
"extract_op c_calls c \<equiv>  case c_calls c of Some (Call op r) \<Rightarrow> op"

(* TODO utils *)
lemma option_bind_def:
"(x \<bind> f) = (case x of None \<Rightarrow> None | Some a \<Rightarrow> f a)"
  by (metis bind.bind_lunit bind_eq_None_conv option.case_eq_if option.exhaust_sel)

(* TODO
so far the relation is only without nesting (for identity mapping.
Must add the mapping to both sides of the equation
left through transforming the context, right through C directly

best to prove equivalence for the map first and see what is required
 *)

(* TODO utils *)
definition map_chain ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" (infixr "\<ggreater>" 54) where
"(f \<ggreater> g) \<equiv> \<lambda>x. f x \<bind> g"

definition map_map ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" where
"(map_map f g) \<equiv> \<lambda>x. map_option g (f x)"

lemma dom_map_chain: 
"dom (f \<ggreater> g) = {x | x y z. f x \<triangleq> y \<and> g y \<triangleq> z}"
  by (auto simp add: map_chain_def option_bind_def split: option.splits)

lemma dom_map_map[simp]: 
"dom (map_map f g) = dom f"
  by (auto simp add: map_map_def)

lemma map_map_apply_eq_some[simp]:
"(map_map f g x \<triangleq> z) \<longleftrightarrow> (\<exists>y. f x \<triangleq> y \<and> g y = z)"
  by (auto simp add: map_map_def split: option.splits)

lemma map_map_apply_eq_none[simp]:
"(map_map f g x = None) \<longleftrightarrow> (f x = None)"
  by (auto simp add: map_map_def split: option.splits)


lemma map_map_apply:
"map_map f g x = (case f x of None \<Rightarrow> None | Some y \<Rightarrow> Some (g y))"
  by (auto simp add: map_map_def split: option.splits)



definition is_reverse :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
"is_reverse f_in f_out \<equiv> 
  (\<forall>x y. ((f_in x) \<triangleq> y) \<longrightarrow> (f_out y = x))
  \<and> (\<forall>x.  (f_in (f_out x)) \<triangleq> x)"

lemma is_reverse_1:
  assumes "is_reverse f_in f_out"
    and "f_in x \<triangleq> y"
  shows "f_out y = x"
  by (meson assms is_reverse_def)


lemma is_reverse_2:
  assumes "is_reverse f_in f_out"
  shows "f_in (f_out x) \<triangleq> x"
  by (meson assms is_reverse_def)


lemma is_reverse_combine:
  assumes is_rev: "is_reverse C_in C_out"
    and is_rev': "is_reverse C_in' C_out'"
    shows "is_reverse (C_in' \<ggreater> C_in) (C_out' \<circ> C_out)"
  by (smt bind_eq_Some_conv comp_apply is_rev is_rev' is_reverse_def map_chain_def)




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
  by (smt IntD2 assms(2) call.collapse call.sel(1) call_operation_def calls_sub_context domD domIff dom_calls_sub_context_rewrite extract_op_def is_none_bind is_none_simps(1) is_none_simps(2) option.simps(5) restrict_in)

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
    \<longrightarrow>
       (spec op (sub_context C_in Cs ctxt) r
    \<longleftrightarrow> cspec op (dom ((map_map (calls ctxt) call_operation) \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt))  (happensBefore ctxt) C_out r))

"

lemmas use_crdt_spec_rel = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format]
lemmas use_crdt_spec_rel1 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD1]
lemmas use_crdt_spec_rel2 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD2]

lemma use_crdt_spec_rel_toplevel:
  assumes rel: "crdt_spec_rel spec cspec"
    and hb_wf: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  shows "spec op ctxt r 
 =  cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  r"
proof (fuzzy_rule use_crdt_spec_rel[OF rel])
  show "is_reverse Some id"
    by (simp add: is_reverse_def)

  show "Some op \<triangleq> op"
    by simp

  show "dom (map_map (calls ctxt) call_operation \<ggreater> Some) \<inter> UNIV = dom (calls ctxt)"
    by (auto simp add: dom_map_map dom_map_chain)

  have h1: "calls (sub_context Some UNIV ctxt) =  calls ctxt "
    by (auto simp add: calls_sub_context)

  have h2: "happensBefore (sub_context Some UNIV ctxt) =  happensBefore ctxt "
    apply (auto simp add: happens_before_sub_context calls_sub_context)
     apply (meson FieldI1 domD hb_wf subsetD)
    by (meson FieldI2 domD hb_wf in_mono)


  from h1 h2
  show "sub_context Some UNIV ctxt = ctxt "
    by auto
qed



lemma show_crdt_spec_rel:
  assumes
  a: "\<And>C_in C_out  ctxt outer_op op r Cs.
\<lbrakk>is_reverse C_in C_out; 
 C_in outer_op \<triangleq> op\<rbrakk> \<Longrightarrow>
     spec op (sub_context C_in Cs ctxt) r
 \<longleftrightarrow> cspec op (dom (calls (sub_context C_in Cs ctxt))) (extract_op (calls ctxt))  (happensBefore ctxt) C_out  r 
"
shows "crdt_spec_rel spec cspec"
  by (simp add: a crdt_spec_rel_def dom_calls_sub_context_rewrite)


definition convert_spec ::  "('op, 'op, 'res) ccrdtSpec \<Rightarrow> ('op, 'res) crdtSpec" where
"convert_spec cspec op ctxt res \<equiv> 
  cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  res"


lemma crdt_spec_rel_convert:
  assumes rel: "crdt_spec_rel spec cspec"
    and field: "Field (happensBefore ctxt) \<subseteq> dom (calls (ctxt))"
  shows "spec op ctxt r = convert_spec cspec op ctxt r"
  unfolding convert_spec_def
proof -
  show "spec op ctxt r = cspec op (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id  r" 
  proof (fuzzy_rule use_crdt_spec_rel[OF rel])
    show "is_reverse Some id"
      by (simp add: is_reverse_def)
    show "Some op \<triangleq> op"
      by simp
    show "dom (map_map (calls ctxt) call_operation \<ggreater> Some) \<inter> UNIV = dom (calls ctxt)"
      by (auto simp add: map_chain_def map_map_apply_eq_some)
    have h1: "calls (sub_context Some UNIV ctxt) = calls ctxt "
      by (auto simp add: calls_sub_context)

    have h2: "happensBefore (sub_context Some UNIV ctxt) = happensBefore ctxt "
      using field by (auto simp add: happens_before_sub_context
          FieldI1 FieldI2 h1 domD subset_h1)

    from h1 h2
    show "sub_context Some UNIV ctxt = ctxt "
      by auto
  qed
qed



subsection "Register"

definition latest_assignments' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> ('v registerOp \<Rightarrow> 'op) \<Rightarrow> (callId \<times> 'v) set"  where
"latest_assignments' vis op hb C \<equiv> 
   {(c,v). c\<in>vis \<and> op c = C (Assign v) \<and> (\<nexists>c' v'. c'\<in>vis \<and> op c' = C (Assign v') \<and> (c,c')\<in>hb)}"

definition
"latest_values' vis op hb C \<equiv> snd ` (latest_assignments' vis op hb C)"

definition register_spec' :: "('res::default) \<Rightarrow> ('op, 'res registerOp, 'res) ccrdtSpec" where
"register_spec' initial oper vis op hb C  res \<equiv>
  case oper of
    Assign _ \<Rightarrow> res = default
  | Read \<Rightarrow>
      if latest_values' vis op hb C = {} then res = initial else res \<in> latest_values' vis op hb C"


definition firstValue' :: "'a \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> 'a" where
"firstValue' d m \<equiv> if m = {} then d else 
  let maxK = wo_rel.minim some_well_order (fst ` m) in
  wo_rel.minim some_well_order {y. (maxK,y)\<in>m}
  "

lemma firstValue'_to_firstValue:
  shows
    "firstValue' initial {(x, y). f x \<triangleq> y}
     = firstValue initial f"
proof (auto simp add: firstValue'_def firstValue_def)

  fix a y
  assume c0: "f a \<triangleq> y"
    and c1: "f \<noteq> Map.empty"
  have h1: "(fst ` {(x, y). f x \<triangleq> y}) =  (dom f)"
    by (auto simp add: image_iff)


  show "wo_rel.minim some_well_order {y. f (wo_rel.minim some_well_order (fst ` {(x, y). f x \<triangleq> y})) \<triangleq> y} 
      = the (f (wo_rel.minim some_well_order (dom f)))"
    apply (auto simp add: h1)
    by (smt c1 domIff dom_eq_empty_conv mem_Collect_eq option.exhaust_sel option.sel some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)

qed



definition lww_register_spec' :: "('v::default) \<Rightarrow> ('op, 'v registerOp, 'v) ccrdtSpec" where
"lww_register_spec' initial oper vis op hb C  res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> res = firstValue' initial (latest_assignments' vis op hb C)"


lemma wo_rel_minim_singleton:
  assumes "S = {y}"
  shows "wo_rel.minim some_well_order S = y"
  by (metis assms insert_not_empty singletonD some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)

lemma wo_rel_minim_singleton2:
  assumes "f \<triangleq> y"
  shows "wo_rel.minim some_well_order {y. f \<triangleq> y} = y"
  by (metis (mono_tags, lifting) assms emptyE mem_Collect_eq option.sel some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)

lemma map_chain_eq_some: 
  "((f \<ggreater> g) x \<triangleq> z) \<longleftrightarrow> (\<exists>y. f x \<triangleq> y \<and> g y \<triangleq> z)"
  by (simp add: bind_eq_Some_conv map_chain_def)



lemma  latest_assignments_rel: 
  assumes is_rev: "is_reverse C_in C_out"
  shows "(latest_assignments' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out)
      = {(x,y) | x y. latestAssignments (sub_context C_in Cs ctxt) x \<triangleq> y}"
proof (auto simp add: latest_assignments'_def latestAssignments_def  latestAssignments_h_def 
    map_chain_eq_some dom_def
    split: option.splits registerOp.splits call.splits, 
    goal_cases A B C D E F G H)
  case (A a b y)
  then show ?case
    by (simp add: calls_sub_context)
next
  case (B a b y x1a c' v' r' x2)
  then show ?case 
    apply (auto simp add: calls_sub_context option_bind_def restrict_map_def happens_before_sub_context split: if_splits option.splits)
    by (metis (mono_tags, lifting) call_operation_def extract_op_def is_rev is_reverse_1 option.simps(5))
next
  case (C a b y x1a x2)
  then show ?case 
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits)

next
  case (D a b y x2)
  then show ?case 
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits)
next
  case (E a b x2a x1a)
  then show ?case
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits)
next
  case (F a b x2a x1a)
  then show ?case 
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits)
next
  case (G a b x2a x1a)
  then show ?case 
    apply (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits call.splits)
    using is_rev is_reverse_1 by fastforce

next
  case (H a b c' y v' x2a x1a)
  then show ?case 
    apply (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2  split: if_splits option.splits call.splits)
    by (metis (mono_tags, lifting) H(5) bind.bind_lunit call.sel(1) calls_sub_context domI happens_before_sub_context option.simps(5) restrict_map_def)
qed

lemma lww_register_spec_rel:
"crdt_spec_rel (lww_register_spec initial) (lww_register_spec' initial) "
  unfolding crdt_spec_rel_def
  by (auto simp add: lww_register_spec_def lww_register_spec'_def 
          latest_assignments_rel firstValue'_to_firstValue split: registerOp.splits)


subsection "Sets"

definition set_rw_spec' :: "(bool \<Rightarrow> 'r) \<Rightarrow> ('op, 'v setOp, ('r::default)) ccrdtSpec" where
"set_rw_spec' from_bool oper vis op hb C  res \<equiv> 
  case oper of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool 
        (\<exists>a\<in>vis. op a = C (Add v)
           \<and> (\<forall>r\<in>vis. op r = C (Remove v)
                 \<longrightarrow> (\<exists>a'\<in>vis. op a' = C (Add v) \<and> (r,a')\<in>hb)))"


lemma set_rw_spec_rel:
  shows "crdt_spec_rel (set_rw_spec from_bool) (set_rw_spec' from_bool) "
  apply (rule show_crdt_spec_rel)
  by (auto simp add: set_rw_spec_def set_rw_spec'_def 
      extract_op_into_sub_context happens_before_into_sub_context
      split: setOp.splits intro!: arg_cong[where f="from_bool"])




subsection "Maps"


definition deleted_calls_dw' :: "callId set \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set" where
"deleted_calls_dw' vis op hb C k \<equiv> {c\<in>vis. \<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb}"

definition 
"restrict_calls vis op C k \<equiv>
{c\<in>vis. \<exists>u. op c = C (NestedOp k u) }"

definition map_spec' :: "
      (callId set  \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set) 
    \<Rightarrow> (bool \<Rightarrow> 'r)
    \<Rightarrow> ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::default)) ccrdtSpec" where
"map_spec' deleted_calls from_bool nestedSpec oper vis op hb C res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c\<in>vis. \<exists>upd_op. op c = C (NestedOp k upd_op) \<and> is_update upd_op \<and>  c \<notin> deleted_calls vis op hb C k)
  | NestedOp k nested_op \<Rightarrow>
     nestedSpec nested_op (restrict_calls vis op C k - deleted_calls vis op hb C k) op hb (\<lambda>x. C (NestedOp k x))  res
"


definition map_dw_spec' :: "
       (bool \<Rightarrow> 'r)
    \<Rightarrow> ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::default)) ccrdtSpec" where
"map_dw_spec' \<equiv>  map_spec' deleted_calls_dw'"



lemma subcontext_calls:
  assumes in_out: "is_reverse C_in C_out"
  shows "(calls (sub_context C_in Cs ctxt) c \<triangleq> Call op r)
     \<longleftrightarrow> (calls ctxt c \<triangleq> Call (C_out op) r \<and> c\<in>Cs \<and> C_in (C_out op) \<triangleq> op)"

  by (auto simp add:   sub_context_def restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def ctxt_restrict_calls_def restrict_map_def option_bind_def split: option.splits call.splits,
      (simp add: in_out[simplified is_reverse_def])+)

lemma subcontext_of_subcontext_collapse:
"sub_context C_inA CsA (sub_context C_inB CsB ctxt)
= sub_context (\<lambda>x. C_inB x \<bind> C_inA) (CsA \<inter> CsB) ctxt"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def 
      fmap_map_values_def ctxt_restrict_calls_def restrict_map_def option_bind_def
      restrict_relation_def
      intro!: ext split: option.splits call.splits)


lemma deleted_calls_dw_rel:
  assumes "is_reverse C_in C_out"
  assumes "L = deleted_calls_dw (sub_context C_in Cs ctxt) k"
and "R = deleted_calls_dw' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "L = R"
  by (auto simp add: deleted_calls_dw_def deleted_calls_dw'_def sub_context_def assms restrict_ctxt_op_def restrict_ctxt_def
      fmap_map_values_def option_bind_def ctxt_restrict_calls_def restrict_map_def
      restrict_relation_def extract_op_def  map_map_def map_chain_def
      split: option.splits call.splits if_splits,
   (smt IntI assms(1) call.collapse call.sel(1) domExists_simp domIff is_reverse_def o_apply option.case_eq_if option.sel),
   (metis assms(1) is_reverse_2 option.distinct(1) option.inject),
   (metis assms(1) is_reverse_2 option.distinct(1) option.sel))






lemma map_spec_rel:
  fixes nestedSpec :: "('opn::crdt_op, 'res::default) crdtSpec"
    and nestedSpec' :: "('op, 'opn, 'res) ccrdtSpec"
    and deletedCalls :: "(('k, 'opn) mapOp, 'res) operationContext \<Rightarrow> 'k \<Rightarrow> callId set"
    and deletedCalls' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set"
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
and deletedCalls_rel: 
    "\<And>ctxt C_in C_out Cs k. is_reverse C_in C_out \<Longrightarrow>
          deleted_calls (sub_context C_in Cs ctxt) k
        = deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "crdt_spec_rel (map_spec deleted_calls from_bool nestedSpec) (map_spec' deleted_calls' from_bool nestedSpec') "
  unfolding crdt_spec_rel_def
proof (intro allI impI)

  show "map_spec deleted_calls from_bool nestedSpec op (sub_context C_in Cs ctxt) r 
     = map_spec' deleted_calls' from_bool nestedSpec' op (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out  r"
      (is "?l = ?r")
    if is_rev: "is_reverse C_in C_out"
      and in_out: "C_in outer_op \<triangleq> op"
    for  C_in C_out ctxt outer_op op r Cs
  proof -


    show "?l = ?r"
    proof (cases op)
      case (NestedOp k nestedOp)


      have h1: "((restrict_calls (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) C_out k)
                   - deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k) = 
            {c \<in> dom (calls ctxt). c \<in> Cs \<and> (\<exists>u. extract_op (calls ctxt) c = C_out (NestedOp k u)) 
               \<and> c \<notin> deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k}
              " 
         by (auto simp add: restrict_calls_def)




      show ?thesis 
      proof (simp add: NestedOp h1 map_spec_def map_spec'_def subcontext_calls[OF is_rev] deletedCalls_rel subcontext_of_subcontext_collapse)

        show "nestedSpec nestedOp (sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs) ctxt) r =
            nestedSpec' nestedOp
             (restrict_calls (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) C_out k -
              deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x))  r"
        proof (subst use_crdt_spec_rel[OF nested_rel])        

          show is_rev_combined: "is_reverse (\<lambda>x. C_in x \<bind> nested_op_on_key k) (\<lambda>x. C_out (NestedOp k x))"
            by (auto simp add: is_reverse_def option_bind_def nested_op_on_key_def 
                is_reverse_1[OF is_rev] is_reverse_2[OF is_rev] split: option.splits mapOp.splits)

          show "(C_in (C_out (NestedOp k nestedOp)) \<bind> nested_op_on_key k) \<triangleq> nestedOp"
            using is_rev_combined is_reverse_def by fastforce

          have h1: "deleted_calls (sub_context C_in Cs ctxt) k
              = deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            by (rule deletedCalls_rel[OF is_rev])




          have h4: "
             (dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter> (- DC  \<inter> Cs) )
             =
             ({c \<in> dom (map_map (calls ctxt) call_operation \<ggreater> C_in).
               c \<in> Cs \<and> (\<exists>u. extract_op (calls ctxt) c = C_out (NestedOp k u))} - DC)"
            if "DC = deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            for DC
            apply (auto simp add: map_map_def map_chain_def option_bind_def split: option.splits)
             apply (auto simp add: nested_op_on_key_def extract_op_def split: option.splits mapOp.splits if_splits call.splits)
               apply (auto simp add: is_reverse_2[OF is_rev])
            using is_rev is_reverse_1 by fastforce



          show "nestedSpec' nestedOp
               (dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter>
                (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs))
               (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x))  r =
              nestedSpec' nestedOp
               (restrict_calls (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) C_out k -
                deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
               (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x))  r"
            by (simp add: h1 h4 restrict_calls_def)
        qed
      qed

    next
      case (KeyExists k)
      show ?thesis 
      proof (simp add: KeyExists map_spec_def map_spec'_def, 
              subst deletedCalls_rel[OF is_rev],
              rule arg_cong[where f="\<lambda>x. r = from_bool x"])

        show "(\<exists>c op.
                (\<exists>r. calls (sub_context C_in Cs ctxt) c \<triangleq> Call (NestedOp k op) r) \<and>
                is_update op \<and>
                c \<notin> deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt))
                      (happensBefore ctxt) C_out k) =
            (\<exists>c\<in>dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs.
                \<exists>upd_op.
                   extract_op (calls ctxt) c = C_out (NestedOp k upd_op) \<and>
                   is_update upd_op \<and>
                   c \<notin> deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt))
                         (happensBefore ctxt) C_out k)"
        proof (auto simp add: Bex_def calls_sub_context option_bind_def dom_map_chain restrict_map_def split: option.splits, goal_cases A B)
          case (A c y)
          show ?case
            apply (auto intro!: exI[where x=c])
            using A(1) A(2) apply auto[1]
            using A(1) apply blast
          proof -
            obtain zz :: "('a, 'opn) mapOp \<Rightarrow> 'opn" where
              f1: "C_in (call_operation y) \<noteq> None \<and> (\<forall>m. C_in (call_operation y) \<noteq> Some m \<or> (c \<notin> Cs \<or> m = NestedOp k (zz m) \<and> is_update (zz m) \<and> c \<notin> deleted_calls' ({c. \<exists>z. (\<exists>ca. calls ctxt c \<triangleq> ca \<and> call_operation ca = z) \<and> (\<exists>m. C_in z \<triangleq> m)} \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k) \<and> c \<in> Cs)"
              using A(1) by moura
            then obtain mm :: "('a, 'opn) mapOp option \<Rightarrow> ('a, 'opn) mapOp" and zza :: "('a, 'opn) mapOp \<Rightarrow> 'opn" where
              f2: "mm (C_in (call_operation y)) = NestedOp k (zza (mm (C_in (call_operation y)))) \<and> is_update (zza (mm (C_in (call_operation y)))) \<and> c \<notin> deleted_calls' ({c. \<exists>z. (\<exists>ca. calls ctxt c \<triangleq> ca \<and> call_operation ca = z) \<and> (\<exists>m. C_in z \<triangleq> m)} \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
              by auto
            have f3: "\<forall>f fa. is_reverse f fa = ((\<forall>z m. f (z::'op) \<noteq> Some (m::('a, 'opn) mapOp) \<or> fa m = z) \<and> (\<forall>m. f (fa m) \<triangleq> m))"
              by (simp add: is_reverse_def)
            have f4: "(case calls ctxt c of None \<Rightarrow> ??? | Some (Call z r) \<Rightarrow> z) = call_operation y"
              by (simp add: A(2) call_operation_def)
            obtain mma :: "('a, 'opn) mapOp option \<Rightarrow> ('a, 'opn) mapOp" where
              f5: "C_in (call_operation y) \<triangleq> mma (C_in (call_operation y))"
              using f1 by (meson option.exhaust)
            then have "extract_op (calls ctxt) c = C_out (mma (C_in (call_operation y)))"
              using f4 f3 by (metis (no_types) extract_op_def is_rev)
            then show "\<exists>z. extract_op (calls ctxt) c = C_out (NestedOp k z) \<and> is_update z \<and> c \<notin> deleted_calls' ({c. \<exists>z. (\<exists>ca. calls ctxt c \<triangleq> ca \<and> call_operation ca = z) \<and> (\<exists>m. C_in z \<triangleq> m)} \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
              using f5 f1 by force
          qed

        next
          case (B c upd_op ya z)
          show ?case
            apply (rule exI[where x=c], auto)
            using B apply auto
            by (metis call_operation_def extract_op_def is_rev is_reverse_2 option.inject option.simps(5))

        qed
      qed
    next
      case (DeleteKey k)
      then show ?thesis
        by (auto simp add: map_spec_def map_spec'_def)
    qed


  qed
qed



lemma map_dw_spec_rel:
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
shows "crdt_spec_rel (map_dw_spec from_bool nestedSpec) (map_dw_spec' from_bool nestedSpec') "
  by (smt deleted_calls_dw_rel map_dw_spec'_def map_dw_spec_def map_spec_rel nested_rel)


subsection "Structs"

definition struct_field' :: "('opn \<Rightarrow> 'a) \<Rightarrow> ('op, 'opn, 'res) cOperationResultSpec \<Rightarrow> ('op, 'a, 'res) cOperationResultSpec "  where
"struct_field' C_out spec  \<equiv> 
  \<lambda> vis op hb x_C_out res.
    spec {c\<in>vis. \<exists>x. op c = x_C_out (C_out x)} op hb (x_C_out \<circ> C_out)  res"


lemma struct_field_eq:
  assumes rel: "crdt_spec_rel nspec nspec'"
    and is_rev: "is_reverse C_in C_out"
    and is_rev': "is_reverse C_in' C_out'"

shows "struct_field (nspec n_op) C_in ctxt res 
      =  struct_field' C_out (nspec' n_op) c_calls op hb C_out' res"
proof (simp add: struct_field_def struct_field'_def)
  show "nspec n_op (restrict_ctxt_op C_in ctxt) res =
    nspec' n_op {c \<in> c_calls. \<exists>x. op c = C_out' (C_out x)} op hb (C_out' \<circ> C_out) res"
  proof (fuzzy_rule use_crdt_spec_rel[OF rel])


    show "is_reverse (C_in' \<ggreater> C_in) (C_out' \<circ> C_out)"
      by (simp add: is_rev is_rev' is_reverse_combine)

    define complete_ctxt where "complete_ctxt =  \<lparr>calls = (\<lambda>c. if c\<in>c_calls then Some (Call (op c) (call_res (the (calls ctxt c)))) else None), happensBefore = hb\<rparr> "

    show "happensBefore complete_ctxt = hb"
      by (auto simp add: complete_ctxt_def)

    show "extract_op (calls complete_ctxt) = op"
      apply (auto simp add: complete_ctxt_def extract_op_def intro!: ext)
\<comment> \<open>TODO should be sufficient is op is equal on the relevant data, i.e. the given set c_Calls\<close>
      sorry

    show "(C_in' \<ggreater> C_in) (C_out' (C_out n_op)) \<triangleq> n_op"
      by (simp add: is_rev is_rev' is_reverse_2 map_chain_def)

\<comment> \<open>Restrict ctxt to be a subcontext?\<close>
    show " sub_context (C_in' \<ggreater> C_in) c_calls complete_ctxt  = restrict_ctxt_op C_in ctxt"
      apply (auto simp add: operationContext_ext calls_sub_context happens_before_sub_context complete_ctxt_def)
          apply (auto simp add: option_bind_def restrict_ctxt_op_def restrict_map_def 
          map_chain_def restrict_ctxt_def fmap_map_values_def
          intro!: ext split: if_splits option.splits call.splits)

      sorry

    show "dom (map_map
          (calls
            complete_ctxt)
          call_operation \<ggreater>
         C_in' \<ggreater> C_in) \<inter>
    c_calls =
    {c \<in> c_calls. \<exists>x. op c = C_out' (C_out x)}"
      apply (auto simp add: map_map_def map_chain_def option_bind_def complete_ctxt_def split: option.splits)
        apply (metis is_rev is_rev' is_reverse_1)
       apply (meson is_rev' is_reverse_def)
      by (metis is_rev is_rev' is_reverse_2 option.sel)


  qed 
qed




end