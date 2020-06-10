section "CRDT Specifications Part 2"
theory crdt_specs2
  imports crdt_specs
    crdt_specs_v
    "fuzzyrule.fuzzyrule"
    "fuzzyrule.fuzzy_goal_cases"
begin


text "We now relate the original CRDT specifications and the ones that are better
suited for verification of applications."



subsection "Register"

definition latest_assignments' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> ('v registerOp \<Rightarrow> 'op) \<Rightarrow> (callId \<times> 'v) set"  where
"latest_assignments' vis op hb C \<equiv> 
   {(c,v). c\<in>vis \<and> op c = C (Assign v) \<and> (\<nexists>c' v'. c'\<in>vis \<and> op c' = C (Assign v') \<and> (c,c')\<in>hb)}"

definition
"latest_values' vis op hb C \<equiv> snd ` (latest_assignments' vis op hb C)"


lemma latest_assignments'_exists:
  assumes fin: "finite vis"
    and acyclic: "acyclic hb"
    and a: "\<exists>c y. c\<in>vis \<and> op c = C (Assign y)"
  shows "\<exists>x. x\<in> latest_assignments' vis op hb C"
proof (auto simp add: latest_assignments'_def)

  define all_assignments where "all_assignments \<equiv> {c\<in>vis. \<exists>y. op c = C (Assign y)}"

  have "all_assignments \<noteq> {}"
    using a by (auto simp add: all_assignments_def)

  have "finite all_assignments"
    by (rule finite_subset[rotated, OF fin], auto simp add: all_assignments_def)

  obtain c 
    where c_in: "c \<in> all_assignments"
      and c_max: "\<forall>c'\<in>all_assignments. \<not>(c,c')\<in>hb"
    by (metis (mono_tags, lifting) \<open>finite all_assignments\<close> a acyclic all_assignments_def exists_max mem_Collect_eq)

  hence "c \<in> vis \<and> (\<exists>b. op c = C (Assign b)) \<and> (\<forall>c'. c' \<in> vis \<longrightarrow> (\<forall>v'. op c' \<noteq> C (Assign v')) \<or> (c, c') \<notin> hb)"
    by (auto simp add: all_assignments_def)

  thus "\<exists>a. a \<in> vis \<and> (\<exists>b. op a = C (Assign b)) \<and> (\<forall>c'. c' \<in> vis \<longrightarrow> (\<forall>v'. op c' \<noteq> C (Assign v')) \<or> (a, c') \<notin> hb)" ..
qed


lemma latest_values'_exists:
  assumes fin: "finite vis"
    and acyclic: "acyclic hb"
    and a: "\<exists>c y. c\<in>vis \<and> op c = C (Assign y)"
  shows "\<exists>x. x\<in> latest_values' vis op hb C"
  unfolding latest_values'_def
  using a acyclic fin latest_assignments'_exists by fastforce



definition register_spec' :: "('res::default) \<Rightarrow> ('op, 'res registerOp, 'res) ccrdtSpec" where
"register_spec' initial oper vis op hb C  res \<equiv>
  case oper of
    Assign _ \<Rightarrow> res = default
  | Read \<Rightarrow>
      is_from res initial (latest_values' vis op hb C)"


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

  have h1: "(fst ` {(x, y). f x \<triangleq> y}) =  (dom f)"
    by (auto simp add: image_iff)


  show "wo_rel.minim some_well_order {y. f (wo_rel.minim some_well_order (fst ` {(x, y). f x \<triangleq> y})) \<triangleq> y} 
      = the (f (wo_rel.minim some_well_order (dom f)))"

  proof (cases "f = Map.empty")
    case True
    then show ?thesis
      using c0 by (auto simp add: h1)
  next
    case False
    then show ?thesis 
      by (auto simp add: h1, smt False domIff dom_eq_empty_conv mem_Collect_eq option.exhaust_sel option.sel some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)
  qed
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
    map_chain_eq_some dom_def Op_def
    split: option.splits registerOp.splits call.splits, 
    fuzzy_goal_cases A B C D E F G H)
  case (A a b y)
  then show ?case
    by (simp add: calls_sub_context)
next
  case (B a b y x1a c' v' r' x2)
  then show ?case 
    apply (auto simp add: calls_sub_context option_bind_def restrict_map_def happens_before_sub_context split: if_splits option.splits)
    by (metis (mono_tags, lifting) call_operation_def extract_op_def' is_rev is_reverse_1 option.simps(5))
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


lemma  latest_assignments_rel2: 
  assumes is_rev: "is_reverse C_in C_out"
    and Cs_subset: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
  shows "(latest_assignments' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out)
      = {(x,y) | x y. latestAssignments (sub_context C_in Cs ctxt) x \<triangleq> y}"
  by (metis (mono_tags, lifting) Collect_cong Cs_subset inf.absorb_iff2 is_rev latest_assignments_rel)


lemma lww_register_spec_rel:
"crdt_spec_rel (lww_register_spec initial) (lww_register_spec' initial) "
  unfolding crdt_spec_rel_def
  by (auto simp add: lww_register_spec_def lww_register_spec'_def 
          latest_assignments_rel2 firstValue'_to_firstValue split: registerOp.splits)


lemma latestValues_rel:
  assumes is_rev: "is_reverse C_in C_out"
    and subset: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
shows "latestValues (sub_context C_in Cs ctxt)
     = latest_values' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out"
  by (auto simp add: latestValues_def latest_values'_def latest_assignments_rel2[OF is_rev subset] ran_def in_img_simp)

lemma register_spec_rel:
"crdt_spec_rel (register_spec initial) (register_spec' initial) "
  unfolding crdt_spec_rel_def
  by (auto simp add: register_spec_def register_spec'_def is_from_def
          latestValues_rel firstValue'_to_firstValue split: registerOp.splits)



lemma latest_assignments'_wf:
  assumes "map_same_on Cs op op'"
and "rel_same_on Cs hb hb'"
shows " latest_assignments' Cs op hb C_out =  latest_assignments' Cs op' hb' C_out"
  using assms by (auto simp add: latest_assignments'_def  map_same_on_def rel_same_on_def)


lemma latest_values'_wf:
  assumes "map_same_on Cs op op'"
and "rel_same_on Cs hb hb'"
shows " latest_values' Cs op hb C_out =  latest_values' Cs op' hb' C_out"
  by (auto simp add: latest_values'_def latest_assignments'_wf[OF assms])


lemma register_spec_wf[simp]:
"ccrdtSpec_wf (register_spec' i op)"
  by (auto simp add: ccrdtSpec_wf_def register_spec'_def latest_values'_wf split: registerOp.splits)

lemma lww_register_spec_wf[simp]:
"ccrdtSpec_wf (lww_register_spec' i op)"
  by (auto simp add: ccrdtSpec_wf_def lww_register_spec'_def latest_assignments'_wf split: registerOp.splits)





subsection "Sets"

definition set_rw_spec' :: "('op, 'v setOp, ('r::{default,from_bool})) ccrdtSpec" where
"set_rw_spec' oper vis op hb C  res \<equiv> 
  case oper of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool 
        (\<exists>a\<in>vis. op a = C (Add v)
           \<and> (\<forall>r\<in>vis. op r = C (Remove v)
                 \<longrightarrow> (\<exists>a'\<in>vis. op a' = C (Add v) \<and> (r,a')\<in>hb)))"


lemma sub_context_operationContext_wf:
  assumes wf: "operationContext_wf ctxt"
  shows "operationContext_wf (sub_context C_in Cs ctxt)"
  using wf
  unfolding operationContext_wf_def
proof (intro conjI; elim conjE)
  assume a0: "trans (happensBefore ctxt)"
    and a1: "wf ((happensBefore ctxt)\<inverse>)"
    and a2: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"


  show "trans (happensBefore (sub_context C_in Cs ctxt))"
    by (metis (mono_tags, lifting) a0 happens_before_sub_context trans_def)

  show " wf ((happensBefore (sub_context C_in Cs ctxt))\<inverse>)"
    by (metis a1 converse.cases converse.intros happens_before_sub_context wf_def)

  show "Field (happensBefore (sub_context C_in Cs ctxt)) \<subseteq> dom (calls (sub_context C_in Cs ctxt))"
    using a2
    by (auto simp add: sub_context_def restrict_ctxt_op_def ctxt_restrict_calls_def restrict_ctxt_def
          restrict_relation_def fmap_map_values_def restrict_map_def Field_def)


qed


lemma Op_subcontext:
"Op (sub_context C_in Cs ctxt) c \<triangleq> op
\<longleftrightarrow> (\<exists>op'. c\<in>Cs \<and> Op ctxt c \<triangleq> op' \<and> C_in op' \<triangleq> op)"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def Op_def 
      ctxt_restrict_calls_def restrict_map_def
      fmap_map_values_def option_bind_def split: option.splits call.splits)

lemma "calls (sub_context C_in Cs ctxt) c = ???"
  apply (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def Op_def 
      ctxt_restrict_calls_def restrict_map_def
      fmap_map_values_def option_bind_def split: option.splits call.splits)
  oops

lemma calls_subcontext: 
"calls (sub_context C_in Cs ctxt)
  = (\<lambda>c. if c\<in>Cs then 
            case calls ctxt c of 
              None \<Rightarrow> None 
            | Some (Call op r) \<Rightarrow> C_in op \<bind> (\<lambda>op'. Some (Call op' r))
         else None)"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def Op_def 
      ctxt_restrict_calls_def restrict_map_def
      fmap_map_values_def option_bind_def split: option.splits call.splits intro!: ext)

lemma calls_subcontext_dom: 
"dom (calls (sub_context C_in Cs ctxt))
= {c | c op r. c\<in>Cs \<and> calls ctxt c \<triangleq> Call op r \<and> C_in op \<noteq> None}"
  by (auto simp add: calls_subcontext option_bind_def split: if_splits option.splits call.splits)

lemma calls_subcontext_some:
"calls (sub_context C_in Cs ctxt) c \<triangleq> ci
\<longleftrightarrow> c\<in>Cs \<and> (\<exists>ci'. calls ctxt c \<triangleq> ci' \<and> call_res ci = call_res ci' \<and> C_in (call_operation ci') \<triangleq> call_operation ci)"
  by (auto simp add: calls_subcontext option_bind_def split: if_splits option.splits call.splits)

lemma calls_subcontext_some':
"calls (sub_context C_in Cs ctxt) c \<triangleq> ci
\<longleftrightarrow> c\<in>Cs \<and> (\<exists>op'. calls ctxt c \<triangleq> Call op' (call_res ci) \<and> C_in op' \<triangleq> call_operation ci)"
  by (auto simp add: calls_subcontext option_bind_def split: if_splits option.splits call.splits)

lemma set_rw_spec_rel:
  shows "crdt_spec_rel set_rw_spec set_rw_spec'"
proof (rule show_crdt_spec_rel)


  show "set_rw_spec op (sub_context C_in Cs ctxt) r = set_rw_spec' op (dom (calls (sub_context C_in Cs ctxt))) (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
    if irev: "is_reverse C_in C_out"
      and c1: "C_in outer_op \<triangleq> op"
      and wf: "operationContext_wf ctxt"
    for  C_in C_out ctxt outer_op op r Cs
  proof (cases op)
    case (Add x1)
    then show ?thesis
      by (simp add: set_rw_spec'_def)
  next
    case (Remove x2)
    then show ?thesis
      by (simp add: set_rw_spec'_def)
  next
    case (Contains x3)

    have wf': "operationContext_wf (sub_context C_in Cs ctxt)"
      by (simp add: local.wf sub_context_operationContext_wf)

    from Contains
    show ?thesis
      apply (auto simp add: set_rw_spec'_def set_rw_spec_Contains_iff[OF wf'] intro!: arg_cong[where f="from_bool"])
      apply (auto simp add: extract_op_into_sub_context[OF irev]
          happens_before_into_sub_context[OF irev])
             apply (auto simp add: happens_before_sub_context Op_subcontext)
             apply (auto simp add: calls_subcontext_dom calls_subcontext_some)
      apply (auto simp add: Op_def extract_op_def is_reverse_2[OF irev])
      subgoal
        by (metis (no_types, lifting) call.collapse)
      subgoal
        using is_reverse_2[OF irev]
        by blast    
      subgoal for x a_info c c_info x_info
        apply (cases a_info; cases x_info)
        by fastforce
      subgoal for a y ra ci' z
        apply (cases y; cases ci')
        apply auto
        by (metis (no_types, lifting) call.collapse)
      subgoal for a z
        by (cases z) auto
      subgoal for a ra y ci' z
        apply (cases y; cases ci'; cases z)
        apply auto
        apply (thin_tac "_ = from_bool _")
        using is_reverse_2[OF irev]
        by (metis (mono_tags, lifting) call.sel(1))
      done
  qed
qed



lemma set_rw_spec_wf[simp]:
"ccrdtSpec_wf (set_rw_spec' op)"
  by (auto simp add: ccrdtSpec_wf_def set_rw_spec'_def map_same_on_def rel_same_on_def split: setOp.splits)




subsection "Maps"


definition deleted_calls_dw' :: "callId set \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set" where
"deleted_calls_dw' vis op hb C k \<equiv> {c\<in>vis. \<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb}"

lemma in_deleted_calls_dw':
"c\<in>deleted_calls_dw' vis op hb C k \<longleftrightarrow> c\<in>vis \<and> (\<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb)"
  by (auto simp add: deleted_calls_dw'_def)

definition "C_out_calls C_out op vis \<equiv> {c\<in>vis. \<exists>x. op c = C_out x}"

definition 
"restrict_calls vis op C k \<equiv>
{c\<in>vis. \<exists>u. op c = C (NestedOp k u) }"

lemma restrict_calls_def2: "restrict_calls vis op C k = C_out_calls (C \<circ> (\<lambda>u. NestedOp k u)) op vis"
  by (auto simp add: restrict_calls_def C_out_calls_def)


definition map_spec' :: "
      (callId set  \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set) 
    \<Rightarrow> ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::{default,from_bool})) ccrdtSpec" where
"map_spec' deleted_calls nestedSpec oper vis op hb C res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c\<in>vis. \<exists>upd_op. op c = C (NestedOp k upd_op) \<and> is_update upd_op \<and>  c \<notin> deleted_calls vis op hb C k)
  | NestedOp k nested_op \<Rightarrow>
     nestedSpec nested_op (restrict_calls vis op C k - deleted_calls vis op hb C k) op hb (\<lambda>x. C (NestedOp k x))  res
"


definition map_dw_spec' :: "
       ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::{default,from_bool})) ccrdtSpec" where
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
      restrict_relation_def extract_op_def'  map_map_def map_chain_def
      split: option.splits call.splits if_splits,
   (smt IntI assms(1) call.collapse call.sel(1) domExists_simp domIff is_reverse_def o_apply option.case_eq_if option.sel),
   (metis assms(1) is_reverse_2 option.distinct(1) option.inject),
   (metis assms(1) is_reverse_2 option.distinct(1) option.sel))






lemma map_spec_rel:
  fixes nestedSpec :: "('opn::crdt_op, 'res::{default,from_bool}) crdtSpec"
    and nestedSpec' :: "('op, 'opn, 'res) ccrdtSpec"
    and deletedCalls :: "(('k, 'opn) mapOp, 'res) operationContext \<Rightarrow> 'k \<Rightarrow> callId set"
    and deletedCalls' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set"
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
and deletedCalls_rel: 
    "\<And>ctxt C_in C_out Cs k. \<lbrakk>
      is_reverse C_in C_out;
      Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)
     \<rbrakk> \<Longrightarrow>
          deleted_calls (sub_context C_in Cs ctxt) k
        = deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "crdt_spec_rel (map_spec deleted_calls  nestedSpec) (map_spec' deleted_calls'  nestedSpec') "
  unfolding crdt_spec_rel_def
proof (intro allI impI)

  show "map_spec deleted_calls nestedSpec op (sub_context C_in Cs ctxt) r 
      = map_spec' deleted_calls' nestedSpec' op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r" 
    (is "?l = ?r")
    if is_rev: "is_reverse C_in C_out"
   and in_out: "C_in outer_op \<triangleq> op"
   and Cs_sub: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
   and wf: "operationContext_wf ctxt"
   for  C_in C_out ctxt outer_op op r Cs
  proof -

    from Cs_sub
    have Cs_sub': "\<forall>c\<in>Cs. \<exists>op op' r. calls ctxt c \<triangleq> Call op r \<and> C_in op \<triangleq> op'"
      by (smt call.collapse in_dom map_chain_eq_some map_map_apply_eq_some)



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

        have sc2: "(sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs) ctxt)
            = (sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k 
                    \<inter> {c\<in>Cs. \<exists>x y z. calls ctxt c \<triangleq> Call x y \<and> C_in x \<triangleq> z \<and> nested_op_on_key k z \<noteq>None  }  ) ctxt)"
          apply (auto simp add: operationContext_ext calls_sub_context happens_before_sub_context restrict_map_def option_bind_def 
              intro!: ext split: option.splits if_splits call.splits)
          by (metis call.collapse)+




        show "nestedSpec nestedOp
           (sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs) ctxt) r =
          nestedSpec' nestedOp
           (restrict_calls Cs (extract_op (calls ctxt)) C_out k -
            deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
           (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r"
        proof (subst sc2, subst use_crdt_spec_rel[OF nested_rel])        

          show is_rev_combined: "is_reverse (\<lambda>x. C_in x \<bind> nested_op_on_key k) (\<lambda>x. C_out (NestedOp k x))"
            by (auto simp add: is_reverse_def option_bind_def nested_op_on_key_def 
                is_reverse_1[OF is_rev] is_reverse_2[OF is_rev] split: option.splits mapOp.splits)

          show "(C_in (C_out (NestedOp k nestedOp)) \<bind> nested_op_on_key k) \<triangleq> nestedOp"
            using is_rev_combined is_reverse_def by fastforce

          have h1: "deleted_calls (sub_context C_in Cs ctxt) k
              = deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            using Cs_sub
            by (rule deletedCalls_rel[OF is_rev])




          have h4: "
             (dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter> (- DC  \<inter> Cs) )
             =
             ({c \<in> dom (map_map (calls ctxt) call_operation \<ggreater> C_in).
               c \<in> Cs \<and> (\<exists>u. extract_op (calls ctxt) c = C_out (NestedOp k u))} - DC)"
            if "DC = deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            for DC
            apply (auto simp add: map_map_def map_chain_def option_bind_def split: option.splits)
             apply (auto simp add: nested_op_on_key_def extract_op_def' split: option.splits mapOp.splits if_splits call.splits)
               apply (auto simp add: is_reverse_2[OF is_rev])
            using is_rev is_reverse_1 by fastforce

          show "- deleted_calls (sub_context C_in Cs ctxt) k \<inter>
              {c \<in> Cs. \<exists>x y z. calls ctxt c \<triangleq> Call x y \<and> C_in x \<triangleq> z \<and> nested_op_on_key k z \<noteq> None}
              \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k))"
            using Cs_sub'
            by (auto simp add: map_chain_def option_bind_def map_map_def dom_def dest!: subset_h1 split: option.splits) 


          have h5: "(- deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k \<inter>
               {c \<in> Cs. \<exists>x. (\<exists>y. calls ctxt c \<triangleq> Call x y) \<and> (\<exists>z. C_in x \<triangleq> z \<and> (\<exists>y. nested_op_on_key k z \<triangleq> y))})
            = (restrict_calls Cs (extract_op (calls ctxt)) C_out k - deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)"
            apply (auto simp add: restrict_calls_def )
            using Cs_sub' apply (auto simp add: extract_op_def'  is_reverse_2[OF is_rev]  split: option.splits call.splits)
            using is_reverse_1[OF is_rev]  by (auto simp add: nested_op_on_key_def  split: mapOp.splits if_splits)


          show "nestedSpec' nestedOp
             (- deleted_calls (sub_context C_in Cs ctxt) k \<inter>
              {c \<in> Cs. \<exists>x y z. calls ctxt c \<triangleq> Call x y \<and> C_in x \<triangleq> z \<and> nested_op_on_key k z \<noteq> None})
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r =
            nestedSpec' nestedOp
             (restrict_calls Cs (extract_op (calls ctxt)) C_out k -
              deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r"
            by (simp add: h1 h5)
          show "operationContext_wf ctxt"
            by (simp add: local.wf)

        qed
      qed

    next
      case (KeyExists k)
      show ?thesis 
      proof (simp add: KeyExists map_spec_def map_spec'_def, 
              subst deletedCalls_rel[OF is_rev Cs_sub],
              rule arg_cong[where f="\<lambda>x. r = from_bool x"])

        show "(\<exists>c op.
                  (\<exists>r. calls (sub_context C_in Cs ctxt) c \<triangleq> Call (NestedOp k op) r) \<and>
                  is_update op \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k) 
             = (\<exists>c\<in>Cs.
                  \<exists>upd_op.
                     extract_op (calls ctxt) c = C_out (NestedOp k upd_op) \<and>
                     is_update upd_op \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)"
        proof (auto simp add: Bex_def calls_sub_context option_bind_def dom_map_chain restrict_map_def split: option.splits, fuzzy_goal_cases A B)
          case (A c y)
          show ?case
            apply (auto intro!: exI[where x=c])
            using A(1) A(2) apply auto[1]
            using A  apply (auto simp add: extract_op_def' split: option.splits call.splits )
          proof -
            fix x1 :: 'op and x2 :: 'res
            assume a1: "y = Call x1 x2"
            have "\<forall>m z. C_out m = z \<or> C_in z \<noteq> Some m"
              by (meson is_rev is_reverse_def)
            then show "\<exists>z. x1 = C_out (NestedOp k z) \<and> is_update z \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
              using a1 by (metis A(1) call.sel(1) not_None_eq)
          qed

        next
          case (B c upd_op)
          show ?case
            apply (rule exI[where x=c], auto)
            using B apply auto
            using B  Cs_sub' apply (auto simp add: extract_op_def' split: option.splits call.splits )
            using is_rev is_reverse_2 by fastforce

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
  shows "crdt_spec_rel (map_dw_spec nestedSpec) (map_dw_spec' nestedSpec') "
  unfolding map_dw_spec'_def map_dw_spec_def
proof (rule map_spec_rel[OF nested_rel])
  show "deleted_calls_dw (sub_context C_in Cs ctxt) k = deleted_calls_dw' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
    if c0: "is_reverse C_in C_out"
      and c1: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
    for  ctxt C_in C_out Cs k
    by (metis c0 c1 deleted_calls_dw_rel inf.absorb_iff2)
qed

lemma restrict_calls_wf:
  assumes " map_same_on Cs op op'"
  shows "restrict_calls Cs op C_out k
  = restrict_calls Cs op' C_out k"
  using assms by (auto simp add: restrict_calls_def map_same_on_def)


lemma map_spec_wf[simp]:
  assumes nested: "\<And>oper. ccrdtSpec_wf (nested oper)"
    and dwf: "\<forall>oper Cs op op' hb hb' C_out k. 
      map_same_on Cs op op'
      \<longrightarrow> rel_same_on Cs hb hb'
      \<longrightarrow> deleted_calls Cs op hb C_out k = deleted_calls Cs op' hb' C_out k"
    shows
"ccrdtSpec_wf (map_spec' deleted_calls nested oper)"
proof (simp add: ccrdtSpec_wf_def; intro impI allI)

  show "map_spec' deleted_calls nested oper Cs op hb C_out r = map_spec' deleted_calls nested oper Cs op' hb' C_out r"
    if c0: "map_same_on Cs op op'"
      and c1: "rel_same_on Cs hb hb'"
    for  oper Cs op op' hb hb' C_out r
  proof -

    have h1: "map_same_on (restrict_calls Cs op' C_out k - deleted_calls Cs op' hb' C_out k) op op'" for k
      using c0 by (auto simp add: map_same_on_def restrict_calls_def)

    have h2: "rel_same_on (restrict_calls Cs op' C_out k - deleted_calls Cs op' hb' C_out k) hb hb'" for k
      using c1 by (auto simp add: rel_same_on_def restrict_calls_def)

    show "map_spec' deleted_calls nested oper Cs op hb C_out r
    = map_spec' deleted_calls nested oper Cs op' hb' C_out r"
    apply (auto simp add: map_spec'_def  dwf[rule_format, OF c0 c1] restrict_calls_wf[OF c0] use_ccrdtSpec_wf[OF nested h1 h2] split: mapOp.splits)
      using c0 by (auto simp add:   map_same_on_def)
  qed
qed

lemma map_dw_spec_wf[simp]:
  assumes nested_rel: "\<And>oper. ccrdtSpec_wf (nestedSpec oper)"
  shows "ccrdtSpec_wf (map_dw_spec' nestedSpec oper) "
  unfolding map_dw_spec'_def using nested_rel
proof (rule map_spec_wf; intro allI impI)

  show "deleted_calls_dw' Cs op hb C_out k = deleted_calls_dw' Cs op' hb' C_out k"
    if c0: "\<And>oper. ccrdtSpec_wf (nestedSpec oper)"
      and c1: "map_same_on Cs op op'"
      and c2: "rel_same_on Cs hb hb'"
    for  oper Cs op op' hb hb' C_out k
    using c1 c2
    by (auto simp add: deleted_calls_dw'_def map_same_on_def rel_same_on_def)
qed


subsection "Structs"



definition struct_field' :: "('opn \<Rightarrow> 'a) \<Rightarrow> ('op, 'opn, 'res) cOperationResultSpec \<Rightarrow> ('op, 'a, 'res) cOperationResultSpec "  where
"struct_field' C_out spec  \<equiv> 
  \<lambda> vis op hb x_C_out res.
    spec (C_out_calls (x_C_out \<circ> C_out) op vis) op hb (x_C_out \<circ> C_out)  res"


lemma struct_field_eq:
  assumes rel: "crdt_spec_rel nspec nspec'"
    and is_rev: "is_reverse C_in C_out"
    and is_rev': "is_reverse C_in' C_out'"
    and c_calls_subset: "c_calls \<subseteq> dom (calls ctxt)"
    and wf: "operationContext_wf ctxt"
shows "struct_field (nspec n_op) C_in (sub_context C_in' c_calls ctxt) res 
      =  struct_field' C_out (nspec' n_op) c_calls (extract_op (calls ctxt)) (happensBefore ctxt) C_out' res"
proof (simp add: struct_field_def struct_field'_def C_out_calls_def)
  show " nspec n_op (restrict_ctxt_op C_in (sub_context C_in' c_calls ctxt)) res =
    nspec' n_op {c \<in> c_calls. \<exists>x. extract_op (calls ctxt) c = C_out' (C_out x)} (extract_op (calls ctxt))
     (happensBefore ctxt) (C_out' \<circ> C_out) res"
  proof (fuzzy_rule use_crdt_spec_rel[OF rel])


    show "is_reverse (C_in' \<ggreater> C_in) (C_out' \<circ> C_out)"
      by (simp add: is_rev is_rev' is_reverse_combine)


    show "(C_in' \<ggreater> C_in) (C_out' (C_out n_op)) \<triangleq> n_op"
      by (simp add: is_rev is_rev' is_reverse_2 map_chain_def)

    show "{c \<in> c_calls. \<exists>x. extract_op (calls ctxt) c = C_out' (C_out x)}
      \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in' \<ggreater> C_in)"
      apply (auto simp add: 
          operationContext_ext calls_sub_context happens_before_sub_context
          option_bind_def restrict_ctxt_op_def restrict_map_def 
          map_chain_def restrict_ctxt_def fmap_map_values_def
          restrict_relation_def 
          split: if_splits option.splits call.splits)
      using c_calls_subset apply blast
       apply (simp add: call_operation_def extract_op_def is_rev' is_reverse_2)
      by (metis call_operation_def extract_op_def is_rev is_rev' is_reverse_2 option.sel option.simps(5))

    show "sub_context (C_in' \<ggreater> C_in) {c \<in> c_calls. \<exists>x. extract_op (calls ctxt) c = C_out' (C_out x)} ctxt =
    restrict_ctxt_op C_in (sub_context C_in' c_calls ctxt)"
      apply (auto simp add: map_map_def map_chain_def option_bind_def  split: option.splits)
      using c_calls_subset apply (auto simp add: call_operation_def extract_op_def is_rev' is_reverse_2 operationContext_ext calls_sub_context 
          restrict_map_def option_bind_def
          restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def option_bind_def
          happens_before_sub_context restrict_relation_def
          is_reverse_1[OF is_rev] is_reverse_1[OF is_rev']
          is_reverse_2[OF is_rev] is_reverse_2[OF is_rev']
          intro!: ext
          split: option.splits  call.splits  if_splits)
        apply (metis is_rev is_rev' is_reverse_1)
       apply (metis is_rev is_rev' is_reverse_1)
      by (metis is_rev is_rev' is_reverse_1)

    show "operationContext_wf ctxt"
      using wf .
  qed 
qed

lemma struct_field_wf[simp]:
  assumes nested_rel: "ccrdtSpec_wf nestedSpec"
  shows "ccrdtSpec_wf (struct_field' C_out nestedSpec) "
proof (clarsimp simp add: ccrdtSpec_wf_def struct_field'_def C_out_calls_def)

  show "nestedSpec {c \<in> Cs. \<exists>x. op c = C_outa (C_out x)} op hb (C_outa \<circ> C_out) r = nestedSpec {c \<in> Cs. \<exists>x. op' c = C_outa (C_out x)} op' hb' (C_outa \<circ> C_out) r"
    if c0: "map_same_on Cs op op'"
      and c1: "rel_same_on Cs hb hb'"
    for  Cs op op' hb hb' C_outa r
  proof (subst use_ccrdtSpec_wf[OF nested_rel, where op'=op' and hb'=hb'])
    have "{c \<in> Cs. \<exists>x. op c = C_outa (C_out x)} =
          {c \<in> Cs. \<exists>x. op' c = C_outa (C_out x)}"
      using c0 by (auto simp add: map_same_on_def)

    thus "nestedSpec {c \<in> Cs. \<exists>x. op c = C_outa (C_out x)} op' hb' (C_outa \<circ> C_out) r =
          nestedSpec {c \<in> Cs. \<exists>x. op' c = C_outa (C_out x)} op' hb' (C_outa \<circ> C_out) r"
      by simp

    show "map_same_on {c \<in> Cs. \<exists>x. op c = C_outa (C_out x)} op op'"
      using c0 by (auto simp add: map_same_on_def)

    show "rel_same_on {c \<in> Cs. \<exists>x. op c = C_outa (C_out x)} hb hb'"
      using c1 by (auto simp add: rel_same_on_def)
  qed
qed

lemma sub_context_id: 
  assumes calls_sub: "dom (calls ctxt) \<subseteq> c_calls"
    and hb_wf: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  shows "(sub_context Some c_calls ctxt) = ctxt"
  apply (auto simp add: operationContext_ext calls_sub_context happens_before_sub_context restrict_map_def intro!: ext)
  using calls_sub domIff apply force
  apply (meson FieldI1 hb_wf in_dom)
  apply (meson FieldI1 calls_sub hb_wf subset_h1)
  apply (meson FieldI2 hb_wf in_dom)
  by (meson FieldI2 calls_sub hb_wf subset_h1)

lemma sub_context_id2: 
  assumes  hb_wf: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  shows "(sub_context Some (dom (calls ctxt)) ctxt) = ctxt"
  by (simp add: hb_wf sub_context_id)

lemma sub_context_id3: 
  assumes  wf: "operationContext_wf ctxt"
  shows "(sub_context Some (dom (calls ctxt)) ctxt) = ctxt"
proof (rule sub_context_id2)
  show "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
    by (simp add: local.wf operationContext_wf_hb_field)
qed

(*
text "We can also do a generic conversion between the two specification formats: "

definition "some_inverse f \<equiv> SOME g. is_reverse g f"

lemma "inj f \<Longrightarrow> \<exists>g. is_reverse g f"
  apply (auto simp add: is_reverse_def)



lemma "is_reverse (some_inverse f) f"
  unfolding some_inverse_def
proof -


  show "is_reverse (SOME g. is_reverse g f) f"
  proof (rule someI[where P="\<lambda>x. is_reverse x f"])

definition "transformSpec spec op Cs ops hb C_out r \<equiv> 
  spec op (sub_context (some_inverse C_out) Cs \<lparr>calls = \<lambda>c. if c\<in>Cs then Some (Call (ops c) ???) else None, happensBefore = hb\<rparr>) r"

lemma 
"crdt_spec_rel crdtSpec (transformSpec crdtSpec)"
proof (rule show_crdt_spec_rel')

  show "crdtSpec op (sub_context C_in Cs ctxt) r = transformSpec crdtSpec op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
    if c0: "is_reverse C_in C_out"
      and c1: "operationContext_wf ctxt"
      and c2: "C_in outer_op \<triangleq> op"
      and c3: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
    for  C_in C_out ctxt outer_op op r Cs

*)

end