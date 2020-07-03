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
    map_chain_eq_some dom_def cOp_def
    split: option.splits registerOp.splits call.splits, 
    fuzzy_goal_cases A B C D E F G H)
  case (A a b y)
  then show ?case
    by (simp add: calls_sub_context)
next
  case (B a b y x1a c' v' r' x2)
  then show ?case 
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def happens_before_sub_context split: if_splits option.splits)
     (metis (mono_tags, lifting) call_operation_def extract_op_def' is_rev is_reverse_1 option.simps(5))
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
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2 split: if_splits option.splits call.splits)
      (use is_rev is_reverse_1 in fastforce)

next
  case (H a b c' y v' x2a x1a)
  then show ?case 
    by (auto simp add: calls_sub_context option_bind_def restrict_map_def  call_operation_def extract_op_def is_rev is_reverse_2  split: if_splits option.splits call.splits)
     (metis (mono_tags, lifting) H(5) bind.bind_lunit call.sel(1) calls_sub_context domI happens_before_sub_context option.simps(5) restrict_map_def)
qed


lemma  latest_assignments_rel2: 
  assumes is_rev: "is_reverse C_in C_out"
    and Cs_subset: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
  shows "(latest_assignments' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out)
      = {(x,y) | x y. latestAssignments (sub_context C_in Cs ctxt) x \<triangleq> y}"
  by (metis (mono_tags, lifting) Collect_cong Cs_subset inf.absorb_iff2 is_rev latest_assignments_rel)


lemma  latest_assignments_rel3: 
  assumes is_rev: "is_reverse C_in C_out"
    and Cs_subset: "Cs \<subseteq> dom (calls ctxt)"
  shows "(latest_assignments' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out)
      = {(x,y) | x y. latestAssignments (sub_context C_in Cs ctxt) x \<triangleq> y}"
  using Cs_subset 
  by (auto simp add: latest_assignments'_def latestAssignments_def latestAssignments_h_def
      cOp_def
      sub_context_def restrict_ctxt_op_def 
      restrict_ctxt_def fmap_map_values_def
      ctxt_restrict_calls_def option_bind_def
      in_dom
      extract_op_def
      is_reverse_2[OF is_rev] is_reverse_1[OF is_rev]
      restrict_relation_def restrict_map_def
      split: option.splits registerOp.splits if_splits)
    (metis is_rev is_reverse_1 option.sel, use  is_rev is_reverse_2 in fastforce)



lemma lww_register_spec_rel[intro!]:
"crdt_spec_rel (lww_register_spec initial) (lww_register_spec' initial) "
  unfolding crdt_spec_rel_def
  by (auto simp add: lww_register_spec_def lww_register_spec'_def 
          latest_assignments_rel3 firstValue'_to_firstValue split: registerOp.splits)


lemma latestValues_rel:
  assumes is_rev: "is_reverse C_in C_out"
    and subset: "Cs \<subseteq> dom (calls ctxt)"
shows "latestValues (sub_context C_in Cs ctxt)
     = latest_values' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out"
  by (auto simp add: latestValues_def latest_values'_def latest_assignments_rel3[OF is_rev subset] ran_def in_img_simp)

lemma register_spec_rel[intro!]:
"crdt_spec_rel (register_spec initial) (register_spec' initial) "
  unfolding crdt_spec_rel_def
  by (auto simp add: register_spec_def register_spec'_def is_from_def
          latestValues_rel firstValue'_to_firstValue split: registerOp.splits)



lemma latest_assignments'_wf:
  assumes a1: "map_same_on Cs' op op'"
and a2: "rel_same_on Cs' hb hb'"
and a3: "Cs' \<subseteq> Cs"
and a4: "\<forall>c\<in>Cs. (\<exists>y. C_out y = op c) \<longrightarrow> c\<in>Cs'"
shows " latest_assignments' Cs op hb C_out =  latest_assignments' Cs' op' hb' C_out"
  using a1 a2 a3 by (auto simp add: latest_assignments'_def  map_same_on_def rel_same_on_def)
    (metis a4 in_mono)+




lemma latest_values'_wf:
  assumes "map_same_on Cs' op op'"
and "rel_same_on Cs' hb hb'"
and "Cs' \<subseteq> Cs"
and "\<forall>c\<in>Cs. (\<exists>y. C_out y = op c) \<longrightarrow> c\<in>Cs'"
shows " latest_values' Cs op hb C_out =  latest_values' Cs' op' hb' C_out"
  by (auto simp add: latest_values'_def latest_assignments'_wf[OF assms])


lemma register_spec_wf[simp]:
"ccrdtSpec_wf (register_spec' i)"
  by (auto simp add: ccrdtSpec_wf_def register_spec'_def latest_values'_wf split: registerOp.splits)




lemma lww_register_spec_wf[simp]:
"ccrdtSpec_wf (lww_register_spec' i)"
  by (auto simp add: ccrdtSpec_wf_def lww_register_spec'_def latest_assignments'_wf split: registerOp.splits)






subsection "Sets"



text_raw \<open>\DefineSnippet{set_rw_spec2}{\<close>
definition set_rw_spec' :: "('op, 'v setOp, ('r::{default,from_bool})) ccrdtSpec" where
"set_rw_spec' oper vis op hb C  res \<equiv> 
  case oper of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool 
        (\<exists>a\<in>vis. op a = C (Add v)
           \<and> (\<forall>r\<in>vis. op r = C (Remove v)
                 \<longrightarrow> (\<exists>a'\<in>vis. op a' = C (Add v) \<and> (r,a')\<in>hb)))"
text_raw \<open>}%EndSnippet\<close>



lemma sub_context_operationContext_wf:
  assumes wf: "operationContext_wf ctxt"
  shows "operationContext_wf (sub_context C_in Cs ctxt)"
  unfolding operationContext_wf_def
proof (intro conjI)
  have a0: "trans (happensBefore ctxt)"
    by (simp add: local.wf operationContext_wf_trans)

  have a1: "wf ((happensBefore ctxt)\<inverse>)"
    by (simp add: local.wf operationContext_wf_wf)

  have a2: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
    by (simp add: local.wf operationContext_wf_hb_field)



  show "trans (happensBefore (sub_context C_in Cs ctxt))"
    by (metis (mono_tags, lifting) a0 happens_before_sub_context trans_def)

  show "irrefl (happensBefore (sub_context C_in Cs ctxt))"
    by (meson a1 acyclic_converse happens_before_sub_context irrefl_def local.wf operationContext_wf_finite_hb wf_acyclic wf_asym wf_iff_acyclic_if_finite)


  show "Field (happensBefore (sub_context C_in Cs ctxt)) \<subseteq> dom (calls (sub_context C_in Cs ctxt))"
    using a2
    by (auto simp add: sub_context_def restrict_ctxt_op_def ctxt_restrict_calls_def restrict_ctxt_def
          restrict_relation_def fmap_map_values_def restrict_map_def Field_def)

  show "finite (dom (calls (sub_context C_in Cs ctxt)))"
  proof (rule finite_subset)
    show "dom (calls (sub_context C_in Cs ctxt)) \<subseteq> dom (calls ctxt)"
      by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def ctxt_restrict_calls_def fmap_map_values_def option_bind_def restrict_map_def split: option.splits if_splits)
    show "finite (dom (calls ctxt))"
      using local.wf operationContext_wf_def by blast
  qed
qed


lemma Op_subcontext:
"Op (sub_context C_in Cs ctxt) c \<triangleq> op
\<longleftrightarrow> (\<exists>op'. c\<in>Cs \<and> Op ctxt c \<triangleq> op' \<and> C_in op' \<triangleq> op)"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def cOp_def 
      ctxt_restrict_calls_def restrict_map_def
      fmap_map_values_def option_bind_def split: option.splits call.splits)


lemma calls_subcontext: 
"calls (sub_context C_in Cs ctxt)
  = (\<lambda>c. if c\<in>Cs then 
            case calls ctxt c of 
              None \<Rightarrow> None 
            | Some (Call op r) \<Rightarrow> C_in op \<bind> (\<lambda>op'. Some (Call op' r))
         else None)"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def cOp_def 
      ctxt_restrict_calls_def restrict_map_def
      fmap_map_values_def option_bind_def split: option.splits call.splits intro!: ext)

lemma calls_subcontext_dom: 
"dom (calls (sub_context C_in Cs ctxt))
= {c | c op. c\<in>Cs \<and> Op ctxt c \<triangleq> op \<and> C_in op \<noteq> None}"
  by (auto simp add: calls_subcontext option_bind_def cOp_def split: if_splits option.splits call.splits)

lemma calls_subcontext_dom_exists: 
"(\<exists>c\<in>dom (calls (sub_context C_in Cs ctxt)). P c)
= (\<exists>c\<in>Cs. \<exists>op. Op ctxt c \<triangleq> op \<and> C_in op \<noteq> None \<and> P c)"
  by (auto simp add: calls_subcontext_dom)

lemma calls_subcontext_dom_forall: 
"(\<forall>c\<in>dom (calls (sub_context C_in Cs ctxt)). P c)
= (\<forall>c\<in>Cs. \<forall>op. Op ctxt c \<triangleq> op \<longrightarrow> C_in op \<noteq> None \<longrightarrow> P c)"
  by (auto simp add: calls_subcontext_dom)



lemma calls_subcontext_some:
"calls (sub_context C_in Cs ctxt) c \<triangleq> ci
\<longleftrightarrow> c\<in>Cs \<and> (\<exists>ci'. calls ctxt c \<triangleq> ci' \<and> call_res ci = call_res ci' \<and> C_in (call_operation ci') \<triangleq> call_operation ci)"
  by (auto simp add: calls_subcontext option_bind_def split: if_splits option.splits call.splits)

lemma calls_subcontext_some':
"calls (sub_context C_in Cs ctxt) c \<triangleq> ci
\<longleftrightarrow> c\<in>Cs \<and> (\<exists>op'. calls ctxt c \<triangleq> Call op' (call_res ci) \<and> C_in op' \<triangleq> call_operation ci)"
  by (auto simp add: calls_subcontext option_bind_def split: if_splits option.splits call.splits)

lemma forall_call_expand:
"(\<forall>c. P c) \<longleftrightarrow> (\<forall>op r. P (Call op r))"
  by (metis call.exhaust)


lemma not_some_the[simp]: "y \<noteq> Some (the y) \<longleftrightarrow> y = None"
  by (cases y) auto


lemma set_rw_spec_rel[intro!]:
  shows "crdt_spec_rel set_rw_spec set_rw_spec'"
proof (rule show_crdt_spec_rel)


  show "set_rw_spec op (sub_context C_in Cs ctxt) r = set_rw_spec' op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
    if irev: "is_reverse C_in C_out"
      and c1: "C_in outer_op \<triangleq> op"
      and wf: "operationContext_wf ctxt"
      and CS_subset: "Cs \<subseteq> dom (calls ctxt)"
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


    show ?thesis
      unfolding Contains
        set_rw_spec_Contains_iff[OF wf']
        set_rw_spec'_def
      apply (simp add: calls_subcontext_dom_exists calls_subcontext_dom_forall 
        extract_op_into_sub_context'[OF irev]
        happens_before_into_sub_context[OF irev]
        Op_subcontext
        , rule from_bool_eq_simp')
      apply (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def ctxt_restrict_calls_def
restrict_relation_def fmap_map_values_def restrict_map_def
option_bind_def domExists_simp cOp_def extract_op_def
is_reverse_1[OF irev] is_reverse_2[OF irev] 
 split: option.splits)
         apply force
      subgoal for a z r
        by (smt CS_subset domIff irev is_reverse_def option.collapse subset_iff)
      subgoal
        using CS_subset irev is_reverse_2 by fastforce
      subgoal
        by (smt CS_subset domIff irev is_reverse_def option.collapse option.sel subsetD)
      done

  qed
qed



lemma set_rw_spec_wf[simp]:
  "ccrdtSpec_wf set_rw_spec'"
  by (auto simp add: ccrdtSpec_wf_def set_rw_spec'_def map_same_on_def rel_same_on_def subset_eq
      split: setOp.splits
      intro!: arg_cong[where f=from_bool])
    metis+




text_raw \<open>\DefineSnippet{set_aw_spec2}{\<close>
definition set_aw_spec' :: "('op, 'v setOp, ('r::{default,from_bool})) ccrdtSpec" where
"set_aw_spec' oper vis op hb C  res \<equiv> 
  case oper of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool 
        (\<exists>a\<in>vis. op a = C (Add v)
           \<and> \<not>(\<exists>r\<in>vis. op r = C (Remove v) \<and> (a,r)\<in>hb))"
text_raw \<open>}%EndSnippet\<close>

schematic_goal set_aw_spec'_contains:
"set_aw_spec' (Contains x) vis op hb id res \<longleftrightarrow> ?x"
  using [[simp_trace,simp_trace_depth_limit=10000]]
  by (subst set_aw_spec'_def, simp del: bex_simps(8))

text \<open>
\DefineSnippet{set_aw_spec2_contains}{
  @{thm [display] set_aw_spec'_contains}
}%EndSnippet\<close>

lemma set_aw_spec_wf[simp]:
  "ccrdtSpec_wf set_aw_spec'"
  by (auto simp add: ccrdtSpec_wf_def set_aw_spec'_def map_same_on_def rel_same_on_def subset_eq
      split: setOp.splits
      intro!: arg_cong[where f=from_bool])
    metis+



lemma set_aw_spec_rel[intro!]:
  shows "crdt_spec_rel set_aw_spec set_aw_spec'"
proof (rule show_crdt_spec_rel, fuzzy_goal_cases A)
  case (A C_in C_out ctxt outer_op op r Cs)
  show ?case
  proof (cases op)
    case (Add x1)
    then show ?thesis
      by (auto simp add: set_aw_spec'_def)
  next
    case (Remove x2)
    then show ?thesis
      by (auto simp add: set_aw_spec'_def)
  next
    case (Contains x3)
    thus ?thesis
    proof auto
      assume a: "set_aw_spec (Contains x3) (sub_context C_in Cs ctxt) r"

      have owf: \<open>operationContext_wf (sub_context C_in Cs ctxt)\<close>
        by (simp add: A.operationContext_wf sub_context_operationContext_wf)


      show "set_aw_spec' (Contains x3) Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
        apply (auto simp add: set_aw_spec_Contains[OF a owf] set_aw_spec'_def  intro!: arg_cong[where f=from_bool])
        subgoal for a
          apply (rule bexI[where x=a], auto)
            apply (auto simp add:  Op_subcontext happens_before_sub_context calls_subcontext_dom)
           apply (auto simp add: cOp_def extract_op_def is_reverse_1[OF A.is_reverse] is_reverse_2[OF A.is_reverse])
          using A.less_eq  is_reverse_2[OF A.is_reverse] by fastforce
        subgoal for a
          apply (rule exI[where x=a], auto)
           apply (auto simp add:  Op_subcontext happens_before_sub_context calls_subcontext_dom)
           apply (auto simp add: cOp_def extract_op_def is_reverse_1[OF A.is_reverse] is_reverse_2[OF A.is_reverse])
          using A.less_eq  is_reverse_2[OF A.is_reverse] by fastforce
        done

    next 

      assume a: "set_aw_spec' (Contains x3) Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"

      hence "r =
        from_bool
         (\<exists>a\<in>Cs.
             extract_op (calls ctxt) a = C_out (Add x3) \<and>
             (\<forall>r\<in>Cs. extract_op (calls ctxt) r = C_out (Remove x3) \<longrightarrow> (a, r) \<notin> happensBefore ctxt))"
        unfolding set_aw_spec'_def
        by simp

      from is_reverse_2[OF A.is_reverse]
      have [simp]: "C_in (C_out x) \<triangleq> x" for x .

      from is_reverse_1[OF A.is_reverse]
      have [simp]: "C_in x \<triangleq> y \<Longrightarrow> C_out y = x" for x y .

      show "set_aw_spec (Contains x3) (sub_context C_in Cs ctxt) r"
      proof (rule set_aw_spec_Contains2)
        show "operationContext_wf (sub_context C_in Cs ctxt)"
          by (simp add: A.operationContext_wf sub_context_operationContext_wf)
        show "r =
            from_bool
             (\<exists>a. Op (sub_context C_in Cs ctxt) a \<triangleq> Add x3 \<and>
                  (\<nexists>r. Op (sub_context C_in Cs ctxt) r \<triangleq> Remove x3 \<and>
                       (a, r) \<in> happensBefore (sub_context C_in Cs ctxt)))"
          using a
          apply (auto simp add: set_aw_spec'_def intro!: arg_cong[where f=from_bool])
           apply (auto simp add:  Op_subcontext happens_before_sub_context calls_subcontext_dom)
           apply (auto simp add: cOp_def extract_op_def)
          subgoal for a
            apply (rule exI[where x=a])
            apply auto
            by (meson A.is_reverse A.less_eq domIff is_reverse_2 not_some_the subsetD)
          subgoal for a z
            apply (rule bexI[where x=a])
            using A.less_eq apply (auto simp add: subset_iff)
            by (metis (mono_tags, lifting) \<open>\<And>x. C_in (C_out x) \<triangleq> x\<close> domIff not_some_the option.discI)
          done
      qed
    qed
  qed
qed



subsection "Maps"


text_raw \<open>\DefineSnippet{map_sdw_spec'}{\<close>
definition 
"restrict_calls vis op C k \<equiv>
{c\<in>vis. \<exists>u. op c = C (NestedOp k u) }"

definition map_spec' :: "
      (callId set  \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set) 
    \<Rightarrow> ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::{default,from_bool})) ccrdtSpec" where
"map_spec' deleted_calls nestedSpec oper vis op hb C res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c\<in>vis. \<exists>upd_op. op c = C (NestedOp k upd_op) \<and> is_update upd_op \<and>  c \<notin> deleted_calls vis op hb C k)
  | NestedOp k nested_op \<Rightarrow>
     nestedSpec nested_op (vis - deleted_calls vis op hb C k) op hb (\<lambda>x. C (NestedOp k x))  res
"

definition deleted_calls_sdw' :: "callId set \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set" where
"deleted_calls_sdw' vis op hb C k \<equiv> {c\<in>vis. \<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb}"

definition
"map_sdw_spec' \<equiv>  map_spec' deleted_calls_sdw'"
text_raw \<open>}%EndSnippet\<close>



lemma in_deleted_calls_sdw':
"c\<in>deleted_calls_sdw' vis op hb C k \<longleftrightarrow> c\<in>vis \<and> (\<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb)"
  by (auto simp add: deleted_calls_sdw'_def)

definition "C_out_calls C_out op vis \<equiv> {c\<in>vis. \<exists>x. op c = C_out x}"



lemma restrict_calls_def2: "restrict_calls vis op C k = C_out_calls (C \<circ> (\<lambda>u. NestedOp k u)) op vis"
  by (auto simp add: restrict_calls_def C_out_calls_def)



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


lemma deleted_calls_sdw_rel:
  assumes "is_reverse C_in C_out"
  assumes "L = deleted_calls_sdw (sub_context C_in Cs ctxt) k"
and "R = deleted_calls_sdw' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "L = R"
  by (auto simp add: deleted_calls_sdw_def deleted_calls_sdw'_def sub_context_def assms restrict_ctxt_op_def restrict_ctxt_def
      fmap_map_values_def option_bind_def ctxt_restrict_calls_def restrict_map_def
      restrict_relation_def extract_op_def'  map_map_def map_chain_def cOp_def
      split: option.splits call.splits if_splits,
   (metis (mono_tags, lifting) IntI assms(1) call.sel(1) comp_eq_dest_lhs domIff is_reverse_1 option.simps(3) option.simps(5)),
   (metis assms(1) call.collapse call.sel(1) is_reverse_2 option.sel),
   (metis assms(1) call.collapse call.sel(1) is_reverse_2 option.sel))






lemma map_spec_rel[intro]:
  fixes nestedSpec :: "('opn::crdt_op, 'res::{default,from_bool}) crdtSpec"
    and nestedSpec' :: "('op, 'opn, 'res) ccrdtSpec"
    and deletedCalls :: "(('k, 'opn) mapOp, 'res) operationContext \<Rightarrow> 'k \<Rightarrow> callId set"
    and deletedCalls' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set"
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
    and nested_wf: "ccrdtSpec_wf nestedSpec'"
and deletedCalls_rel: 
    "\<And>ctxt C_in C_out Cs k c. \<lbrakk>
      is_reverse C_in C_out;
      Cs \<subseteq> dom (calls ctxt);
      \<exists>co. Op ctxt c \<triangleq> C_out co
     \<rbrakk> \<Longrightarrow>
          c \<in> deleted_calls (sub_context C_in Cs ctxt) k
      \<longleftrightarrow> c \<in> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "crdt_spec_rel (map_spec deleted_calls  nestedSpec) (map_spec' deleted_calls'  nestedSpec') "
  unfolding crdt_spec_rel_def
proof (intro allI impI)

  show "map_spec deleted_calls nestedSpec op (sub_context C_in Cs ctxt) r 
      = map_spec' deleted_calls' nestedSpec' op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r" 
    (is "?l = ?r")
    if is_rev: "is_reverse C_in C_out"
   and in_out: "C_in outer_op \<triangleq> op"
   and Cs_sub: "Cs \<subseteq> dom (calls ctxt)"
   and wf: "operationContext_wf ctxt"
   for  C_in C_out ctxt outer_op op r Cs
  proof -
(*
    from Cs_sub
    have Cs_sub': "\<forall>c\<in>Cs. \<exists>op op' r. calls ctxt c \<triangleq> Call op r \<and> C_in op \<triangleq> op'"
      by (smt call.collapse in_dom map_chain_eq_some map_map_apply_eq_some)
*)


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
          by (auto simp add: operationContext_ext calls_sub_context happens_before_sub_context restrict_map_def option_bind_def 
              intro!: ext split: option.splits if_splits call.splits)
           (metis call.collapse)+




        show "nestedSpec nestedOp
           (sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs) ctxt) r =
          nestedSpec' nestedOp (Cs - deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
     (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r "
        proof (subst sc2, subst use_crdt_spec_rel[OF nested_rel])        

          show is_rev_combined: "is_reverse (\<lambda>x. C_in x \<bind> nested_op_on_key k) (\<lambda>x. C_out (NestedOp k x))"
            by (auto simp add: is_reverse_def option_bind_def nested_op_on_key_def 
                is_reverse_1[OF is_rev] is_reverse_2[OF is_rev] split: option.splits mapOp.splits)

          show "(C_in (C_out (NestedOp k nestedOp)) \<bind> nested_op_on_key k) \<triangleq> nestedOp"
            using is_rev_combined is_reverse_def by fastforce

          have h1: "c \<in> deleted_calls (sub_context C_in Cs ctxt) k
               \<longleftrightarrow> c \<in> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            if "\<exists>co. Op ctxt c \<triangleq> C_out co"
            for c
            using Cs_sub that
            by (rule deletedCalls_rel[OF is_rev])


          have h2: "\<exists>co'. Op ctxt c \<triangleq> C_out co'"
            if "calls ctxt c \<triangleq> Call co cr" 
                and "C_in co \<triangleq> co'"
              for c co cr co'
            by (metis cOp_def call.sel(1) is_rev is_reverse_1 option.simps(9) that(1) that(2))

          have h2': "\<exists>co'. Op ctxt c \<triangleq> C_out co'"
            if "C_out (NestedOp k y) = extract_op (calls ctxt) c" 
              and "c \<in> Cs"
            for c y
            by (metis (mono_tags, lifting) Cs_sub cOp_def extract_op_def in_dom option.sel option.simps(9) that(1) that(2))


          have h3: "c \<in> deleted_calls (sub_context C_in Cs ctxt) k
               \<longleftrightarrow> c \<in> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            if "calls ctxt c \<triangleq> Call co cr" 
              and "C_in co \<triangleq> co'"
            for c co cr co'
            using h1[OF  h2[OF that]] 
            by auto


          have h4: "
             (dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter> (- DC  \<inter> Cs) )
             =
             ({c \<in> dom (map_map (calls ctxt) call_operation \<ggreater> C_in).
               c \<in> Cs \<and> (\<exists>u. extract_op (calls ctxt) c = C_out (NestedOp k u))} - DC)"
            if "DC = deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            for DC
            by (auto simp add: map_map_def map_chain_def option_bind_def split: option.splits,
              auto simp add: nested_op_on_key_def extract_op_def' is_reverse_2[OF is_rev] split: option.splits mapOp.splits if_splits call.splits,
              use is_rev is_reverse_1 in fastforce)

          show "- deleted_calls (sub_context C_in Cs ctxt) k \<inter>
              {c \<in> Cs. \<exists>x y z. calls ctxt c \<triangleq> Call x y \<and> C_in x \<triangleq> z \<and> nested_op_on_key k z \<noteq> None}
              \<subseteq> dom (calls ctxt)"
            using Cs_sub
            by (auto simp add: map_chain_def option_bind_def map_map_def dom_def dest!: subset_h1 split: option.splits) 


          have subset: "(- deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k \<inter>
                    {c \<in> Cs. \<exists>x. (\<exists>y. calls ctxt c \<triangleq> Call x y) \<and> (\<exists>z. C_in x \<triangleq> z \<and> (\<exists>y. nested_op_on_key k z \<triangleq> y))})
              \<subseteq> (Cs - deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k) "
            by auto



          show "nestedSpec' nestedOp
             (- deleted_calls (sub_context C_in Cs ctxt) k \<inter>
              {c \<in> Cs. \<exists>x y z. calls ctxt c \<triangleq> Call x y \<and> C_in x \<triangleq> z \<and> nested_op_on_key k z \<noteq> None})
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r =
            nestedSpec' nestedOp (Cs - deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) r"
            apply (rule use_ccrdtSpec_wf'[OF nested_wf, symmetric])
               apply (auto simp add: h1 h2' h2 )
            by (smt Cs_sub bind.bind_lunit extract_op_eq is_rev is_rev_combined is_reverse_def subsetD)

          show "operationContext_wf ctxt"
            by (simp add: local.wf)

        qed
      qed

    next
      case (KeyExists k)
      show ?thesis 
      proof (simp add: KeyExists map_spec_def map_spec'_def, 
              rule arg_cong[where f="\<lambda>x. r = from_bool x"])

        show "(\<exists>c op.
                (\<exists>r. calls (sub_context C_in Cs ctxt) c \<triangleq> Call (NestedOp k op) r) \<and>
                is_update op \<and> c \<notin> deleted_calls (sub_context C_in Cs ctxt) k) =
            (\<exists>c\<in>Cs.
                \<exists>upd_op.
                   extract_op (calls ctxt) c = C_out (NestedOp k upd_op) \<and>
                   is_update upd_op \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)"
        proof (auto simp add: Bex_def calls_sub_context option_bind_def dom_map_chain restrict_map_def split: option.splits, fuzzy_goal_cases A B)
          case (A c y)
          show ?case
          proof (auto intro!: exI[where x=c])
            show "c \<in> Cs"
              using A(1) A(2) by auto
            show "\<exists>upd_op.
             extract_op (calls ctxt) c = C_out (NestedOp k upd_op) \<and>
             is_update upd_op \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
              using A  
            proof (auto simp add: extract_op_def' split: option.splits call.splits )
              fix x1 :: 'op and x2 :: 'res
              assume a1: "y = Call x1 x2"
              have "\<forall>m z. C_out m = z \<or> C_in z \<noteq> Some m"
                by (meson is_rev is_reverse_def)
              then show "\<exists>z. x1 = C_out (NestedOp k z) \<and> is_update z \<and> c \<notin> deleted_calls' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
                by (smt A(2) A.All_conj Cs_sub a1 assms(3) cOp_def call.sel(1) is_rev option.exhaust_sel option.map(2))
            qed
          qed

        next
          case (B c upd_op)
          show ?case
          proof (rule exI[where x=c], auto)
            show " \<exists>y. calls ctxt c \<triangleq> y"
              using B.member Cs_sub by blast
            show "\<And>x2. \<lbrakk>C_in (call_operation x2) = None; calls ctxt c \<triangleq> x2\<rbrakk> \<Longrightarrow> False"
              by (metis B.extract_op_eq extract_op_def is_rev is_reverse_2 option.discI option.sel)

            show "\<exists>op. x2a = NestedOp k op \<and> is_update op \<and> c \<notin> deleted_calls (sub_context C_in Cs ctxt) k"
              if c0: "C_in (call_operation x2) \<triangleq> x2a"
                and c1: "calls ctxt c \<triangleq> x2"
                and c2: "c \<in> Cs"
              for  x2 x2a
              by (smt B.extract_op_eq B.is_update B.not_member Cs_sub c0 c1 cOp_def deletedCalls_rel extract_op_def is_rev is_reverse_2 option.sel option.simps(9))

            show "\<And>x2 x2a. \<lbrakk>C_in (call_operation x2) \<triangleq> x2a; calls ctxt c \<triangleq> x2\<rbrakk> \<Longrightarrow> c \<in> Cs"
              by (simp add: B.member)
          qed
        qed
      qed
    next
      case (DeleteKey k)
      then show ?thesis
        by (auto simp add: map_spec_def map_spec'_def)
    qed


  qed
qed



lemma map_sdw_spec_rel[intro!]:
  fixes nestedSpec' :: "('op, 'opn::crdt_op, 'res::from_bool) ccrdtSpec"
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
    and nested_wf: "ccrdtSpec_wf nestedSpec'"
  shows "crdt_spec_rel (map_sdw_spec nestedSpec) (map_sdw_spec' nestedSpec') "
  unfolding map_sdw_spec'_def map_sdw_spec_def
proof (rule map_spec_rel[OF nested_rel nested_wf])

  show "(c \<in> deleted_calls_sdw (sub_context C_in Cs ctxt) k) = (c \<in> deleted_calls_sdw' Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)"
    if c0: "is_reverse C_in C_out"
      and c1: "Cs \<subseteq> dom (calls ctxt)"
      and c2: "\<exists>co. Op ctxt c \<triangleq> C_out co"
    for  ctxt C_in C_out Cs k c
  apply (auto simp add: deleted_calls_sdw_def deleted_calls_sdw'_def calls_subcontext_some)
    apply (auto simp add: Op_subcontext)
    apply (auto simp add: cOp_def sub_context_def
restrict_ctxt_op_def restrict_ctxt_def ctxt_restrict_calls_def restrict_relation_def
fmap_map_values_def extract_op_def
is_reverse_1[OF c0] is_reverse_2[OF c0])
  subgoal
  using c0 is_reverse_1 by force
  subgoal for d 
  proof -
    assume a0: "c \<in> Cs"
      and a1: "d \<in> Cs"
      and a2: "call_operation (the (calls ctxt d)) = C_out (DeleteKey k)"
      and a3: "(d, c) \<notin> happensBefore ctxt"


    obtain x_call where "calls ctxt c \<triangleq> x_call"
      using a0 c1 by auto

    show "\<exists>y ci'. calls ctxt c \<triangleq> ci' \<and> call_res y = call_res ci' \<and> C_in (call_operation ci') \<triangleq> call_operation y"
    proof (intro conjI exI)
      show "calls ctxt c \<triangleq> x_call"
        by (simp add: \<open>calls ctxt c \<triangleq> x_call\<close>)

      show "call_res (Call (the (C_in (call_operation x_call))) (call_res x_call)) = call_res x_call"
        by simp

      show "C_in (call_operation x_call) \<triangleq> call_operation (Call (the (C_in (call_operation x_call))) (call_res x_call))"
        apply auto
        by (metis \<open>calls ctxt c \<triangleq> x_call\<close> c0 c2 cOp_def is_reverse_def map_option_eq_Some option.sel)
    qed
  qed

  subgoal
    using c0 c1 is_reverse_2 by force
  done
qed

lemma restrict_calls_wf:
  assumes " map_same_on Cs op op'"
  shows "restrict_calls Cs op C_out k
  = restrict_calls Cs op' C_out k"
  using assms by (auto simp add: restrict_calls_def map_same_on_def)


lemma map_spec_wf[simp]:
  assumes nested: "\<And>oper. ccrdtSpec_wf nested"
    and dwf: "\<forall>oper Cs Cs' op op' hb hb' C_out k c. 
      map_same_on Cs' op op'
      \<longrightarrow> rel_same_on Cs' hb hb'
      \<longrightarrow> Cs' \<subseteq> Cs
      \<longrightarrow> (\<forall>c\<in>Cs. (\<exists>y. C_out y = op c) \<longrightarrow> c \<in> Cs')
      \<longrightarrow> c \<in> Cs'
      \<longrightarrow> (c \<in> deleted_calls Cs op hb C_out k \<longleftrightarrow> c \<in> deleted_calls Cs' op' hb' C_out k)"
  shows
    "ccrdtSpec_wf (map_spec' deleted_calls nested)"
proof (simp add: ccrdtSpec_wf_def; intro impI allI)

  show "map_spec' deleted_calls nested opr Cs op hb C_out r = map_spec' deleted_calls nested opr Cs' op' hb' C_out r"
    if c0: "map_same_on Cs' op op'"
      and c1: "rel_same_on Cs' hb hb'"
      and c2: "Cs' \<subseteq> Cs"
      and c3: "\<forall>c\<in>Cs. (\<exists>y. C_out y = op c) \<longrightarrow> c \<in> Cs'"
    for  opr Cs Cs' op op' hb hb' C_out r
  proof -


    show "map_spec' deleted_calls nested opr Cs op hb C_out r 
        = map_spec' deleted_calls nested opr Cs' op' hb' C_out r"
      unfolding map_spec'_def proof (cases opr; clarsimp)
      case (NestedOp k nop)

      show "nested nop (Cs - deleted_calls Cs op hb C_out k) op hb (\<lambda>x. C_out (NestedOp k x)) r
          = nested nop (Cs' - deleted_calls Cs' op' hb' C_out k) op' hb' (\<lambda>x. C_out (NestedOp k x)) r"
      proof (rule use_ccrdtSpec_wf'[OF nested])
        show "map_same_on (Cs' - deleted_calls Cs' op' hb' C_out k) op op'"
          by (meson DiffD1 c0 map_same_on_def)
        show "rel_same_on (Cs' - deleted_calls Cs' op' hb' C_out k) hb hb'"
          by (meson DiffD1 c1 rel_same_on_def)
        show "Cs' - deleted_calls Cs' op' hb' C_out k \<subseteq> Cs - deleted_calls Cs op hb C_out k"
          apply auto
          using c2 apply blast
          using c0 c1 c2 c3 dwf by blast
        show "\<And>c. \<lbrakk>c \<in> Cs - deleted_calls Cs op hb C_out k; \<exists>y. C_out (NestedOp k y) = op c\<rbrakk> \<Longrightarrow> c \<in> Cs' - deleted_calls Cs' op' hb' C_out k"
          apply (auto simp add: Diff_iff)
          using c3 apply blast
          using c0 c1 c2 c3 dwf by blast
      qed
    next
      case (KeyExists x2)
      show "(r =
           from_bool
            (\<exists>c\<in>Cs. \<exists>upd_op. op c = C_out (NestedOp x2 upd_op) \<and> is_update upd_op \<and> c \<notin> deleted_calls Cs op hb C_out x2)) =
          (r =
           from_bool
            (\<exists>c\<in>Cs'. \<exists>upd_op. op' c = C_out (NestedOp x2 upd_op) \<and> is_update upd_op \<and> c \<notin> deleted_calls Cs' op' hb' C_out x2))"
        apply (auto intro!: arg_cong[where f="from_bool"])
        subgoal for c upd_op
          apply (rule bexI[where x=c])
           apply (rule exI[where x=upd_op])
           apply auto
            apply (metis c0 c3 map_same_on_def)
           apply (metis (mono_tags, lifting) c0 c1 c2 c3 dwf)
          using c3 by fastforce
        subgoal for c upd_op
          apply (rule bexI[where x=c])
           apply (rule exI[where x=upd_op])
           apply auto
            apply (metis c0 map_same_on_def)
           apply (metis (mono_tags, lifting) c0 c1 c2 c3 dwf)
          using c2 by blast
        subgoal for c upd_op
          apply (rule bexI[where x=c])
           apply (rule exI[where x=upd_op])
           apply auto
            apply (metis c0 map_same_on_def)
           apply (metis (mono_tags, lifting) c0 c1 c2 c3 dwf)
          using c2 by blast
        subgoal for c upd_op
          apply (rule bexI[where x=c])
           apply (rule exI[where x=upd_op])
           apply auto
            apply (metis c0 c3 map_same_on_def)
           apply (metis (mono_tags, lifting) c0 c1 c2 c3 dwf)
          using c3 by fastforce
        done
    qed
  qed
qed

lemma map_sdw_spec_wf[intro!]:
  assumes nested_rel: "ccrdtSpec_wf nestedSpec"
  shows "ccrdtSpec_wf (map_sdw_spec' nestedSpec)"
  unfolding map_sdw_spec'_def using nested_rel
proof (rule map_spec_wf; intro allI impI)


  show "(c \<in> deleted_calls_sdw' Cs op hb C_out k) = (c \<in> deleted_calls_sdw' Cs' op' hb' C_out k)"
    if c0: "ccrdtSpec_wf nestedSpec"
      and c1: "map_same_on Cs' op op'"
      and c2: "rel_same_on Cs' hb hb'"
      and c3: "Cs' \<subseteq> Cs"
      and c4: "\<forall>c\<in>Cs. (\<exists>y. C_out y = op c) \<longrightarrow> c \<in> Cs'"
      and c5: "c \<in> Cs'"
    for  oper Cs Cs' op op' hb hb' C_out k c
    apply (auto simp add: deleted_calls_sdw'_def map_same_on_def rel_same_on_def)
    subgoal
      using c5 by auto
    subgoal
      by (smt c1 c2 c4 c5 map_same_on_def rel_same_on_def)
    subgoal
      using c3 by blast
    subgoal
      by (smt c1 c2 c3 in_mono map_same_on_def rel_same_on_def)
    done
qed



subsection "Structs"



definition struct_field' :: "('opn \<Rightarrow> 'a) \<Rightarrow> ('op, 'opn, 'res) ccrdtSpec \<Rightarrow> ('op, 'a, 'res) ccrdtSpec " where
"struct_field' C_out spec opr  \<equiv> 
  \<lambda> vis op hb x_C_out res.
    case select_field C_out opr of 
      Some i_op \<Rightarrow> spec i_op vis op hb (x_C_out \<circ> C_out)  res
    | None \<Rightarrow> False
"

definition compose_struct' :: "('op, 'opn, 'r) ccrdtSpec \<Rightarrow> ('op, 'opn, 'r) ccrdtSpec \<Rightarrow> ('op, 'opn, 'r) ccrdtSpec" (infixr ".\<or>.." 30) where
"A .\<or>.. B \<equiv> \<lambda>opr vis op hb f r. A opr vis op hb f r \<or> B opr vis op hb f r"


lemma compose_struct'_simp[simp]:
"(A .\<or>.. B) opr vis op hb f r \<longleftrightarrow> A opr vis op hb f r \<or> B opr vis op hb f r"
  unfolding compose_struct'_def by auto

lemma struct_field'_same[simp]:
  assumes "inj f"
  shows "struct_field' f spec (f opr) vis op hb out1 r  \<longleftrightarrow> spec opr vis op hb (out1 \<circ> f) r"
  using assms by (auto simp add: struct_field'_def is_reverse_2 select_field_reverse split: option.splits)


lemma struct_field'_different[simp]:
  assumes "\<And>x y. f x \<noteq> g y"
  shows "\<not>struct_field' f spec (g opr) vis op hb out1 r"
  by (metis (no_types, lifting) assms option.simps(4) select_field_def struct_field'_def)


lemma crdt_spec_rel_struct_field[intro!]:
  fixes nspec :: "('opn, 'r) crdtSpec"
    and nspec' :: "('op, 'opn, 'r) ccrdtSpec"
  assumes rel: "crdt_spec_rel nspec nspec'"
    and f_inj: "inj f"
  shows "crdt_spec_rel (struct_field f nspec) (struct_field' f nspec')"
proof (rule show_crdt_spec_rel')

  show "struct_field f nspec op (sub_context C_in Cs ctxt) r
      = struct_field' f nspec' op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
    if c0: "is_reverse C_in C_out"
      and c1: "operationContext_wf ctxt"
      and c2: "C_in outer_op \<triangleq> op"
      and c3: "Cs \<subseteq> dom (calls ctxt)"
    for  C_in C_out ctxt outer_op op r Cs
   unfolding struct_field_def struct_field'_def
  proof (cases "select_field f op"; clarsimp)
    case (Some op')

    show "nspec op' (restrict_ctxt_op (select_field f) (sub_context C_in Cs ctxt)) r 
        = nspec' op' Cs (extract_op (calls ctxt))
          (happensBefore ctxt) (C_out \<circ> f) r"
    proof (fuzzy_rule use_crdt_spec_rel[OF rel])

      show "is_reverse (C_in \<ggreater> select_field f) (C_out \<circ> f)"
        by (simp add: c0 f_inj is_reverse_combine select_field_reverse)

      show "(C_in \<ggreater> select_field f) outer_op \<triangleq> op'"
        by (simp add: Some c2 map_chain_eq_some)

      show "operationContext_wf ctxt" using c1 .

      show " Cs \<subseteq> dom (calls ctxt)"
        by (simp add: c3)

      show "sub_context (C_in \<ggreater> select_field f) Cs ctxt
         = restrict_ctxt_op (select_field f) (sub_context C_in Cs ctxt)"
        using is_reverse_1[OF c0]
        by (auto simp add: sub_context_def C_out_calls_def select_field_def
            restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def
            ctxt_restrict_calls_def restrict_map_def extract_op_def 
            option_bind_def map_chain_def
            restrict_relation_def
            fmap_map_values_def intro!: HOL.ext
            split: option.splits if_splits)
          metis+
    qed
  qed
qed






lemma crdt_spec_rel_compose[intro!]:
  assumes relA: "crdt_spec_rel specA specA'"
    and relB: "crdt_spec_rel specB specB'"
  shows "crdt_spec_rel (specA .\<or>. specB) (specA' .\<or>.. specB')"
  using assms  by (auto simp add: compose_struct_def compose_struct'_def dom_calls_sub_context_rewrite 
      use_crdt_spec_rel1 dom_calls_sub_context_rewrite inf.absorb_iff2 use_crdt_spec_rel2 intro!: show_crdt_spec_rel)



lemma struct_field_wf[intro!]:
  assumes nested_rel: "ccrdtSpec_wf nestedSpec"
  shows "ccrdtSpec_wf (struct_field' C_out nestedSpec)"
proof (clarsimp simp add: ccrdtSpec_wf_def struct_field'_def C_out_calls_def split: option.splits)

  show "nestedSpec x2 Cs op hb (C_outa \<circ> C_out) r 
    = nestedSpec x2 Cs' op' hb' (C_outa \<circ> C_out) r"
    if c0: "map_same_on Cs' op op'"
   and c1: "rel_same_on Cs' hb hb'"
   and c2: "Cs' \<subseteq> Cs"
   and c3: "\<forall>c\<in>Cs. (\<exists>y. C_outa y = op c) \<longrightarrow> c \<in> Cs'"
   and c4: "select_field C_out opr \<triangleq> x2"
 for  opr Cs Cs' op op' hb hb' C_outa r x2
    by (metis (mono_tags, lifting) c0 c1 c2 c3 comp_apply nested_rel use_ccrdtSpec_wf')
qed

lemma struct_compose_wf[intro!]:
  assumes wfA: "ccrdtSpec_wf specA"
    and wfB: "ccrdtSpec_wf specB"
  shows "ccrdtSpec_wf (specA .\<or>.. specB)"
  by (auto simp add: ccrdtSpec_wf_def compose_struct'_def use_ccrdtSpec_wf'1[OF wfA] use_ccrdtSpec_wf'1[OF wfB]
      use_ccrdtSpec_wf'2[OF wfA] use_ccrdtSpec_wf'2[OF wfB])


lemma sub_context_id: 
  assumes calls_sub: "dom (calls ctxt) \<subseteq> c_calls"
    and hb_wf: "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  shows "(sub_context Some c_calls ctxt) = ctxt"
proof (auto simp add: operationContext_ext calls_sub_context happens_before_sub_context restrict_map_def intro!: ext)
  show "\<And>c. c \<notin> c_calls \<Longrightarrow> None = calls ctxt c"
using calls_sub domIff by force
  show "\<And>a b. \<lbrakk>(a, b) \<in> happensBefore ctxt; a \<in> c_calls\<rbrakk> \<Longrightarrow> \<exists>y. calls ctxt a \<triangleq> y"
    by (meson FieldI1 hb_wf in_dom)
  show "\<And>a b. (a, b) \<in> happensBefore ctxt \<Longrightarrow> a \<in> c_calls"
    by (meson FieldI1 calls_sub hb_wf subset_h1)
  show "\<And>a b. \<lbrakk>(a, b) \<in> happensBefore ctxt; b \<in> c_calls\<rbrakk> \<Longrightarrow> \<exists>y. calls ctxt b \<triangleq> y"
    by (meson FieldI2 hb_wf in_dom)
  show "\<And>a b. (a, b) \<in> happensBefore ctxt \<Longrightarrow> b \<in> c_calls "
    by (meson FieldI2 calls_sub hb_wf subset_h1)
qed

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


end