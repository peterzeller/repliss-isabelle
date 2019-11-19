theory crdt_specs
imports repliss_sem
begin

section "Composable CRDT specifications"

text "In this section we define the semantics of several conflict-free replicated data types (CRDTs)."

type_synonym ('op, 'res) crdtSpec = "'op \<Rightarrow> ('op, 'res) operationContext \<Rightarrow> 'res \<Rightarrow> bool"

text "Some helper functions for defining the specs:"

definition map_map_values :: "('x \<Rightarrow> 'y) \<Rightarrow> ('k \<rightharpoonup> 'x) \<Rightarrow> ('k \<rightharpoonup> 'y)" where
"map_map_values f m \<equiv> \<lambda>x. case m x of Some a \<Rightarrow> Some (f a) | None \<Rightarrow> None"

definition fmap_map_values :: "('x \<rightharpoonup> 'y) \<Rightarrow> ('k \<rightharpoonup> 'x) \<Rightarrow> ('k \<rightharpoonup> 'y)" where
"fmap_map_values f m \<equiv> \<lambda>x. case m x of Some a \<Rightarrow> f a | None \<Rightarrow> None"

definition 
"map_ctxt f c \<equiv> c\<lparr>calls := map_map_values f (calls c)\<rparr>"

definition 
"restrict_ctxt f ctxt \<equiv> \<lparr>calls = fmap_map_values f (calls ctxt), happensBefore = happensBefore ctxt |r {c | c x. calls ctxt c \<triangleq> x \<and> f x \<noteq> None } \<rparr>"

definition restrict_ctxt_op :: "('op1 \<rightharpoonup> 'op2) \<Rightarrow>   ('op1, 'r) operationContext \<Rightarrow>   ('op2, 'r) operationContext" where
"restrict_ctxt_op f \<equiv> 
  restrict_ctxt (\<lambda>c. 
    case c of Call op r \<Rightarrow> (case f op of Some op' \<Rightarrow> Some (Call op' r) | None \<Rightarrow> None))
"

definition ctxt_remove_calls :: "callId set \<Rightarrow> ('op, 'r) operationContext \<Rightarrow> ('op, 'r) operationContext"  where
"ctxt_remove_calls Cs ctxt = \<lparr>calls = calls ctxt |` Cs, happensBefore = happensBefore ctxt |r Cs\<rparr>"


text "To make it easier to simplify composed specifications, we define well-formedness of specifications:
A spec is well formed if it only uses happens-before information from existing calls."

definition crdt_spec_wf :: "('op, 'res) crdtSpec \<Rightarrow> bool" where
"crdt_spec_wf spec \<equiv>
  \<forall>op ctxt r. spec op ctxt r \<longleftrightarrow> spec op (ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>) r"

lemma use_crdt_spec_wf:
  assumes "crdt_spec_wf spec"
shows "spec op ctxt res \<longleftrightarrow> spec op (ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>) res"
  using assms by (auto simp add: crdt_spec_wf_def)


lemma use_crdt_spec_wf2:
  assumes wf: "crdt_spec_wf spec"
and c: "calls ctxt = calls ctxt'"
and h: "happensBefore ctxt |r dom (calls ctxt) = happensBefore ctxt' |r dom (calls ctxt)"
shows "spec op ctxt res \<longleftrightarrow> spec op ctxt' res"
  using assms 
proof -
  have 1: "spec op ctxt res = spec op (ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>) res"
    by (rule use_crdt_spec_wf[OF wf])

  have 2: "spec op ctxt' res = spec op (ctxt'\<lparr>happensBefore := happensBefore ctxt' |r dom (calls ctxt')\<rparr>) res"
    by (rule use_crdt_spec_wf[OF wf])


  have 3: "ctxt'\<lparr>happensBefore := happensBefore ctxt' |r dom (calls ctxt')\<rparr>
      = ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>"
    using c h by auto

  show "spec op ctxt res = spec op ctxt' res"
    by (simp add: "1" "2" "3")
qed


lemma use_crdt_spec_wf3:
  assumes wf: "crdt_spec_wf spec"
and 1: "spec op ctxt res"
and c: "calls ctxt = calls ctxt'"
and h: "happensBefore ctxt |r dom (calls ctxt) = happensBefore ctxt' |r dom (calls ctxt)"
shows "spec op ctxt' res"
  by (meson "1" c h local.wf use_crdt_spec_wf2)





subsection "Register"

datatype 'a registerOp =
    Assign 'a
  | Read

text "The latest values are all assigned values that have not been overridden by another call to assign."

definition 
"latestAssignments ctxt \<equiv> 
   \<lambda>c. case calls ctxt c of 
    Some (Call (Assign v) r) \<Rightarrow> 
        if \<exists>c' v' r'. calls ctxt c' \<triangleq> Call (Assign v') r' \<and> (c,c')\<in>happensBefore ctxt then None else Some v
  | _ \<Rightarrow> None"

definition 
"latestValues ctxt \<equiv> Map.ran (latestAssignments ctxt)" 

lemma latestValues_def2:
"latestValues ctxt =
  {v | c v r . calls ctxt c \<triangleq> Call (Assign v) r  
        \<and> (\<nexists>c' v' r'. calls ctxt c' \<triangleq> Call (Assign v') r' \<and> (c,c')\<in>happensBefore ctxt)}" 
  apply (auto simp add: latestValues_def latestAssignments_def image_def ran_def split: option.splits call.splits )
  apply (case_tac y, auto)
  apply (case_tac x1, auto split: if_splits)
  done






definition register_spec :: "'a \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> True
  | Read \<Rightarrow> if latestValues ctxt = {} then res = initial else res \<in> latestValues ctxt "


lemma latest_assignments_wf:
"latestAssignments (ctxt\<lparr>happensBefore := Restr (happensBefore ctxt) (dom (calls ctxt))\<rparr>)
= latestAssignments ctxt"
  by (auto simp add: latestAssignments_def intro!: ext split: call.splits option.splits registerOp.splits, auto)



lemma latest_assignments_wf2:
"latestAssignments (ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>)
= latestAssignments ctxt"
  by (simp add: latest_assignments_wf restrict_relation_def)


lemma register_spec_wf: "crdt_spec_wf (register_spec i)"
  by (auto simp add:  crdt_spec_wf_def register_spec_def latest_assignments_wf2 latestValues_def split: registerOp.splits)


text "To define LWW-registers, we use some arbitrary order on calls.
First we show that this exists:"


definition some_well_order :: "'a rel" where
 "some_well_order \<equiv> (SOME ord. well_order ord)"

lemma some_well_order_is_well_order: "well_order some_well_order"
  by (metis someI_ex some_well_order_def well_ordering)

lemma some_well_order_is_linear_order: "linear_order some_well_order"
  using some_well_order_is_well_order well_order_on_def by blast

lemma some_well_order_is_wo_rel: "wo_rel some_well_order"
  using some_well_order_is_well_order well_order_on_Well_order wo_rel_def by blast

lemma some_well_order_includes_all: "S \<subseteq> Field some_well_order"
  using some_well_order_is_well_order well_order_on_Field by fastforce


definition firstValue :: "'a \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'a" where
"firstValue d m \<equiv> if m = Map.empty then d else 
  let maxK = wo_rel.minim some_well_order (dom m) in
  the (m maxK)
  "


lemma firstValue_in_ran:
  assumes "finite (dom m)"
and not_default: "firstValue d m \<noteq> d"
shows "firstValue d m \<in> Map.ran m"
  using not_default proof (auto simp add: firstValue_def )
  assume "m \<noteq> Map.empty"
  have "(wo_rel.minim some_well_order (dom m)) \<in> dom m"
    by (simp add: \<open>m \<noteq> Map.empty\<close> some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)


  from this
  show "the (m (wo_rel.minim some_well_order (dom m))) \<in> ran m"
    by (meson domIff option.exhaust_sel ranI)
qed


definition lww_register_spec :: "'a \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"lww_register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> True
  | Read \<Rightarrow> res = firstValue initial (latestAssignments ctxt)"

lemma lwwregister_spec_wf: "crdt_spec_wf (lww_register_spec i)"
  by (auto simp add:  crdt_spec_wf_def lww_register_spec_def latest_assignments_wf2 latestValues_def split: registerOp.splits)



subsection "Multi-Value Register"


definition mv_register_spec :: "('a \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"mv_register_spec is_set oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> True
  | Read \<Rightarrow> is_set res (latestValues ctxt)"

lemma mv_register_spec_wf: "crdt_spec_wf (mv_register_spec f)"
  by (auto simp add: crdt_spec_wf_def mv_register_spec_def latestValues_def latest_assignments_wf2 split: registerOp.splits)


subsection "Maps"

datatype ('k,'v) mapOp =
      NestedOp 'k 'v
    | KeyExists 'k
    | DeleteKey 'k


definition
"nested_op_on_key k op \<equiv> case op of NestedOp k' op' \<Rightarrow> if k = k' then Some op' else None | _ \<Rightarrow> None"

definition
"deleted_calls_uw ctxt k \<equiv> {c\<in>dom (calls ctxt).  \<exists>c' r. calls ctxt c' \<triangleq> Call (DeleteKey k) r \<and> (c,c')\<in>happensBefore ctxt}"

definition
"deleted_calls_dw ctxt k \<equiv> {c\<in>dom (calls ctxt). \<exists>c' r. calls ctxt c' \<triangleq> Call (DeleteKey k) r \<and> (c',c)\<notin>happensBefore ctxt}"


definition map_spec :: "((('k, 'v) mapOp, 'r) operationContext \<Rightarrow> 'k \<Rightarrow> callId set) \<Rightarrow>  ('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_spec deleted_calls nestedSpec oper ctxt res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> True
  | KeyExists k \<Rightarrow> \<exists>c\<in>dom (calls ctxt). c \<notin> deleted_calls ctxt k
  | NestedOp k op \<Rightarrow>
     nestedSpec op (restrict_ctxt_op (nested_op_on_key k) 
          (ctxt_remove_calls (deleted_calls ctxt k) ctxt)) res
"

definition map_uw_spec :: "('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_uw_spec \<equiv> map_spec deleted_calls_uw"

definition map_dw_spec :: "('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_dw_spec \<equiv> map_spec deleted_calls_dw"


lemma calls_ctxt_remove_calls: "calls (ctxt_remove_calls S ctxt) c = (calls ctxt |` S) c"
  by (auto simp add: ctxt_remove_calls_def)

lemma calls_restrict_ctxt_op: "calls (restrict_ctxt_op f ctxt) c
  = (case calls ctxt c of None \<Rightarrow> None | Some (Call op r) \<Rightarrow> (case f op of None \<Rightarrow> None | Some op' \<Rightarrow> Some (Call op' r)))"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def)

lemma happensBefore_restrict_ctxt_op:  "(c, c') \<in> happensBefore (restrict_ctxt_op f ctxt) \<longleftrightarrow> 
(\<exists>op r op' r'. (c, c') \<in> happensBefore ctxt 
  \<and> calls ctxt c \<triangleq> Call op r \<and> f op \<noteq> None 
  \<and> calls ctxt c' \<triangleq> Call op' r' \<and> f op' \<noteq> None)"
  apply (auto simp add: restrict_ctxt_op_def restrict_ctxt_def restrict_relation_def split: call.splits option.splits)
    apply (meson call.exhaust option.exhaust)
  apply force
  apply force
  done

lemma happensBefore_ctxt_remove_calls: "(c, c') \<in> happensBefore (ctxt_remove_calls S ctxt) \<longleftrightarrow> (c, c') \<in> happensBefore ctxt |r S"
  by (auto simp add: ctxt_remove_calls_def)

lemma map_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
    and deleted_calls_wf: "\<And>ctxt. deleted_calls (ctxt\<lparr>happensBefore := Restr (happensBefore ctxt) (dom (calls ctxt))\<rparr>) = deleted_calls ctxt"
  shows "crdt_spec_wf (map_spec deleted_calls nested)"
  by (auto simp add: crdt_spec_wf_def map_spec_def  
      deleted_calls_wf calls_ctxt_remove_calls calls_restrict_ctxt_op restrict_map_def restrict_relation_def deleted_calls_uw_def 
      happensBefore_restrict_ctxt_op happensBefore_ctxt_remove_calls 
      intro!: ext 
      split: option.splits call.splits mapOp.splits if_splits
      elim!: use_crdt_spec_wf3[OF wf])

lemma map_uw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_uw_spec  nested)"
  using wf unfolding map_uw_spec_def by (rule map_spec_wf, auto simp add: deleted_calls_uw_def intro!: ext, auto)

lemma map_dw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_dw_spec  nested)"
  using wf unfolding map_dw_spec_def by (rule map_spec_wf, auto simp add: deleted_calls_dw_def intro!: ext, auto)






end