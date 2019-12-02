theory crdt_specs
  imports repliss_sem
 unique_ids
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

text "To combine CRDT specifications, we need to distinguish updates from queries, which we can do using
the following typeclass:"

class crdt_op = valueType +
  fixes is_update :: "'a \<Rightarrow> bool"
begin

end

abbreviation "is_query x \<equiv> \<not>is_update x"


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

instance registerOp :: (countable) countable
  by countable_datatype
instantiation registerOp :: (valueType) crdt_op begin
definition  "uniqueIds_registerOp x \<equiv> 
  case x of 
     Assign x \<Rightarrow> uniqueIds x
   | Read \<Rightarrow> {}"
definition [simp]: "default_registerOp \<equiv> Read"
definition [simp]: "is_update_registerOp x \<equiv> x \<noteq> Read"

lemma [simp]: "uniqueIds (Assign x) = uniqueIds x"
  and [simp]: "uniqueIds Read = {}"
  by (auto simp add: uniqueIds_registerOp_def)

instance by (standard, auto simp add: uniqueIds_registerOp_def)
end

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






definition register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
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


definition lww_register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"lww_register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> res = firstValue initial (latestAssignments ctxt)"

lemma lwwregister_spec_wf: "crdt_spec_wf (lww_register_spec i)"
  by (auto simp add:  crdt_spec_wf_def lww_register_spec_def latest_assignments_wf2 latestValues_def split: registerOp.splits)



subsection "Multi-Value Register"


definition mv_register_spec :: "('a::default \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"mv_register_spec is_set oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> is_set res (latestValues ctxt)"

lemma mv_register_spec_wf: "crdt_spec_wf (mv_register_spec f)"
  by (auto simp add: crdt_spec_wf_def mv_register_spec_def latestValues_def latest_assignments_wf2 split: registerOp.splits)

subsection "Sets"

datatype 'v setOp =
    Add 'v
  | Remove 'v
  | Contains 'v
 
instance setOp :: (countable) countable
  by countable_datatype
instantiation setOp :: (valueType) crdt_op begin
definition  "uniqueIds_setOp x \<equiv> 
  case x of 
     Add v \<Rightarrow> uniqueIds v
   | Remove v \<Rightarrow> uniqueIds v
   | Contains v \<Rightarrow> uniqueIds v"
definition [simp]: "default_setOp \<equiv> Add default"
definition "is_update_setOp x \<equiv> case x of Add _ \<Rightarrow> True | Remove _ \<Rightarrow> True | Contains _ \<Rightarrow> False"

lemma [simp]: "uniqueIds (Add v) = uniqueIds v"
  and [simp]:"uniqueIds (Remove v) = uniqueIds v"
  and [simp]:"uniqueIds (Contains v) = uniqueIds v"
  by (auto simp add: uniqueIds_setOp_def)

lemma [simp]: "is_update (Add v) = True"
  and [simp]:"is_update (Remove v) = True"
  and [simp]:"is_update (Contains v) = False"
  by (auto simp add: is_update_setOp_def)

instance by (standard, auto simp add: uniqueIds_setOp_def)
end

definition set_aw_spec :: "(bool \<Rightarrow> 'r::default) \<Rightarrow> ('v setOp, 'r) crdtSpec" where
"set_aw_spec from_bool op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a. calls ctxt a \<triangleq> Call (Add v) default 
                           \<and> (\<nexists>r. calls ctxt r \<triangleq> Call (Remove v) default \<and> (a,r)\<in>happensBefore ctxt))"



definition set_rw_spec :: "(bool \<Rightarrow> 'r::default) \<Rightarrow> ('v setOp, 'r) crdtSpec" where
"set_rw_spec from_bool op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a. calls ctxt a \<triangleq> Call (Add v) default 
                           \<and> (\<forall>r. calls ctxt r \<triangleq> Call (Remove v) default 
                               \<longrightarrow> (\<exists>a'. calls ctxt a' \<triangleq> Call (Add v) default \<and> (r,a)\<in>happensBefore ctxt)))"



text "Alternative definition: 
The following definition is closer to the @{term set_aw_spec} in the structure of the formula.
However, the semantic is strange in the sense that an add-operation does not overwrite the removes that came before it." 
definition set_rw_spec2 :: "(bool \<Rightarrow> 'r::default) \<Rightarrow> ('v setOp, 'r) crdtSpec" where
"set_rw_spec2 from_bool op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a. calls ctxt a \<triangleq> Call (Add v) default 
                           \<and> (\<nexists>r. calls ctxt r \<triangleq> Call (Remove v) default \<and> (r,a)\<notin>happensBefore ctxt))"







subsection "Maps"

datatype ('k,'v) mapOp =
      NestedOp 'k 'v
    | KeyExists 'k
    | DeleteKey 'k

instance mapOp :: (countable,countable) countable
  by countable_datatype
instantiation mapOp :: (valueType,crdt_op) crdt_op begin
definition  "uniqueIds_mapOp x \<equiv> 
  case x of 
     NestedOp k v \<Rightarrow> uniqueIds k \<union> uniqueIds v
   | KeyExists k \<Rightarrow> uniqueIds k
   | DeleteKey k \<Rightarrow> uniqueIds k"
definition [simp]: "default_mapOp \<equiv> KeyExists default"
definition "is_update_mapOp x \<equiv> case x of NestedOp k v \<Rightarrow> is_update v | DeleteKey _ \<Rightarrow> True | KeyExists _ \<Rightarrow> False"


lemma [simp]: "uniqueIds (NestedOp k v) = uniqueIds k \<union> uniqueIds v"
  and [simp]: "uniqueIds (KeyExists k) = uniqueIds k"
  and [simp]: "uniqueIds (DeleteKey k) = uniqueIds k"
  by (auto simp add: uniqueIds_mapOp_def)

lemma [simp]: "is_update (NestedOp k v) = is_update v"
  and [simp]: "is_update (KeyExists k) = False"
  and [simp]: "is_update (DeleteKey k) = True"
  by (auto simp add: is_update_mapOp_def)


instance by (standard, auto simp add: uniqueIds_mapOp_def)
end


definition
"nested_op_on_key k op \<equiv> case op of NestedOp k' op' \<Rightarrow> if k = k' then Some op' else None | _ \<Rightarrow> None"

definition
"deleted_calls_uw ctxt k \<equiv> {c\<in>dom (calls ctxt).  \<exists>c' r. calls ctxt c' \<triangleq> Call (DeleteKey k) r \<and> (c,c')\<in>happensBefore ctxt}"

definition
"deleted_calls_dw ctxt k \<equiv> {c\<in>dom (calls ctxt). \<exists>c' r. calls ctxt c' \<triangleq> Call (DeleteKey k) r \<and> (c',c)\<notin>happensBefore ctxt}"


definition map_spec :: "((('k, 'v::crdt_op) mapOp, 'r::default) operationContext \<Rightarrow> 'k \<Rightarrow> callId set) \<Rightarrow> (bool \<Rightarrow> 'r) \<Rightarrow>   ('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_spec deleted_calls from_bool nestedSpec oper ctxt res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c op r. calls ctxt c \<triangleq> Call (NestedOp k op) r \<and> is_update op \<and>  c \<notin> deleted_calls ctxt k)
  | NestedOp k op \<Rightarrow>
     nestedSpec op (restrict_ctxt_op (nested_op_on_key k) 
          (ctxt_remove_calls (deleted_calls ctxt k) ctxt)) res
"

definition map_uw_spec :: "(bool \<Rightarrow> 'r) \<Rightarrow> ('v::crdt_op,'r::default) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_uw_spec \<equiv> map_spec deleted_calls_uw"

definition map_dw_spec :: "(bool \<Rightarrow> 'r) \<Rightarrow> ('v::crdt_op,'r::default) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
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
  shows "crdt_spec_wf (map_spec deleted_calls from_bool nested)"
  by (auto simp add: crdt_spec_wf_def map_spec_def  
      deleted_calls_wf calls_ctxt_remove_calls calls_restrict_ctxt_op restrict_map_def restrict_relation_def deleted_calls_uw_def 
      happensBefore_restrict_ctxt_op happensBefore_ctxt_remove_calls 
      intro!: ext 
      split: option.splits call.splits mapOp.splits if_splits
      elim!: use_crdt_spec_wf3[OF wf])

lemma map_uw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_uw_spec from_bool nested)"
  using wf unfolding map_uw_spec_def by (rule map_spec_wf, auto simp add: deleted_calls_uw_def intro!: ext, auto)

lemma map_dw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_dw_spec from_bool  nested)"
  using wf unfolding map_dw_spec_def by (rule map_spec_wf, auto simp add: deleted_calls_dw_def intro!: ext, auto)


subsection "Structs"

definition struct_field :: "(('i, 'r) operationContext \<Rightarrow> 'r \<Rightarrow> bool) \<Rightarrow> ('o \<Rightarrow> 'i option) \<Rightarrow> ('o, 'r) operationContext \<Rightarrow> 'r \<Rightarrow> bool"  where
"struct_field spec to_op   \<equiv> \<lambda>ctxt r. spec (restrict_ctxt_op to_op ctxt) r"


definition ctxt_map_result :: "('a \<Rightarrow> 'b) \<Rightarrow> ('o, 'a) operationContext \<Rightarrow> ('o, 'b) operationContext" where
"ctxt_map_result f ctxt  \<equiv> \<lparr>
    calls = (\<lambda>c. (case calls ctxt c of Some (Call op r) \<Rightarrow> Some (Call op (f r)) | _ \<Rightarrow> None)),
    happensBefore = happensBefore ctxt
 \<rparr>"

definition map_result :: "('b \<Rightarrow> 'a) \<Rightarrow> ('o, 'a) crdtSpec \<Rightarrow> ('o, 'b) crdtSpec" where
"map_result f spec \<equiv> \<lambda>op ctxt r. spec op (ctxt_map_result f ctxt) (f r)" 


subsection "Queries cannot guess Ids"

lemmas use_queries_cannot_guess_ids = queries_cannot_guess_ids_def2[THEN iffD1, rule_format]

lemma map_spec_queries_cannot_guess_ids[intro]:
  assumes nested: "queries_cannot_guess_ids n"
    and bools_no_uids[simp]: "\<And>b. uniqueIds (from_bool b) = {}"
  shows"queries_cannot_guess_ids (map_spec r from_bool n) "
proof (auto simp add: queries_cannot_guess_ids_def2 map_spec_def  split: mapOp.splits)
  fix ctxt res key op x
  assume a0: "n op (restrict_ctxt_op (nested_op_on_key key) (ctxt_remove_calls (r ctxt key) ctxt)) res"
    and a1: "x \<in> uniqueIds res"
    and a2: "x \<notin> uniqueIds key"
and a3: "x \<notin> uniqueIds op"



  obtain cId opr res
    where cId1: "calls (restrict_ctxt_op (nested_op_on_key key) (ctxt_remove_calls (r ctxt key) ctxt)) cId \<triangleq> Call opr res"
      and cId2: "x \<in> uniqueIds opr"
    using use_queries_cannot_guess_ids[OF nested a0 a1 a3] by blast


  from this
  show "\<exists>cId opr. (\<exists>res. calls ctxt cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr"
  proof (intro exI conjI)
    from cId1
    show  "calls ctxt cId \<triangleq> Call (NestedOp key opr) res"
      by (auto simp add: calls_restrict_ctxt_op calls_ctxt_remove_calls restrict_map_def nested_op_on_key_def split: option.splits call.splits if_splits mapOp.splits)

    from `x \<in> uniqueIds opr`
    show "x \<in> uniqueIds (NestedOp key opr)"
      by (simp add: uniqueIds_mapOp_def)
  qed
qed


lemma map_uw_spec_queries_cannot_guess_ids[intro]:
  assumes nested: "queries_cannot_guess_ids n"
    and bools_no_uids[simp]: "\<And>b. uniqueIds (from_bool b) = {}"
  shows"queries_cannot_guess_ids (map_uw_spec from_bool n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_uw_spec_def nested)

lemma map_dw_spec_queries_cannot_guess_ids[intro]:
  assumes nested: "queries_cannot_guess_ids n"
    and bools_no_uids[simp]: "\<And>b. uniqueIds (from_bool b) = {}"
  shows"queries_cannot_guess_ids (map_dw_spec from_bool n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_dw_spec_def nested)


lemma register_spec_queries_cannot_guess_ids[intro]:
  assumes i_no: "uniqueIds i = {}"
  shows "queries_cannot_guess_ids (register_spec i)"
  apply (auto simp add: queries_cannot_guess_ids_def2 register_spec_def latestValues_def i_no
      latestAssignments_def ran_def uniqueIds_registerOp_def split: registerOp.splits option.splits if_splits)
  apply (auto split: call.splits if_splits registerOp.splits)
  by (metis call.sel(1) registerOp.distinct(1) registerOp.inject)


lemma query_cannot_guess_ids_struct_field:
  assumes a1: "query_cannot_guess_ids uids spec"
    and a2: "\<And>op op'. f op \<triangleq> op' \<Longrightarrow> uniqueIds op' \<subseteq> uniqueIds op"
  shows "query_cannot_guess_ids uids (struct_field spec f)"
  using a1 proof (auto simp add: query_cannot_guess_ids_def2)
  fix ctxt res x
  assume a0: "\<forall>ctxt res.            spec ctxt res \<longrightarrow> (\<forall>x. x \<in> uniqueIds res \<longrightarrow> x \<notin> uids \<longrightarrow> (\<exists>cId opr. (\<exists>res. calls ctxt cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr))"
    and a1: "struct_field spec f ctxt res"
    and a2: "x \<in> uniqueIds res"
    and a3: "x \<notin> uids"

  from a1 have "spec (restrict_ctxt_op f ctxt) res"
    by (auto simp add: struct_field_def)

  from a0[rule_format, OF this a2 a3]
  have " \<exists>cId opr. (\<exists>res. calls (restrict_ctxt_op f ctxt) cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr"
    by simp

  from this obtain cId opr res' 
    where "calls (restrict_ctxt_op f ctxt) cId \<triangleq> Call opr res'"
      and "x \<in> uniqueIds opr"
    by blast

  from this obtain opr'
    where "calls ctxt cId \<triangleq> Call opr' res'"
      and "f opr' \<triangleq> opr"
    by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def split: option.splits call.splits)

  have "x \<in> uniqueIds opr'"
    using \<open>f opr' \<triangleq> opr\<close> \<open>x \<in> uniqueIds opr\<close> assms(2) by blast


  show "\<exists>cId opr. (\<exists>res. calls ctxt cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr"
    using \<open>calls ctxt cId \<triangleq> Call opr' res'\<close> \<open>x \<in> uniqueIds opr'\<close> by blast
qed

lemma query_cannot_guess_ids_struct_field2[intro]:
  assumes a1: "queries_cannot_guess_ids spec"
    and a2: "\<And>op op'. f op \<triangleq> op' \<Longrightarrow> uniqueIds op' \<subseteq> uniqueIds op"
  shows "query_cannot_guess_ids (uniqueIds op) (struct_field (spec op) f)"
  using a1 a2 queries_cannot_guess_ids_def query_cannot_guess_ids_struct_field by blast




end