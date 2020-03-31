section "Composable CRDT specifications"
theory crdt_specs
  imports repliss_sem
 unique_ids
 "HOL-Library.Monad_Syntax"
begin


text "In this section we define the semantics of several conflict-free replicated data types (CRDTs)."

type_synonym ('op, 'res) crdtSpec = "'op \<Rightarrow> ('op, 'res) operationContext \<Rightarrow> 'res \<Rightarrow> bool"

text "Some helper functions for defining the specs:"

definition map_map_values :: "('x \<Rightarrow> 'y) \<Rightarrow> ('k \<rightharpoonup> 'x) \<Rightarrow> ('k \<rightharpoonup> 'y)" where
"map_map_values f m \<equiv> \<lambda>x. case m x of Some a \<Rightarrow> Some (f a) | None \<Rightarrow> None"



definition fmap_map_values :: "('x \<rightharpoonup> 'y) \<Rightarrow> ('k \<rightharpoonup> 'x) \<Rightarrow> ('k \<rightharpoonup> 'y)" where
"fmap_map_values f m \<equiv> \<lambda>x. m x \<bind> f"

lemma fmap_map_values_def':
"fmap_map_values f m = (\<lambda>x. case m x of Some a \<Rightarrow> f a | None \<Rightarrow> None)"
  by (auto simp add: fmap_map_values_def split: option.splits)


lemma fmap_map_values_eq_some:
"(fmap_map_values f g x \<triangleq> y) \<longleftrightarrow> (\<exists>a. g x \<triangleq> a \<and> f a \<triangleq> y) "
  by (auto simp add: fmap_map_values_def' split: option.splits)

definition 
"map_ctxt f c \<equiv> c\<lparr>calls := map_map_values f (calls c)\<rparr>"

definition restrict_hb :: "('op, 'res) operationContext \<Rightarrow> ('op, 'res) operationContext" where
"restrict_hb ctxt \<equiv> ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>"

lemma calls_restrict_hb[simp]: "calls (restrict_hb c) = calls c"
  by (simp add: restrict_hb_def) 

lemma happensBefore_restrict_hb[simp]: "happensBefore (restrict_hb c) = happensBefore c |r dom (calls c)"
  by (simp add: restrict_hb_def) 

definition 
"restrict_ctxt f ctxt \<equiv> restrict_hb \<lparr>calls = fmap_map_values f (calls ctxt), happensBefore = happensBefore ctxt\<rparr>"


definition 
"map_Call f c \<equiv> case c of Call op r \<Rightarrow> (case f op of None \<Rightarrow> None | Some op' \<Rightarrow> Some (Call op' r))"

definition restrict_ctxt_op :: "('op1 \<rightharpoonup> 'op2) \<Rightarrow>   ('op1, 'r) operationContext \<Rightarrow>   ('op2, 'r) operationContext" where
"restrict_ctxt_op f \<equiv> 
  restrict_ctxt (\<lambda>c. 
    case c of Call op r \<Rightarrow> (case f op of Some op' \<Rightarrow> Some (Call op' r) | None \<Rightarrow> None))
"


lemma calls_restrict_ctxt_op1:
"calls (restrict_ctxt_op f ctxt) c = (case calls ctxt c of None \<Rightarrow> None | Some call \<Rightarrow> map_Call f call)"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def map_Call_def intro!: ext split: option.splits call.splits)


definition ctxt_restrict_calls :: "callId set \<Rightarrow> ('op, 'r) operationContext \<Rightarrow> ('op, 'r) operationContext"  where
"ctxt_restrict_calls Cs ctxt = \<lparr>calls = calls ctxt |` Cs, happensBefore = happensBefore ctxt |r Cs\<rparr>"


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
   \<forall>op c r. spec op (restrict_hb c) r = spec op c r"

lemma use_crdt_spec_wf:
  assumes "crdt_spec_wf spec"
  shows "spec op (restrict_hb c) = spec op c"
  using assms  by (auto simp add: crdt_spec_wf_def)


subsection "Counter"

datatype counterOp =
    Increment int
    | GetCount

instance counterOp :: countable
  by countable_datatype
instantiation counterOp :: crdt_op begin
definition "is_update_counterOp op \<equiv> op \<noteq> GetCount"
definition "uniqueIds_counterOp (op::counterOp) \<equiv> {}::uniqueId set"
definition "default_counterOp \<equiv> GetCount"
instance by standard (auto simp add: uniqueIds_counterOp_def)
end



definition 
"increments op \<equiv> case op of Increment i \<Rightarrow> i | _ \<Rightarrow> 0"

class from_int = valueType +
  fixes from_int :: "int \<Rightarrow> 'a"
  assumes from_int_no_uniqueIds: "uniqueIds (from_int x) = {}"


definition counter_spec :: "(counterOp, 'a::{default,from_int}) crdtSpec" where
"counter_spec oper ctxt res \<equiv> 
  case oper of
    Increment i \<Rightarrow> res = default
  | GetCount \<Rightarrow> res = from_int (\<Sum>(_,c)\<leftarrow>\<^sub>m calls ctxt. increments (call_operation c))"



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
"latestAssignments_h c_calls s_happensBefore \<equiv> 
   \<lambda>c. case c_calls c of 
    Some (Call (Assign v) r) \<Rightarrow> 
        if \<exists>c' v' r'. c_calls c' \<triangleq> Call (Assign v') r' \<and> (c,c')\<in>s_happensBefore then None else Some v
  | _ \<Rightarrow> None"

definition latestAssignments :: "('a registerOp, 'r) operationContext \<Rightarrow> callId \<rightharpoonup> 'a"  where
"latestAssignments ctxt \<equiv> latestAssignments_h (calls ctxt) (happensBefore ctxt)"


lemma ctxt_spec_wf_latestAssignments[simp]:
"latestAssignments (restrict_hb c) = latestAssignments c"
  by (auto simp add: restrict_hb_def latestAssignments_h_def
      restrict_relation_def latestAssignments_def
      intro!: ext 
      split: option.splits if_splits registerOp.splits call.splits,
      blast+)



definition 
"latestValues ctxt \<equiv> Map.ran (latestAssignments ctxt)" 

lemma latestValues_def2:
"latestValues ctxt =
  {v | c v r . calls ctxt c \<triangleq> Call (Assign v) r  
        \<and> (\<nexists>c' v' r'. calls ctxt c' \<triangleq> Call (Assign v') r' \<and> (c,c')\<in>happensBefore ctxt)}" 
proof (auto simp add: latestValues_def latestAssignments_def latestAssignments_h_def image_def ran_def 
    split: option.splits call.splits if_splits, fuzzy_goal_cases G)
  case (G x a y)
  then show ?case
    by (cases y; cases "call_operation y", auto split: if_splits)
qed


lemma ctxt_spec_wf_latestValues[simp]:
"latestValues (restrict_hb c) = latestValues c"
  by (auto simp add: latestValues_def)



definition register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> if latestValues ctxt = {} then res = initial else res \<in> latestValues ctxt "


lemma latest_assignments_wf:
"latestAssignments_h c_calls (Restr c_happensBefore (dom c_calls))
= latestAssignments_h c_calls c_happensBefore"
  by (auto simp add: latestAssignments_h_def intro!: ext split: call.splits option.splits registerOp.splits, auto)

lemma latest_assignments_wf2[simp]:
  assumes "c_calls \<subseteq>\<^sub>m calls c"
  shows "latestAssignments_h c_calls (happensBefore (restrict_hb c))
= latestAssignments_h c_calls (happensBefore c)"
  using assms  by (auto simp add: map_le_def latestAssignments_h_def restrict_hb_def restrict_relation_def intro!: ext split: call.splits option.splits registerOp.splits,
 (metis domI)+)


lemma register_spec_restrict_hb[simp]:
"register_spec i op (restrict_hb c) r 
 \<longleftrightarrow> register_spec i op c r"
  by (auto simp add: register_spec_def split: registerOp.splits)

lemma register_spec_wf: "crdt_spec_wf (register_spec i)"
  by (auto simp add: crdt_spec_wf_def )


text "To define LWW-registers, we use some arbitrary order on calls.
First we show that this exists:"



definition lww_register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"lww_register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> res = firstValue initial (latestAssignments ctxt)"

lemma lwwregister_restrict_hb[simp]: 
"lww_register_spec i op (restrict_hb c) r
\<longleftrightarrow> lww_register_spec i op c r"
  by (auto simp add: lww_register_spec_def split: registerOp.splits )

lemma lwwregister_spec_wf: "crdt_spec_wf (lww_register_spec i)"
  by (simp add: crdt_spec_wf_def) 



subsection "Multi-Value Register"

class is_set =
  fixes is_set :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"

definition mv_register_spec :: "('a registerOp, 'a::{default,is_set}) crdtSpec" where
"mv_register_spec oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> is_set res (latestValues ctxt)"


lemma mv_register_spec_restrict_hb[simp]: 
"mv_register_spec op (restrict_hb c) r
= mv_register_spec op c r"
  by (auto simp add: mv_register_spec_def split: registerOp.splits)


lemma mv_register_spec_wf: "crdt_spec_wf mv_register_spec"
  by (simp add: crdt_spec_wf_def)

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

class from_bool = valueType +
  fixes from_bool :: "bool \<Rightarrow> 'a"
  assumes from_bool_no_uniqueIds: "uniqueIds (from_bool x) = {}"

instantiation bool :: from_bool begin
  definition from_bool_bool :: "bool\<Rightarrow>bool" where [simp]: "from_bool_bool = id"
instance
  by standard auto
end


definition set_aw_spec :: "('v setOp, 'r::{default,from_bool}) crdtSpec" where
"set_aw_spec op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a. calls ctxt a \<triangleq> Call (Add v) default 
                           \<and> (\<nexists>r. calls ctxt r \<triangleq> Call (Remove v) default \<and> (a,r)\<in>happensBefore ctxt))"



definition set_rw_spec :: "('v setOp, 'r::{default,from_bool}) crdtSpec" where
"set_rw_spec op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a a_res. calls ctxt a \<triangleq> Call (Add v) a_res 
                           \<and> (\<forall>r r_res. calls ctxt r \<triangleq> Call (Remove v) r_res 
                               \<longrightarrow> (\<exists>a' a'_res. calls ctxt a' \<triangleq> Call (Add v) a'_res \<and> (r,a')\<in>happensBefore ctxt)))"



text "Alternative definition: 
The following definition is closer to the @{term set_aw_spec} in the structure of the formula.
However, the semantic is strange in the sense that an add-operation does not overwrite the removes that came before it." 
definition set_rw_spec2 :: "('v setOp, 'r::{default,from_bool}) crdtSpec" where
"set_rw_spec2 op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool (\<exists>a. calls ctxt a \<triangleq> Call (Add v) default 
                           \<and> (\<nexists>r. calls ctxt r \<triangleq> Call (Remove v) default \<and> (r,a)\<notin>happensBefore ctxt))"


lemma set_aw_spec_cannot_guess_ids[simp,intro]:
  assumes "\<And>x. uniqueIds (from_bool x) = {}"
  shows "queries_cannot_guess_ids set_aw_spec"
  by (auto simp add: queries_cannot_guess_ids_def query_cannot_guess_ids_def set_aw_spec_def assms from_bool_no_uniqueIds split: setOp.splits)



lemma set_rw_spec_cannot_guess_ids[simp,intro]:
  assumes "\<And>x. uniqueIds (from_bool x) = {}"
  shows "queries_cannot_guess_ids set_rw_spec"
  by (auto simp add: queries_cannot_guess_ids_def query_cannot_guess_ids_def set_rw_spec_def assms from_bool_no_uniqueIds split: setOp.splits)


lemma set_aw_spec_restrict_hb[simp]:
"set_aw_spec op (restrict_hb c) r 
\<longleftrightarrow> set_aw_spec op c r"
  apply (auto simp add: set_aw_spec_def restrict_hb_def restrict_relation_def split: setOp.splits)
  apply (metis (no_types, lifting)  domI  )+
  done

lemma set_rw_spec_restrict_hb[simp]:
"set_rw_spec op (restrict_hb c) r 
\<longleftrightarrow> set_rw_spec op c r"
  apply (auto simp add: set_rw_spec_def restrict_hb_def restrict_relation_def split: setOp.splits)
  apply (metis (no_types, lifting)  domI  )+
  done

subsection "Flags"

datatype flagOp = Enable | Disable | ReadFlag

instance flagOp :: countable
  by countable_datatype
instantiation flagOp :: crdt_op begin
definition [simp]: "is_update_flagOp op \<equiv> op \<noteq> ReadFlag"
definition "uniqueIds_flagOp (op::flagOp) \<equiv> {}::uniqueId set"
definition "default_flagOp \<equiv> ReadFlag"
instance by standard (auto simp add: uniqueIds_flagOp_def)
end



definition 
"latestOps ctxt \<equiv> 
  {call_operation c | cId c. 
            calls ctxt cId \<triangleq> c 
          \<and> is_update (call_operation c)
          \<and> (\<nexists>cId' c'. calls ctxt cId' \<triangleq> c'
                      \<and> is_update (call_operation c')
                      \<and> (cId, cId')\<in>happensBefore ctxt)}"

definition flag_dw_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_dw_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool (Enable \<in> latestOps ctxt \<and> Disable \<notin> latestOps ctxt)
  | _ \<Rightarrow> res = default"



definition flag_ew_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_ew_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool (Enable \<in> latestOps ctxt)
  | _ \<Rightarrow> res = default"


text "Strong variants:"

definition flag_sdw_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_sdw_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool (\<exists>e. calls ctxt e \<triangleq> Call Enable default
                  \<and> (\<forall>d. calls ctxt d \<triangleq> Call Disable default \<longrightarrow> (d,e)\<in>happensBefore ctxt))
  | _ \<Rightarrow> res = default"

definition flag_sew_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_sew_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool ((\<exists>e. calls ctxt e \<triangleq> Call Enable default)
                  \<and> (\<nexists>d. calls ctxt d \<triangleq> Call Disable default
                    \<and> (\<forall>e. calls ctxt e \<triangleq> Call Enable default \<longrightarrow> (e,d)\<in>happensBefore ctxt)))
  | _ \<Rightarrow> res = default"

text "Next we validate the specification on some examples"


context begin

abbreviation "enable \<equiv> Call Enable default"
abbreviation "disable \<equiv> Call Disable default"

abbreviation "c1 \<equiv> CallId 1"
abbreviation "c2 \<equiv> CallId 2"
abbreviation "c3 \<equiv> CallId 3"
abbreviation "c4 \<equiv> CallId 4"

definition "example1 \<equiv> \<lparr>
  calls = Map.empty,
  happensBefore = {}
\<rparr>"

definition "example2 \<equiv> \<lparr>
  calls = [
    c1 \<mapsto> enable,
    c2 \<mapsto> disable
  ],
  happensBefore = {}
\<rparr>"

definition "example3 \<equiv> \<lparr>
  calls = [
    c1 \<mapsto> disable,
    c2 \<mapsto> disable,
    c3 \<mapsto> enable,
    c4 \<mapsto> enable
  ],
  happensBefore = {(c1,c3), (c2,c4)}
\<rparr>"


definition "example4 \<equiv> \<lparr>
  calls = [
    c1 \<mapsto> enable,
    c2 \<mapsto> enable,
    c3 \<mapsto> disable,
    c4 \<mapsto> disable
  ],
  happensBefore = {(c1,c3), (c2,c4)}
\<rparr>"



lemma "flag_ew_spec ReadFlag example1 False"
  by (auto simp add: flag_ew_spec_def latestOps_def example1_def)
lemma "flag_sew_spec ReadFlag example1 False"
  by (auto simp add: flag_sew_spec_def latestOps_def example1_def)
lemma "flag_dw_spec ReadFlag example1 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example1_def)
lemma "flag_sdw_spec ReadFlag example1 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example1_def)


lemma "flag_ew_spec ReadFlag example2 True"
  by (auto simp add: flag_ew_spec_def latestOps_def example2_def)
lemma "flag_sew_spec ReadFlag example2 True"
  by (auto simp add: flag_sew_spec_def latestOps_def example2_def)
lemma "flag_dw_spec ReadFlag example2 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example2_def cong: conj_cong)
lemma "flag_sdw_spec ReadFlag example2 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example2_def cong: conj_cong)


lemma "flag_ew_spec ReadFlag example3 True"
  apply (auto simp add: flag_ew_spec_def latestOps_def example3_def cong: conj_cong)
  by (smt callId.inject)
lemma "flag_sew_spec ReadFlag example3 True"
  apply (auto simp add: flag_sew_spec_def latestOps_def example3_def cong: conj_cong)
  by (smt callId.inject)
lemma "flag_dw_spec ReadFlag example3 True"
  apply (auto simp add: flag_dw_spec_def latestOps_def example3_def cong: conj_cong)
  by (smt callId.inject)
lemma "flag_sdw_spec ReadFlag example3 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example3_def cong: conj_cong)

lemma "flag_ew_spec ReadFlag example4 False"
  by (auto simp add: flag_ew_spec_def latestOps_def example4_def cong: conj_cong)
lemma "flag_sew_spec ReadFlag example4 True"
  by (auto simp add: flag_sew_spec_def latestOps_def example4_def cong: conj_cong)
lemma "flag_dw_spec ReadFlag example4 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example4_def cong: conj_cong)
lemma "flag_sdw_spec ReadFlag example4 False"
  apply (auto simp add: flag_sdw_spec_def latestOps_def example4_def cong: conj_cong)
  by (smt callId.inject)+




end


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


definition 
"sub_context C_in Cs ctxt \<equiv>
  (restrict_ctxt_op C_in (ctxt_restrict_calls Cs ctxt))"


definition map_spec :: "((('k, 'v::crdt_op) mapOp, 'r::{default,from_bool}) operationContext \<Rightarrow> 'k \<Rightarrow> callId set) \<Rightarrow>  ('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_spec deleted_calls nestedSpec oper ctxt res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c op r. calls ctxt c \<triangleq> Call (NestedOp k op) r \<and> is_update op \<and>  c \<notin> deleted_calls ctxt k)
  | NestedOp k op \<Rightarrow>
     nestedSpec op (sub_context (nested_op_on_key k) (- deleted_calls ctxt k) ctxt) res
"

definition map_uw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_uw_spec \<equiv> map_spec deleted_calls_uw"

definition map_dw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_dw_spec \<equiv> map_spec deleted_calls_dw"


lemma calls_ctxt_restrict_calls: "calls (ctxt_restrict_calls S ctxt) c = (calls ctxt |` S) c"
  by (auto simp add: ctxt_restrict_calls_def)

lemma calls_restrict_ctxt_op: "calls (restrict_ctxt_op f ctxt) c
  = (case calls ctxt c of None \<Rightarrow> None | Some (Call op r) \<Rightarrow> (case f op of None \<Rightarrow> None | Some op' \<Rightarrow> Some (Call op' r)))"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def')

lemma calls_restrict_ctxt_op2: "calls (restrict_ctxt_op f ctxt)
  = (\<lambda>c. calls ctxt c \<bind> (\<lambda>call. f (call_operation call) \<bind> (\<lambda>op'. Some (Call op' (call_res call)))))"
  by (auto simp add: calls_restrict_ctxt_op split: option.splits call.splits)


lemma happensBefore_restrict_ctxt_op:  "(c, c') \<in> happensBefore (restrict_ctxt_op f ctxt) \<longleftrightarrow> 
(\<exists>op r op' r'. (c, c') \<in> happensBefore ctxt 
  \<and> calls ctxt c \<triangleq> Call op r \<and> f op \<noteq> None 
  \<and> calls ctxt c' \<triangleq> Call op' r' \<and> f op' \<noteq> None)"
  apply (auto simp add: restrict_ctxt_op_def restrict_ctxt_def restrict_relation_def  fmap_map_values_eq_some split: call.splits option.splits)
    apply (meson call.exhaust option.exhaust)
  done

lemma happensBefore_ctxt_restrict_calls: "(c, c') \<in> happensBefore (ctxt_restrict_calls S ctxt) \<longleftrightarrow> (c, c') \<in> happensBefore ctxt |r S"
  by (auto simp add: ctxt_restrict_calls_def)

lemma restrict_simp1:
"(restrict_ctxt_op (nested_op_on_key x11)
           (ctxt_restrict_calls (deleted_calls_uw (restrict_hb c) x) (restrict_hb c)))
= (restrict_hb (restrict_ctxt_op (nested_op_on_key x11) (ctxt_restrict_calls (deleted_calls_uw c x) c)))"
  apply (auto simp add: fmap_map_values_def restrict_map_def restrict_relation_def restrict_ctxt_op_def
      restrict_hb_def restrict_ctxt_def ctxt_restrict_calls_def intro!: ext split: option.splits call.splits)
           apply (auto simp add:  deleted_calls_uw_def)
  done 

lemma map_spec_restrict_hb[simp]:
  assumes a1: "dc (restrict_hb c) = dc c"
    and  wf: "crdt_spec_wf nested"
  shows "map_spec dc nested op (restrict_hb c) r 
\<longleftrightarrow> map_spec dc nested op c r"
proof (auto simp add: map_spec_def a1 sub_context_def  split: mapOp.splits)

  have h1: "restrict_hb (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) c))
     = (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) (restrict_hb c)))" for x
    by (auto simp add:  fmap_map_values_def' restrict_map_def restrict_relation_def restrict_ctxt_op_def
      restrict_hb_def restrict_ctxt_def ctxt_restrict_calls_def intro!: ext split: option.splits call.splits)


  show "nested y (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) c)) r"
    if c0: "op = NestedOp x y"
      and c1: "nested y (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) (restrict_hb c))) r"
    for  x y
    by (metis c1 h1 local.wf use_crdt_spec_wf)


  have h2: "restrict_hb (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) c))
           =  (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) (restrict_hb c)))" for x
    by (auto simp add: fmap_map_values_def' restrict_map_def restrict_relation_def restrict_ctxt_op_def
      restrict_hb_def restrict_ctxt_def ctxt_restrict_calls_def intro!: ext split: option.splits call.splits)



  show "nested y (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) (restrict_hb c))) r"
    if c0: "op = NestedOp x y"
      and c1: "nested y (restrict_ctxt_op (nested_op_on_key x) (ctxt_restrict_calls (- dc c x) c)) r"
    for  x y
    by (metis c1 h2 local.wf use_crdt_spec_wf)
qed


lemma deleted_calls_uw_restrict_hb[simp]:
 "deleted_calls_uw (restrict_hb c) = deleted_calls_uw c"
  by (auto simp add: deleted_calls_uw_def restrict_relation_def intro!: ext, auto)


lemma deleted_calls_dw_restrict_hb[simp]:
 "deleted_calls_dw (restrict_hb c) = deleted_calls_dw c"
  by (auto simp add: deleted_calls_dw_def restrict_relation_def intro!: ext, auto)


lemma map_uw_spec_wf_restrict_hb[simp]:
  assumes wf: "crdt_spec_wf nested"
  shows
"map_uw_spec nested op (restrict_hb c) r
\<longleftrightarrow> map_uw_spec nested op c r"
  by (simp add: map_uw_spec_def wf)

lemma map_dw_spec_wf_restrict_hb[simp]:
  assumes wf: "crdt_spec_wf nested"
  shows
"map_dw_spec nested op (restrict_hb c) r
\<longleftrightarrow> map_dw_spec nested op c r"
  by (simp add: map_dw_spec_def wf)


lemma map_uw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_uw_spec nested)"
  using crdt_spec_wf_def local.wf map_uw_spec_wf_restrict_hb by blast

lemma map_dw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_dw_spec nested)"
  using crdt_spec_wf_def local.wf map_dw_spec_wf_restrict_hb by blast


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
  shows"queries_cannot_guess_ids (map_spec r n) "
proof (auto simp add: sub_context_def queries_cannot_guess_ids_def2 map_spec_def  split: mapOp.splits)
  fix ctxt res key op x
  assume a0: "n op (restrict_ctxt_op (nested_op_on_key key) (ctxt_restrict_calls (- r ctxt key) ctxt)) res"
    and a1: "x \<in> uniqueIds res"
    and a2: "x \<notin> uniqueIds key"
and a3: "x \<notin> uniqueIds op"



  obtain cId opr res
    where cId1: "calls (restrict_ctxt_op (nested_op_on_key key) (ctxt_restrict_calls (- r ctxt key) ctxt)) cId \<triangleq> Call opr res"
      and cId2: "x \<in> uniqueIds opr"
    using use_queries_cannot_guess_ids[OF nested a0 a1 a3] by blast


  from this
  show "\<exists>cId opr. (\<exists>res. calls ctxt cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr"
  proof (intro exI conjI)
    from cId1
    show  "calls ctxt cId \<triangleq> Call (NestedOp key opr) res"
      by (auto simp add: calls_restrict_ctxt_op calls_ctxt_restrict_calls restrict_map_def nested_op_on_key_def split: option.splits call.splits if_splits mapOp.splits)

    from `x \<in> uniqueIds opr`
    show "x \<in> uniqueIds (NestedOp key opr)"
      by (simp add: uniqueIds_mapOp_def)
  qed

next
  show "\<exists>cId opr. (\<exists>res. calls ctxt cId \<triangleq> Call opr res) \<and> x \<in> uniqueIds opr"
    if c0: "x \<in> uniqueIds (from_bool (\<exists>c op. (\<exists>r. calls ctxt c \<triangleq> Call (NestedOp x2 op) r) \<and> is_update op \<and> c \<notin> r ctxt x2))"
      and c1: "x \<notin> uniqueIds x2"
    for  ctxt x2 x
    using c0 from_bool_no_uniqueIds by fastforce


qed


lemma map_uw_spec_queries_cannot_guess_ids[intro]:
  assumes nested: "queries_cannot_guess_ids n"
  shows"queries_cannot_guess_ids (map_uw_spec n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_uw_spec_def nested)

lemma map_dw_spec_queries_cannot_guess_ids[intro]:
  assumes nested: "queries_cannot_guess_ids n"
  shows"queries_cannot_guess_ids (map_dw_spec n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_dw_spec_def nested)


lemma register_spec_queries_cannot_guess_ids[intro]:
  assumes i_no: "uniqueIds i = {}"
  shows "queries_cannot_guess_ids (register_spec i)"
  apply (auto simp add: latestAssignments_def queries_cannot_guess_ids_def2 register_spec_def latestValues_def i_no
      latestAssignments_h_def ran_def uniqueIds_registerOp_def split: registerOp.splits option.splits if_splits)
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
    by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def' split: option.splits call.splits)

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



subsection "Rewriting of Specs"


lemma crdt_spec_wf_restrict_ctxt:
  assumes "crdt_spec_wf spec"
  shows "spec op (restrict_ctxt f ctxt) = spec op (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>)"
proof 
  fix r

  have h: "spec op ctxt r 
     = spec op (ctxt\<lparr>happensBefore := happensBefore ctxt |r dom (calls ctxt)\<rparr>) r" for ctxt
    using assms use_crdt_spec_wf
    by (metis restrict_hb_def) 
    
  have a: "spec op (restrict_ctxt f ctxt) r 
   = spec op ((restrict_ctxt f ctxt)\<lparr>happensBefore := happensBefore (restrict_ctxt f ctxt) |r dom (calls (restrict_ctxt f ctxt))\<rparr>) r "
    by (subst h, rule refl)



  have b: "spec op (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>) r
    = spec op ((ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>)\<lparr>happensBefore := happensBefore  (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>) |r dom (calls  (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>))\<rparr>) r "
    by (subst h, rule refl)

  have c: "((restrict_ctxt f ctxt)\<lparr>happensBefore := happensBefore (restrict_ctxt f ctxt) |r dom (calls (restrict_ctxt f ctxt))\<rparr>)
       =   ((ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>)\<lparr>happensBefore := happensBefore  (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>) |r dom (calls  (ctxt\<lparr>calls := fmap_map_values f (calls ctxt) \<rparr>))\<rparr>)"
    by (auto simp add: restrict_ctxt_def restrict_relation_def fmap_map_values_def intro!: operationContext.equality split: option.splits)   

  show "spec op (restrict_ctxt f ctxt) r = spec op (ctxt\<lparr>calls := fmap_map_values f (calls ctxt)\<rparr>) r"
    by (simp add: a b c)
qed



end