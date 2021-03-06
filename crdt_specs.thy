section "Composable CRDT specifications"
theory crdt_specs
  imports repliss_sem
 unique_ids
 "HOL-Library.Monad_Syntax"
begin


text "In this section we define the semantics of several conflict-free replicated data types (CRDTs)."

text_raw \<open>\DefineSnippet{crdtSpec}{\<close>
type_synonym ('op, 'res) crdtSpec = "'op \<Rightarrow> ('op, 'res) operationContext \<Rightarrow> 'res \<Rightarrow> bool"
text_raw \<open>}%EndSnippet\<close>


text "An operation context is well-formed if the happens-before relation is transitive and inversely well-founded."

definition 
"operationContext_wf ctxt \<equiv>
     trans (happensBefore ctxt)
   \<and> irrefl (happensBefore ctxt)
   \<and> Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)
   \<and> finite (dom (calls ctxt))"


lemma operationContext_wf_trans: "operationContext_wf ctxt \<Longrightarrow> trans (happensBefore ctxt)"
  unfolding operationContext_wf_def by auto

lemma operationContext_wf_irrefl: "operationContext_wf ctxt \<Longrightarrow> irrefl (happensBefore ctxt)"
  unfolding operationContext_wf_def by auto

lemma operationContext_wf_hb_field: "operationContext_wf ctxt \<Longrightarrow> Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  unfolding operationContext_wf_def by auto

lemma operationContext_wf_finite: "operationContext_wf ctxt \<Longrightarrow> finite (dom (calls ctxt))"
  unfolding operationContext_wf_def by auto

lemma operationContext_wf_finite_hb: 
  assumes "operationContext_wf ctxt"
  shows "finite (happensBefore ctxt)"
proof (rule finite_subset)
  show "happensBefore ctxt \<subseteq> dom (calls ctxt) \<times> dom (calls ctxt)"
    using operationContext_wf_hb_field[OF assms] 
    by (auto simp add: Field_def)
  show "finite (dom (calls ctxt) \<times> dom (calls ctxt))"
    using operationContext_wf_finite[OF assms] by auto
qed

lemma operationContext_wf_wf: 
  assumes "operationContext_wf ctxt"
  shows "wf ((happensBefore ctxt)\<inverse>)"
  by (simp add: assms operationContext_wf_finite_hb operationContext_wf_irrefl operationContext_wf_trans wf_converse)

lemma operationContext_wf_exists_max:
  assumes wf: "operationContext_wf ctxt"
    and "P x"
  shows "\<exists>x'. P x' \<and> (x = x' \<or> (x,x')\<in>happensBefore ctxt)  \<and> (\<forall>y. P y \<longrightarrow> (x',y)\<notin>happensBefore ctxt)"
  using assms by (simp add:  exists_max_wf' operationContext_wf_trans operationContext_wf_wf)


text "Some helper functions for defining the specs:"

definition "cOp c_calls c \<equiv> map_option call_operation (c_calls c)"

abbreviation "Op ctxt \<equiv> cOp (calls ctxt)"

definition "Res ctxt c \<equiv> map_option call_res (calls ctxt c)"


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

text_raw \<open>\DefineSnippet{sub_contexts}{\<close>
definition restrict_ctxt_op :: "('op1 \<rightharpoonup> 'op2) \<Rightarrow>   ('op1, 'r) operationContext \<Rightarrow>   ('op2, 'r) operationContext" where
"restrict_ctxt_op f \<equiv> 
  restrict_ctxt (\<lambda>c. 
    map_option (\<lambda>op'. Call op' (call_res c)) (f (call_operation c)))"

definition ctxt_restrict_calls :: "callId set \<Rightarrow> ('op, 'r) operationContext \<Rightarrow> ('op, 'r) operationContext"  where
"ctxt_restrict_calls Cs ctxt = \<lparr>
    calls = calls ctxt |` Cs, 
    happensBefore = happensBefore ctxt |r Cs\<rparr>"

definition sub_context :: "('c \<Rightarrow> 'a option) \<Rightarrow> callId set \<Rightarrow> ('c, 'b) operationContext \<Rightarrow> ('a, 'b) operationContext" where
"sub_context C_in Cs ctxt \<equiv>
  (restrict_ctxt_op C_in (ctxt_restrict_calls Cs ctxt))"
text_raw \<open>}%EndSnippet\<close>


lemma calls_restrict_ctxt_op1:
"calls (restrict_ctxt_op f ctxt) c = (case calls ctxt c of None \<Rightarrow> None | Some call \<Rightarrow> map_Call f call)"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def map_Call_def intro!: ext split: option.splits call.splits)


lemma Op_restrict_ctxt_op: 
"Op (restrict_ctxt_op f ctxt) = (\<lambda>c. Op ctxt c \<bind> f)"
  by (auto simp add: cOp_def option_bind_def restrict_ctxt_op_def restrict_ctxt_def  fmap_map_values_def
      intro!: ext split: option.splits call.splits)
   (metis (no_types, lifting) call.sel(1) option.exhaust_sel option.simps(8) option.simps(9))


lemma Op_restrict_ctxt_op_eq: 
"Op (restrict_ctxt_op f ctxt) c \<triangleq> X \<longleftrightarrow> (\<exists>Y. Op ctxt c \<triangleq> Y \<and> f Y \<triangleq> X)"
  by (auto simp add: Op_restrict_ctxt_op option_bind_def split: option.splits)


lemma happensBefore_restrict_ctxt_op:
"(x,y) \<in> happensBefore (restrict_ctxt_op f ctxt)
\<longleftrightarrow> (x,y)\<in>happensBefore ctxt 
      \<and> (\<exists>op. (Op ctxt x \<bind> f) \<triangleq> op)
      \<and> (\<exists>op. (Op ctxt y \<bind> f) \<triangleq> op)"
  by (auto simp add: restrict_ctxt_op_def cOp_def restrict_ctxt_def fmap_map_values_def
      restrict_relation_def option_bind_def
      split: option.splits call.splits)

lemma happensBefore_restrict_ctxt_op':
"(x,y) \<in> happensBefore (restrict_ctxt_op f ctxt)
\<longleftrightarrow> (x,y)\<in>happensBefore ctxt 
      \<and> (\<exists>op. Op ctxt x \<triangleq> op \<and> f op \<noteq> None)
      \<and> (\<exists>op. Op ctxt y \<triangleq> op \<and> f op \<noteq> None)"
  by (auto simp add: happensBefore_restrict_ctxt_op option_bind_def split: option.splits)




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

text_raw \<open>\DefineSnippet{counterOp}{\<close>
datatype counterOp =
      Increment int
    | GetCount
text_raw \<open>}%EndSnippet\<close>


instance counterOp :: countable
  by countable_datatype
instantiation counterOp :: crdt_op begin
definition "is_update_counterOp op \<equiv> op \<noteq> GetCount"
definition "uniqueIds_counterOp (op::counterOp) \<equiv> {}::uniqueId set"
definition "default_counterOp \<equiv> GetCount"
instance by standard (auto simp add: uniqueIds_counterOp_def)
end





class from_int = valueType +
  fixes from_int :: "int \<Rightarrow> 'a"
  assumes from_int_no_uniqueIds: "uniqueIds (from_int x) = {}"

text_raw \<open>\DefineSnippet{counter_spec}{\<close>
definition 
"increments op \<equiv> case op of Increment i \<Rightarrow> i | _ \<Rightarrow> 0"

definition counter_spec :: "(counterOp, 'a::{default,from_int}) crdtSpec" where
"counter_spec oper ctxt res \<equiv> 
  case oper of
    Increment i \<Rightarrow> res = default
  | GetCount \<Rightarrow> res = from_int (\<Sum>(_,c)\<leftarrow>\<^sub>m calls ctxt. increments (call_operation c))"
text_raw \<open>}%EndSnippet\<close>



subsection "Register"

text_raw \<open>\DefineSnippet{registerOp}{\<close>
datatype 'a registerOp =
    Assign 'a
  | Read
text_raw \<open>}%EndSnippet\<close>


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

text_raw \<open>\DefineSnippet{register_spec}{\<close>
definition 
"latestAssignments_h c_ops s_happensBefore \<equiv> 
   \<lambda>c. case c_ops c of 
    Some (Assign v) \<Rightarrow> 
        if \<exists>c' v'. c_ops c' \<triangleq> Assign v' \<and> (c,c')\<in>s_happensBefore then None else Some v
  | _ \<Rightarrow> None"

definition latestAssignments :: "('a registerOp, 'r) operationContext \<Rightarrow> callId \<rightharpoonup> 'a"  where
"latestAssignments ctxt \<equiv> latestAssignments_h (Op ctxt) (happensBefore ctxt)"

definition 
"latestValues ctxt \<equiv> Map.ran (latestAssignments ctxt)" 

definition register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> if latestValues ctxt = {} then res = initial else res \<in> latestValues ctxt "

definition lww_register_spec :: "'a::default \<Rightarrow> ('a registerOp, 'a) crdtSpec" where
"lww_register_spec initial oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
| Read \<Rightarrow> res = firstValue initial (latestAssignments ctxt)"
text_raw \<open>}%EndSnippet\<close>


lemma ctxt_spec_wf_latestAssignments[simp]:
"latestAssignments (restrict_hb c) = latestAssignments c"
  by (auto simp add: restrict_hb_def latestAssignments_h_def
      restrict_relation_def latestAssignments_def cOp_def
      intro!: ext 
      split: option.splits if_splits registerOp.splits call.splits,
      blast+)





lemma latestValues_def2:
"latestValues ctxt =
  {v | c v. Op ctxt c \<triangleq> Assign v  
        \<and> (\<nexists>c' v'. Op ctxt c' \<triangleq> Assign v' \<and> (c,c')\<in>happensBefore ctxt)}" 
proof (auto simp add: latestValues_def latestAssignments_def latestAssignments_h_def image_def ran_def 
    split: option.splits call.splits if_splits, fuzzy_goal_cases G)
  case (G x a y)
  then show ?case
    by (auto simp add: cOp_def split: option.splits registerOp.splits if_splits)
qed


lemma ctxt_spec_wf_latestValues[simp]:
"latestValues (restrict_hb c) = latestValues c"
  by (auto simp add: latestValues_def)





lemma latest_assignments_wf:
"latestAssignments_h c_calls (Restr c_happensBefore (dom c_calls))
= latestAssignments_h c_calls c_happensBefore"
  by (auto simp add: latestAssignments_h_def intro!: ext split: call.splits option.splits registerOp.splits, auto)



lemma latest_assignments_wf2[simp]:
  assumes "c_calls \<subseteq>\<^sub>m Op c"
  shows "latestAssignments_h c_calls (happensBefore (restrict_hb c))
= latestAssignments_h c_calls (happensBefore c)"
  using assms  by (auto simp add: cOp_def  map_option_case map_le_def latestAssignments_h_def restrict_hb_def restrict_relation_def intro!: ext split: call.splits option.splits registerOp.splits,
      auto,
      meson domExists_simp domIff)


lemma register_spec_restrict_hb[simp]:
"register_spec i op (restrict_hb c) r 
 \<longleftrightarrow> register_spec i op c r"
  by (auto simp add: register_spec_def split: registerOp.splits)

lemma register_spec_wf: "crdt_spec_wf (register_spec i)"
  by (auto simp add: crdt_spec_wf_def )


lemma lwwregister_restrict_hb[simp]: 
"lww_register_spec i op (restrict_hb c) r
\<longleftrightarrow> lww_register_spec i op c r"
  by (auto simp add: lww_register_spec_def split: registerOp.splits )

lemma lwwregister_spec_wf: "crdt_spec_wf (lww_register_spec i)"
  by (simp add: crdt_spec_wf_def) 



subsection "Multi-Value Register"

class is_set =
  fixes is_set :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"

text_raw \<open>\DefineSnippet{mv_register_spec}{\<close>
definition mv_register_spec :: "('a registerOp, 'a::{default,is_set}) crdtSpec" where
"mv_register_spec oper ctxt res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
| Read \<Rightarrow> is_set res (latestValues ctxt)"
text_raw \<open>}%EndSnippet\<close>



lemma mv_register_spec_restrict_hb[simp]: 
"mv_register_spec op (restrict_hb c) r
= mv_register_spec op c r"
  by (auto simp add: mv_register_spec_def split: registerOp.splits)


lemma mv_register_spec_wf: "crdt_spec_wf mv_register_spec"
  by (simp add: crdt_spec_wf_def)

subsection "Flags"

text_raw \<open>\DefineSnippet{flagOp}{\<close>
datatype flagOp = Enable | Disable | ReadFlag
text_raw \<open>}%EndSnippet\<close>


instance flagOp :: countable
  by countable_datatype
instantiation flagOp :: crdt_op begin
definition [simp]: "is_update_flagOp op \<equiv> op \<noteq> ReadFlag"
definition "uniqueIds_flagOp (op::flagOp) \<equiv> {}::uniqueId set"
definition "default_flagOp \<equiv> ReadFlag"
instance by standard (auto simp add: uniqueIds_flagOp_def)
end

class from_bool = valueType +
  fixes from_bool :: "bool \<Rightarrow> 'a"
  assumes from_bool_no_uniqueIds[simp]: "uniqueIds (from_bool x) = {}"
    and from_bool_inj: "(from_bool x = from_bool y) \<longleftrightarrow> x = y"

instantiation bool :: from_bool begin
  definition from_bool_bool :: "bool\<Rightarrow>bool" where [simp]: "from_bool_bool = id"
instance
  by standard auto
end



text_raw \<open>\DefineSnippet{flag_specs}{\<close>
definition 
"latestOps ctxt \<equiv> 
  {op | c op. 
            Op ctxt c \<triangleq> op
          \<and> is_update op
          \<and> (\<nexists>c' op'. Op ctxt c' \<triangleq> op'
                      \<and> is_update op'
                      \<and> (c, c')\<in>happensBefore ctxt)}"

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

definition flag_sdw_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_sdw_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool (\<exists>e. Op ctxt e \<triangleq> Enable
                  \<and> (\<forall>d. Op ctxt d \<triangleq> Disable \<longrightarrow> (d,e)\<in>happensBefore ctxt))
  | _ \<Rightarrow> res = default"

definition flag_sew_spec :: "(flagOp, 'a::{default,from_bool}) crdtSpec" where
"flag_sew_spec oper ctxt res \<equiv> 
  case oper of
   ReadFlag \<Rightarrow> res = from_bool ((\<exists>e. Op ctxt e \<triangleq> Enable)
                  \<and> (\<nexists>d. Op ctxt d \<triangleq> Disable
                    \<and> (\<forall>e. Op ctxt e \<triangleq> Enable \<longrightarrow> (e,d)\<in>happensBefore ctxt)))
  | _ \<Rightarrow> res = default"
text_raw \<open>}%EndSnippet\<close>


text "Now we prove alternative specifications for the flags:"




lemma latestOps_alt:
  assumes wf: "operationContext_wf ctxt"
  shows "x \<in> latestOps ctxt \<longleftrightarrow> is_update x \<and>
  (\<exists>c. Op ctxt c \<triangleq> x \<and> (\<forall>c' x'. Op ctxt c' \<triangleq> x' \<longrightarrow> is_update x' \<longrightarrow> (c, c')\<in>happensBefore ctxt \<longrightarrow> x' = x))"
proof safe
  fix x
  assume "x \<in> latestOps ctxt"
  show "is_update x"
    using \<open>x \<in> latestOps ctxt\<close> latestOps_def by blast

  from `x \<in> latestOps ctxt`
  obtain c
    where a0: "Op ctxt c \<triangleq> x"
      and a1: "is_update x"
      and a2: "\<forall>c' op'. is_update op' \<longrightarrow> Op ctxt c' \<triangleq> op' \<longrightarrow> (c, c') \<notin> happensBefore ctxt"
    by (auto simp add: latestOps_def) 

  show "\<exists>c. Op ctxt c \<triangleq> x \<and> (\<forall>c' x'. Op ctxt c' \<triangleq> x' \<longrightarrow> is_update x' \<longrightarrow> (c, c') \<in> happensBefore ctxt \<longrightarrow> x' = x)"
  proof (intro exI conjI allI impI)

    show "Op ctxt c \<triangleq> x"
      by (simp add: a0)


    show "x' = x"
      if c0: "Op ctxt c' \<triangleq> x'"
        and c1: "(c, c') \<in> happensBefore ctxt"
        and c2: "is_update x'"
      for  c' x'
      using a2 c0 c1 c2 by blast
  qed
next
  fix c
  assume a0: "is_update x"
    and a1: "Op ctxt c \<triangleq> x"
    and a2: "\<forall>c' x'. Op ctxt c' \<triangleq> x'  \<longrightarrow> is_update x' \<longrightarrow> (c, c') \<in> happensBefore ctxt \<longrightarrow> x' = x"

  text "Obtain hb-maximal c:"


  obtain cm
    where "Op ctxt cm \<triangleq> x"
      and "cm = c \<or> (c,cm)\<in>happensBefore ctxt"
      and "\<forall>y. Op ctxt y \<triangleq> x \<longrightarrow> (cm, y) \<notin> happensBefore ctxt"
    using operationContext_wf_exists_max[OF wf, where P="\<lambda>c. Op ctxt c \<triangleq> x", OF a1]
    by auto


  show "x \<in> latestOps ctxt"
  proof (auto simp add: latestOps_def `Op ctxt cm \<triangleq> x` a0 intro!: exI[where x=cm])
    fix c' op'
    assume b0: "is_update op'"
      and b1: "Op ctxt c' \<triangleq> op'"
      and b2: "(cm, c') \<in> happensBefore ctxt"


    have "(c, c') \<in> happensBefore ctxt"
      by (metis \<open>cm = c \<or> (c, cm) \<in> happensBefore ctxt\<close> b2 local.wf operationContext_wf_trans transE)


    from a2[rule_format, OF `Op ctxt c' \<triangleq> op'` `is_update op'` `(c, c') \<in> happensBefore ctxt`]
    show "False"
      using \<open>\<forall>y. Op ctxt y \<triangleq> x \<longrightarrow> (cm, y) \<notin> happensBefore ctxt\<close> b1 b2 by blast
  qed
qed


lemma latestOps_Enable:
  assumes wf: "operationContext_wf ctxt"
  shows "Enable \<in> latestOps ctxt \<longleftrightarrow>
  (\<exists>c. Op ctxt c \<triangleq> Enable \<and> (\<forall>c'. Op ctxt c' \<triangleq> Disable \<longrightarrow> (c, c')\<notin>happensBefore ctxt))"
  using flagOp.exhaust by (auto simp add: latestOps_alt[OF wf]) 


lemma latestOps_Disable:
  assumes wf: "operationContext_wf ctxt"
  shows "Disable \<in> latestOps ctxt \<longleftrightarrow>
  (\<exists>c. Op ctxt c \<triangleq> Disable \<and> (\<forall>c'. Op ctxt c' \<triangleq> Enable \<longrightarrow> (c, c')\<notin>happensBefore ctxt))"
  using flagOp.exhaust by (auto simp add: latestOps_alt[OF wf])


lemma latestOps_Enable':
  shows "Enable \<in> latestOps ctxt \<longleftrightarrow>
  (\<exists>c. Op ctxt c \<triangleq> Enable \<and> (\<forall>c'. Op ctxt c' \<triangleq> Enable \<or> Op ctxt c' \<triangleq> Disable \<longrightarrow> (c, c')\<notin>happensBefore ctxt))"
  by (auto simp add: latestOps_def)
   (metis (mono_tags, lifting) flagOp.exhaust)

lemma latestOps_Disable':
  shows "Disable \<in> latestOps ctxt \<longleftrightarrow>
  (\<exists>c. Op ctxt c \<triangleq> Disable \<and> (\<forall>c'. Op ctxt c' \<triangleq> Enable \<or> Op ctxt c' \<triangleq> Disable \<longrightarrow> (c, c')\<notin>happensBefore ctxt))"
  by (auto simp add: latestOps_def)
   (metis (mono_tags, lifting) flagOp.exhaust)


lemma latestOps_Enable'':
  assumes wf: "operationContext_wf ctxt"
    and "\<exists>e. Op ctxt e \<triangleq> Enable"
    and "\<forall>d. Op ctxt d \<triangleq> Disable \<longrightarrow> (\<exists>e. Op ctxt e \<triangleq> Enable \<and> (d, e) \<in> happensBefore ctxt)"
  shows "Enable \<in> latestOps ctxt"
proof -

  obtain e where e: "Op ctxt e \<triangleq> Enable \<or> Op ctxt e \<triangleq> Disable"
    using assms(2) by blast


  obtain em
    where "Op ctxt em \<triangleq> Enable \<or> Op ctxt em \<triangleq> Disable"
      and "\<forall>e'. (Op ctxt e' \<triangleq> Enable \<or> Op ctxt e' \<triangleq> Disable) \<longrightarrow> (em,e')\<notin>happensBefore ctxt"
    using operationContext_wf_exists_max[OF wf, where P="\<lambda>e. Op ctxt e \<triangleq> Enable \<or> Op ctxt e \<triangleq> Disable", OF e]
    by auto

  show ?thesis
    by (auto simp add: latestOps_alt[OF wf])
     (metis (mono_tags, lifting) \<open>\<And>thesis. (\<And>em. \<lbrakk>Op ctxt em \<triangleq> Enable \<or> Op ctxt em \<triangleq> Disable; \<forall>e'. Op ctxt e' \<triangleq> Enable \<or> Op ctxt e' \<triangleq> Disable \<longrightarrow> (em, e') \<notin> happensBefore ctxt\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(3) flagOp.exhaust)
qed

lemma latestOps_Disable'':
  assumes wf: "operationContext_wf ctxt"
    and "\<exists>e. Op ctxt e \<triangleq> Disable"
    and "\<forall>d. Op ctxt d \<triangleq> Enable \<longrightarrow> (\<exists>e. Op ctxt e \<triangleq> Disable \<and> (d, e) \<in> happensBefore ctxt)"
  shows "Disable \<in> latestOps ctxt"
proof -

  obtain e where e: "Op ctxt e \<triangleq> Enable \<or> Op ctxt e \<triangleq> Disable"
    using assms(2) by blast


  obtain em
    where "Op ctxt em \<triangleq> Enable \<or> Op ctxt em \<triangleq> Disable"
      and "\<forall>e'. (Op ctxt e' \<triangleq> Enable \<or> Op ctxt e' \<triangleq> Disable) \<longrightarrow> (em,e')\<notin>happensBefore ctxt"
    using operationContext_wf_exists_max[OF wf, where P="\<lambda>e. Op ctxt e \<triangleq> Enable \<or> Op ctxt e \<triangleq> Disable", OF e]
    by auto

  show ?thesis
    by (auto simp add: latestOps_alt[OF wf])
     (metis (full_types) \<open>Op ctxt em \<triangleq> Enable \<or> Op ctxt em \<triangleq> Disable\<close> \<open>\<forall>e'. Op ctxt e' \<triangleq> Enable \<or> Op ctxt e' \<triangleq> Disable \<longrightarrow> (em, e') \<notin> happensBefore ctxt\<close> assms(3) flagOp.exhaust)
qed


lemma flag_dw_ReadFlag: 
  assumes a1: "flag_dw_spec ReadFlag ctxt res"
    and wf: "operationContext_wf ctxt"
shows "res = from_bool ((\<exists>e. Op ctxt e \<triangleq> Enable) 
  \<and> (\<forall>d. Op ctxt d \<triangleq> Disable \<longrightarrow> (\<exists>e. Op ctxt e \<triangleq> Enable \<and> (d,e) \<in> happensBefore ctxt)))
  "
proof -
  from a1
  have res1: "res = from_bool (Enable \<in> latestOps ctxt \<and> Disable \<notin> latestOps ctxt)"
    by (simp add: flag_dw_spec_def)


  show ?thesis
    unfolding res1
    by  (rule arg_cong[where f=from_bool])
     (meson latestOps_Disable latestOps_Enable' latestOps_Enable'' local.wf)

qed




subsection "Sets"

text_raw \<open>\DefineSnippet{setOp}{\<close>
datatype 'v setOp =
    Add 'v
  | Remove 'v
  | Contains 'v
text_raw \<open>}%EndSnippet\<close>

 
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


text_raw \<open>\DefineSnippet{set_specs}{\<close>
definition set_to_flag where
"set_to_flag v op \<equiv> case op of
   Add x \<Rightarrow> if x = v then Some Enable else None
 | Remove x \<Rightarrow> if x = v then Some Disable else None
 | _ \<Rightarrow> None
"

definition set_spec :: "(flagOp, 'r::{default,from_bool}) crdtSpec \<Rightarrow> ('v setOp, 'r) crdtSpec" where
"set_spec F op ctxt res \<equiv> 
  case op of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> F ReadFlag (restrict_ctxt_op (set_to_flag v) ctxt) res"


definition "set_aw_spec \<equiv> set_spec flag_ew_spec"

definition "set_rw_spec \<equiv> set_spec flag_dw_spec"
text_raw \<open>}%EndSnippet\<close>



lemma set_aw_spec_Add[simp]:
"set_aw_spec (Add x) ctxt res \<longleftrightarrow> res = default"
  by (auto simp add: set_aw_spec_def set_spec_def)

lemma set_aw_spec_Remove[simp]:
"set_aw_spec (Remove x) ctxt res \<longleftrightarrow> res = default"
  by (auto simp add: set_aw_spec_def set_spec_def)

lemma set_rw_spec_Add[simp]:
"set_rw_spec (Add x) ctxt res \<longleftrightarrow> res = default"
  by (auto simp add: set_rw_spec_def set_spec_def)

lemma set_rw_spec_Remove[simp]:
"set_rw_spec (Remove x) ctxt res \<longleftrightarrow> res = default"
  by (auto simp add: set_rw_spec_def set_spec_def)



lemma from_bool_eq_simp:
  assumes "res = from_bool True \<or> res = from_bool False"
  shows "(res = from_bool a \<longleftrightarrow> res = from_bool b) \<longleftrightarrow> a = b"
  using assms
  by (metis from_bool_inj) 

lemma from_bool_eq_simp':
  assumes "a \<longleftrightarrow> b"
  shows "(res = from_bool a \<longleftrightarrow> res = from_bool b)"
  by (simp add: assms)

lemma set_to_flag_Enable:
"set_to_flag x y \<triangleq> Enable \<longleftrightarrow> y = Add x"
  by (auto simp add: set_to_flag_def split: setOp.splits)

lemma set_to_flag_Disable:
  "set_to_flag x y \<triangleq> Disable \<longleftrightarrow> y = Remove x"
  by (auto simp add: set_to_flag_def split: setOp.splits)

lemma set_to_flag_None:
  "set_to_flag x y = None \<longleftrightarrow> y \<noteq> Remove x \<and> y \<noteq> Add x"
  by (auto simp add: set_to_flag_def split: setOp.splits)

lemma trans_restrict_ctxt_op:
  assumes "trans (happensBefore ctxt)"
  shows "trans (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
  by (auto simp add: trans_def happensBefore_restrict_ctxt_op,
      meson assms transE)


lemma wf_restrict_ctxt_op:
  assumes "wf ((happensBefore ctxt)\<inverse>)"
  shows "wf ((happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))\<inverse>)"
  using assms proof (rule wf_subset)
  show "(happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))\<inverse> \<subseteq> (happensBefore ctxt)\<inverse>"
    by (auto simp add: happensBefore_restrict_ctxt_op)
qed


lemma Field_restrict_ctxt_op:
  assumes "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
  shows "Field (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt)) \<subseteq> dom (calls (restrict_ctxt_op (set_to_flag x) ctxt))"
  using assms by (auto simp add: Field_def happensBefore_restrict_ctxt_op)
   (metis cOp_def Op_restrict_ctxt_op map_option_eq_Some)+


lemma operationContext_wf_restrict_ctxt_op:
  assumes "operationContext_wf ctxt"
  shows "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt)"
  unfolding operationContext_wf_def 
proof (intro conjI)
  show "trans (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
  by (simp add: assms operationContext_wf_trans trans_restrict_ctxt_op)
  

  show "Field (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt)) \<subseteq> dom (calls (restrict_ctxt_op (set_to_flag x) ctxt))"
    by (simp add: Field_restrict_ctxt_op assms operationContext_wf_hb_field)

  show "irrefl (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
    by (meson assms happensBefore_restrict_ctxt_op irrefl_def operationContext_wf_irrefl)

  show "finite (dom (calls (restrict_ctxt_op (set_to_flag x) ctxt)))"
  proof (rule finite_subset)
    show "dom (calls (restrict_ctxt_op (set_to_flag x) ctxt)) \<subseteq> dom (calls ctxt)"
      by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def option_bind_def split: option.splits)
    show "finite (dom (calls ctxt))"
      by (simp add: assms operationContext_wf_finite)
  qed
qed

lemma set_aw_spec_Contains:
  assumes spec: "set_aw_spec (Contains x) ctxt res"
    and wf: "operationContext_wf ctxt"
  shows "res = from_bool (\<exists>a. Op ctxt a \<triangleq> Add x
                           \<and> (\<nexists>r. Op ctxt r \<triangleq> Remove x
                                \<and> (a,r)\<in>happensBefore ctxt))"
  using spec proof (auto simp add: set_aw_spec_def set_spec_def flag_ew_spec_def from_bool_inj)
  assume a0: "res = from_bool True"
    and a1: "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"


  have "\<exists>a. Op (restrict_ctxt_op (set_to_flag x) ctxt) a \<triangleq> Enable 
    \<and> (\<forall>r. Op (restrict_ctxt_op (set_to_flag x) ctxt) r \<triangleq> Disable 
          \<longrightarrow> (a, r) \<notin> happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
    using a1 latestOps_Enable' by blast


  thus "\<exists>a. Op ctxt a \<triangleq> Add x \<and> (\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (a, r) \<notin> happensBefore ctxt)"
    by (auto simp add: Op_restrict_ctxt_op option_bind_def happensBefore_restrict_ctxt_op
        set_to_flag_Enable set_to_flag_Disable  split: option.splits)
     (auto simp add: set_to_flag_def)

next

  fix a
  assume a0: "res = from_bool (Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt))"
    and a1: "Op ctxt a \<triangleq> Add x"
    and a2: "\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (a, r) \<notin> happensBefore ctxt"


  have a1': "Op (restrict_ctxt_op (set_to_flag x) ctxt) a \<triangleq> Enable"
    by (simp add: Op_restrict_ctxt_op a1 set_to_flag_Enable)

  have a2': "\<forall>r. Op (restrict_ctxt_op (set_to_flag x) ctxt) r \<triangleq> Disable 
    \<longrightarrow> (a, r) \<notin> happensBefore (restrict_ctxt_op (set_to_flag x) ctxt)"
    by (simp add: Op_restrict_ctxt_op a2 bind_eq_Some_conv happensBefore_restrict_ctxt_op set_to_flag_Disable)

  have wf'': "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt)"
    by (simp add: local.wf operationContext_wf_restrict_ctxt_op)


  show "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    using a1' a2' latestOps_Enable operationContext_wf_def wf'' by blast
qed

lemma set_aw_spec_Contains2:
  assumes spec: "res = from_bool (\<exists>a. Op ctxt a \<triangleq> Add x
                           \<and> (\<nexists>r. Op ctxt r \<triangleq> Remove x
                                \<and> (a,r)\<in>happensBefore ctxt))" (is "res = from_bool ?b")
    and wf: "operationContext_wf ctxt"
  shows  "set_aw_spec (Contains x) ctxt res"
proof (auto simp add: set_aw_spec_def set_spec_def flag_ew_spec_def )

  have owf: "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt)"
    by (simp add: local.wf operationContext_wf_restrict_ctxt_op)

  
  show "res = from_bool (Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt))"
  proof (cases "?b")
    case True
    from this obtain a where "Op ctxt a \<triangleq> Add x"
      and "\<nexists>r. Op ctxt r \<triangleq> Remove x \<and> (a, r) \<in> happensBefore ctxt"
      by blast

    thm set_to_flag_Disable set_to_flag_Enable

    hence "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      by (subst latestOps_Enable[OF owf])
       (auto simp add: Op_restrict_ctxt_op option_bind_def set_to_flag_def happensBefore_restrict_ctxt_op' split: option.splits setOp.splits cong: conj_cong)

    thus ?thesis
      using True local.spec by auto

  next
    case False
    hence "Enable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      by (subst latestOps_Enable[OF owf])
        (auto simp add: Op_restrict_ctxt_op option_bind_def set_to_flag_def happensBefore_restrict_ctxt_op' split: option.splits setOp.splits cong: conj_cong,
            fastforce)


    then show ?thesis
      by (smt False local.spec)
  qed
qed

lemma set_aw_spec_contains:
  assumes  "operationContext_wf ctxt"
  shows "set_aw_spec (Contains x) ctxt res \<longleftrightarrow>
    res = from_bool (\<exists>a. Op ctxt a \<triangleq> Add x
                           \<and> (\<nexists>r. Op ctxt r \<triangleq> Remove x
                                \<and> (a,r)\<in>happensBefore ctxt))"
  using assms set_aw_spec_Contains set_aw_spec_Contains2 by fastforce


text \<open>
\DefineSnippet{set_aw_spec_contains}{
  @{thm [display] (concl) set_aw_spec_contains}
}%EndSnippet\<close>


lemma exists_skolem:
"(\<exists>f. \<forall>x. P x (f x)) \<longleftrightarrow> (\<forall>x. \<exists>y. P x y)"
  by metis

lemma exists_skolem2a:
"(\<exists>f. \<forall>x y. P x y (f x y)) \<longleftrightarrow> (\<forall>x y. \<exists>z. P x y z)"
  by metis

lemma exists_skolem2b:
"(\<exists>f. \<forall>y x. P x y (f x y)) \<longleftrightarrow> (\<forall>y x. \<exists>z. P x y z)"
  by (subst all_comm, subst exists_skolem2a) auto


text_raw \<open>\DefineSnippet{set_rw_spec_Contains}{\<close>
lemma set_rw_spec_Contains:
  assumes spec: "set_rw_spec (Contains x) ctxt res"
    and wf: "operationContext_wf ctxt"
  shows "res = from_bool ((\<exists>a. Op ctxt a \<triangleq> Add x)
                           \<and> (\<forall>r. Op ctxt r \<triangleq> Remove x
                                \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x
                                    \<and> (r,a)\<in>happensBefore ctxt)))"
text_raw \<open>}%EndSnippet\<close>
  using spec proof (auto simp add: set_rw_spec_def set_spec_def flag_dw_spec_def from_bool_inj)
  assume a0: "res = from_bool True"
    and a1: "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    and a2: "Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"

  show "\<exists>a. Op ctxt a \<triangleq> Add x"
    by (smt Op_restrict_ctxt_op a1 bind_eq_Some_conv latestOps_Enable' set_to_flag_Enable)

next
  fix r
  assume a0: "res = from_bool True"
    and a1: "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    and a2: "Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    and a3: "Op ctxt r \<triangleq> Remove x"

  show "\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt"
  proof -
    obtain cc :: "callId \<Rightarrow> (flagOp, 'b) operationContext \<Rightarrow> callId" where
      f1: "\<forall>x0 x1. (\<exists>v2. Op x1 v2 \<triangleq> Enable \<and> (x0, v2) \<in> happensBefore x1) = (Op x1 (cc x0 x1) \<triangleq> Enable \<and> (x0, cc x0 x1) \<in> happensBefore x1)"
      by moura
    obtain ss :: "flagOp \<Rightarrow> ('a setOp \<Rightarrow> flagOp option) \<Rightarrow> 'a setOp option \<Rightarrow> 'a setOp" where
      "\<forall>x0 x1 x2. (\<exists>v3. x2 \<triangleq> v3 \<and> x1 v3 \<triangleq> x0) = (x2 \<triangleq> ss x0 x1 x2 \<and> x1 (ss x0 x1 x2) \<triangleq> x0)"
      by moura
    then have f2: "\<forall>z f fa. (z \<bind> f \<noteq> Some fa \<or> z \<triangleq> ss fa f z \<and> f (ss fa f z) \<triangleq> fa) \<and> ((z \<bind> f) \<triangleq> fa \<or> (\<forall>s. z \<noteq> Some s \<or> f s \<noteq> Some fa))"
      by (meson bind_eq_Some_conv)
    have "(Some (Remove x) \<bind> set_to_flag x) \<triangleq> Disable"
      by (simp add: set_to_flag_Disable)
    then have "Op (restrict_ctxt_op (set_to_flag x) ctxt) (cc r (restrict_ctxt_op (set_to_flag x) ctxt)) \<triangleq> Enable \<and> (r, cc r (restrict_ctxt_op (set_to_flag x) ctxt)) \<in> happensBefore (restrict_ctxt_op (set_to_flag x) ctxt)"
      using f1
      by (metis Op_restrict_ctxt_op a2 a3 latestOps_Disable local.wf operationContext_wf_restrict_ctxt_op)
    then show ?thesis
      using f2 by (metis (full_types) Op_restrict_ctxt_op happensBefore_restrict_ctxt_op set_to_flag_Enable)
  qed
next
  fix a
  assume a0: "res =           from_bool            (Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt) \<and>             Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt))"
    and a1: "\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)"
    and a2: "Op ctxt a \<triangleq> Add x"

  show "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
  proof (rule latestOps_Enable'')
    show "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt)"
      by (simp add: local.wf operationContext_wf_restrict_ctxt_op)
    show "\<exists>e. Op (restrict_ctxt_op (set_to_flag x) ctxt) e \<triangleq> Enable"
      by (metis Op_restrict_ctxt_op a2 bind.bind_lunit set_to_flag_Enable)
    show "\<forall>d. Op (restrict_ctxt_op (set_to_flag x) ctxt) d \<triangleq> Disable \<longrightarrow>
        (\<exists>e. Op (restrict_ctxt_op (set_to_flag x) ctxt) e \<triangleq> Enable \<and>
             (d, e) \<in> happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
      by (auto simp add: Op_restrict_ctxt_op happensBefore_restrict_ctxt_op)
       (metis (no_types, lifting) a1 bind_eq_Some_conv set_to_flag_Disable set_to_flag_Enable)
  qed


next 
  fix a
  assume a0: "res = from_bool False"
    and a1: "\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)"
    and a2: "Op ctxt a \<triangleq> Add x"
    and a3: "Disable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"

  have wf': "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt)"
    by (simp add: local.wf operationContext_wf_restrict_ctxt_op)


  show "False"
  proof -
    obtain cc :: "callId \<Rightarrow> flagOp \<Rightarrow> (flagOp, 'b) operationContext \<Rightarrow> callId" and ff :: "callId \<Rightarrow> flagOp \<Rightarrow> (flagOp, 'b) operationContext \<Rightarrow> flagOp" where
      f2: "\<forall>x0 x1 x2. (\<exists>v3 v4. (Op x2 v3 \<triangleq> v4 \<and> is_update v4 \<and> (x0, v3) \<in> happensBefore x2) \<and> v4 \<noteq> x1) = ((Op x2 (cc x0 x1 x2) \<triangleq> ff x0 x1 x2 \<and> is_update (ff x0 x1 x2) \<and> (x0, cc x0 x1 x2) \<in> happensBefore x2) \<and> ff x0 x1 x2 \<noteq> x1)"
      by moura
    obtain cca :: "flagOp \<Rightarrow> (flagOp, 'b) operationContext \<Rightarrow> callId" where
      "\<forall>x0 x1. (\<exists>v2. Op x1 v2 \<triangleq> x0 \<and> (\<forall>v3 v4. (Op x1 v3 \<noteq> Some v4 \<or> is_query v4 \<or> (v2, v3) \<notin> happensBefore x1) \<or> v4 = x0)) = (Op x1 (cca x0 x1) \<triangleq> x0 \<and> (\<forall>v3 v4. (Op x1 v3 \<noteq> Some v4 \<or> is_query v4 \<or> (cca x0 x1, v3) \<notin> happensBefore x1) \<or> v4 = x0))"
      by (atomize_elim, subst exists_skolem2a, auto, blast)
    then have f3: "\<forall>f z. ((f \<in> latestOps z) = (is_update f \<and> (\<exists>c. Op z c \<triangleq> f \<and> (\<forall>ca fa. (Op z ca \<noteq> Some fa \<or> is_query fa \<or> (c, ca) \<notin> happensBefore z) \<or> fa = f)))) = ((f \<notin> latestOps z \<or> is_update f \<and> Op z (cca f z) \<triangleq> f \<and> (\<forall>c fa. (Op z c \<noteq> Some fa \<or> is_query fa \<or> (cca f z, c) \<notin> happensBefore z) \<or> fa = f)) \<and> (f \<in> latestOps z \<or> is_query f \<or> (\<forall>c. Op z c \<noteq> Some f \<or> (Op z (cc c f z) \<triangleq> ff c f z \<and> is_update (ff c f z) \<and> (c, cc c f z) \<in> happensBefore z) \<and> ff c f z \<noteq> f)))"
      using f2 by blast
    have f4: "wf ((happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))\<inverse>)"
      by (simp add: local.wf operationContext_wf_wf wf_restrict_ctxt_op)
    have "trans (happensBefore (restrict_ctxt_op (set_to_flag x) ctxt))"
      by (simp add: local.wf operationContext_wf_restrict_ctxt_op operationContext_wf_trans)
    then have f5: "is_update Disable \<and> Op (restrict_ctxt_op (set_to_flag x) ctxt) (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt)) \<triangleq> Disable \<and> (\<forall>c f. Op (restrict_ctxt_op (set_to_flag x) ctxt) c \<noteq> Some f \<or> is_query f \<or> (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt), c) \<notin> happensBefore (restrict_ctxt_op (set_to_flag x) ctxt) \<or> f = Disable)"
      by (metis (no_types, lifting) a3 f3 latestOps_alt wf')
    obtain ccb :: "callId \<Rightarrow> callId" where
      f6: "\<forall>c. Op ctxt c \<noteq> Some (Remove x) \<or> Op ctxt (ccb c) \<triangleq> Add x \<and> (c, ccb c) \<in> happensBefore ctxt"
      using a1 by moura
    obtain ss :: "flagOp \<Rightarrow> ('a setOp \<Rightarrow> flagOp option) \<Rightarrow> 'a setOp option \<Rightarrow> 'a setOp" where
      "\<forall>x0 x1 x2. (\<exists>v3. x2 \<triangleq> v3 \<and> x1 v3 \<triangleq> x0) = (x2 \<triangleq> ss x0 x1 x2 \<and> x1 (ss x0 x1 x2) \<triangleq> x0)"
      by moura
    then have "Op ctxt (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt)) \<triangleq> ss Disable (set_to_flag x) (Op ctxt (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt))) \<and> set_to_flag x (ss Disable (set_to_flag x) (Op ctxt (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt)))) \<triangleq> Disable"
      using f5 by (simp add: Op_restrict_ctxt_op bind_eq_Some_conv)
    then have "Op ctxt (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt)) \<triangleq> Remove x"
      by (metis set_to_flag_Disable)
    then have "Op ctxt (ccb (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt))) \<triangleq> Add x \<and> (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt), ccb (cca Disable (restrict_ctxt_op (set_to_flag x) ctxt))) \<in> happensBefore ctxt"
      using f6 by blast
    then show ?thesis
      using f5 by (metis (no_types) Op_restrict_ctxt_op bind.bind_lunit flagOp.distinct(1) flagOp.distinct(3) happensBefore_restrict_ctxt_op is_update_flagOp_def set_to_flag_Enable)
  qed
qed


lemma set_rw_spec_Contains2:
  assumes spec: "res = from_bool ((\<exists>a. Op ctxt a \<triangleq> Add x)
                           \<and> (\<forall>r. Op ctxt r \<triangleq> Remove x
                                \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x
                                    \<and> (r,a)\<in>happensBefore ctxt)))"
    and wf: "operationContext_wf ctxt"
  shows  "set_rw_spec (Contains x) ctxt res"
proof (auto simp add: set_rw_spec_def set_spec_def flag_dw_spec_def spec intro!: arg_cong[where f=from_bool]) 

  have wf': "operationContext_wf (restrict_ctxt_op (set_to_flag x) ctxt) "
    by (simp add: local.wf operationContext_wf_restrict_ctxt_op)


  show "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    if c0: "\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)"
      and c1: "Op ctxt a \<triangleq> Add x"
    for  a
    by (rule latestOps_Enable''[OF wf'])
      (use that in \<open>auto simp add:  Op_restrict_ctxt_op_eq set_to_flag_Enable 
      set_to_flag_Disable happensBefore_restrict_ctxt_op' set_to_flag_None\<close>)


  show "False"
    if c0: "\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)"
      and c1: "Op ctxt a \<triangleq> Add x"
      and c2: "Disable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    for  a
    using that
    by (auto simp add: set_to_flag_None  Op_restrict_ctxt_op_eq happensBefore_restrict_ctxt_op latestOps_Disable set_to_flag_Disable set_to_flag_Enable wf')



  show "\<exists>a. Op ctxt a \<triangleq> Add x"
    if c0: "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      and c1: "Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
    by (smt Op_restrict_ctxt_op_eq c0 latestOps_Enable set_to_flag_Enable wf') 


  show "\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt"
    if c0: "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      and c1: "Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      and c2: "Op ctxt r \<triangleq> Remove x"
    for  r
    using that
    by (auto simp add: set_to_flag_None  Op_restrict_ctxt_op_eq happensBefore_restrict_ctxt_op latestOps_Disable set_to_flag_Disable set_to_flag_Enable wf')
qed


text_raw \<open>\DefineSnippet{set_rw_spec_Contains_iff}{\<close>
lemma set_rw_spec_Contains_iff:
  assumes wf: "operationContext_wf ctxt"
  shows  "set_rw_spec (Contains x) ctxt res
\<longleftrightarrow> res = from_bool ((\<exists>a. Op ctxt a \<triangleq> Add x)
                           \<and> (\<forall>r. Op ctxt r \<triangleq> Remove x
                                \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x
                                    \<and> (r,a)\<in>happensBefore ctxt)))"
  text_raw \<open>}%EndSnippet\<close>
  using local.wf set_rw_spec_Contains set_rw_spec_Contains2 by fastforce



(*
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

*)

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

lemma set_spec_cannot_guess_ids[simp,intro]:
  assumes "\<And>x y res. f x y res \<Longrightarrow> uniqueIds res = {}" 
  shows "queries_cannot_guess_ids (set_spec f)"
  by (auto simp add: queries_cannot_guess_ids_def query_cannot_guess_ids_def set_spec_def 
       split: setOp.splits dest!: assms)

lemma set_aw_spec_cannot_guess_ids[simp,intro]:
  assumes "\<And>x. uniqueIds (from_bool x) = {}"
  shows "queries_cannot_guess_ids set_aw_spec"
  unfolding set_aw_spec_def
  by (standard) (auto simp add: flag_ew_spec_def split: flagOp.splits)



lemma set_rw_spec_cannot_guess_ids[simp,intro]:
  assumes "\<And>x. uniqueIds (from_bool x) = {}"
  shows "queries_cannot_guess_ids set_rw_spec"
  unfolding set_rw_spec_def
  by (standard) (auto simp add: flag_dw_spec_def split: flagOp.splits)


lemma flag_ew_spec_restrict_hb[simp]:
"flag_ew_spec op (restrict_hb c) r
\<longleftrightarrow> flag_ew_spec op c r"
  by (auto simp add: flag_ew_spec_def latestOps_def restrict_relation_def restrict_hb_def cOp_def 
      intro!: arg_cong[where f=from_bool]
      split: flagOp.splits)


lemma latestOps_restrict_ctxt_op_restrict_hb:
" latestOps (restrict_ctxt_op f (restrict_hb c))
 =  latestOps (restrict_ctxt_op f c)"
  by (auto simp add: latestOps_def restrict_ctxt_op_def cOp_def restrict_ctxt_def fmap_map_values_def restrict_relation_def)
   (metis (mono_tags, lifting) bind_eq_None_conv domIff)


lemma flag_ew_spec_restrict_hb2:
"flag_ew_spec ReadFlag (restrict_ctxt_op f (restrict_hb c)) r
\<longleftrightarrow> flag_ew_spec ReadFlag (restrict_ctxt_op f c) r"
  by (auto simp add: flag_ew_spec_def latestOps_restrict_ctxt_op_restrict_hb intro!: arg_cong[where f=from_bool])

lemma set_aw_spec_restrict_hb[simp]:
"set_aw_spec op (restrict_hb c) r 
\<longleftrightarrow> set_aw_spec op c r"
  by (auto simp add: set_aw_spec_def set_spec_def flag_ew_spec_restrict_hb2 split: setOp.splits)


lemma flag_dw_spec_restrict_hb2:
"flag_dw_spec ReadFlag (restrict_ctxt_op f (restrict_hb c)) r
\<longleftrightarrow> flag_dw_spec ReadFlag (restrict_ctxt_op f c) r"
  by (auto simp add: flag_dw_spec_def latestOps_restrict_ctxt_op_restrict_hb intro!: arg_cong[where f=from_bool])

lemma set_rw_spec_restrict_hb[simp]:
"set_rw_spec op (restrict_hb c) r 
\<longleftrightarrow> set_rw_spec op c r"
  by (auto simp add: set_rw_spec_def set_spec_def flag_dw_spec_restrict_hb2 split: setOp.splits)




subsection "Maps"

text_raw \<open>\DefineSnippet{mapOp}{\<close>
datatype ('k,'v) mapOp =
      NestedOp 'k 'v
    | KeyExists 'k
    | DeleteKey 'k
text_raw \<open>}%EndSnippet\<close>


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


text_raw \<open>\DefineSnippet{map_specs}{\<close>
definition
"nested_op_on_key k op \<equiv> 
    case op of NestedOp k' op' \<Rightarrow> if k = k' then Some op' else None 
             | _ \<Rightarrow> None"

definition map_spec :: "((('k, 'v::crdt_op) mapOp, 'r::{default,from_bool}) operationContext \<Rightarrow> 'k \<Rightarrow> callId set) \<Rightarrow>  ('v,'r) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_spec deleted_calls nestedSpec oper ctxt res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c op r. calls ctxt c \<triangleq> Call (NestedOp k op) r 
                                        \<and> is_update op \<and>  c \<notin> deleted_calls ctxt k)
  | NestedOp k op \<Rightarrow>
     nestedSpec op (sub_context (nested_op_on_key k) (- deleted_calls ctxt k) ctxt) res
"
text_raw \<open>}%EndSnippet\<close>

abbreviation "
is_concurrent ctxt c c' \<equiv> (c,c')\<notin>happensBefore ctxt \<and> (c',c)\<notin>happensBefore ctxt \<and> c\<noteq>c'"

text_raw \<open>\DefineSnippet{map_specs2}{\<close>


definition
"deleted_calls_uw ctxt k \<equiv> {c\<in>dom (calls ctxt).  
    \<exists>d. Op ctxt d \<triangleq> DeleteKey k \<and> (c,d)\<in>happensBefore ctxt}"

definition
"deleted_calls_suw ctxt k \<equiv> {c\<in>dom (calls ctxt).  
    \<exists>d. Op ctxt d \<triangleq> DeleteKey k \<and> (c,d)\<in>happensBefore ctxt
     \<and> (\<nexists>u u_op. Op ctxt u \<triangleq> NestedOp k u_op \<and> is_update u_op \<and> is_concurrent ctxt u d)}"

definition
"deleted_calls_dw ctxt k \<equiv> {c\<in>dom (calls ctxt). 
  \<exists>d. Op ctxt d \<triangleq> DeleteKey k \<and> 
  ((c,d)\<in>happensBefore ctxt
   \<or> is_concurrent ctxt c d 
      \<and> (\<nexists>u u_op. Op ctxt u \<triangleq> NestedOp k u_op \<and> is_update u_op 
                 \<and> (d,u)\<in>happensBefore ctxt))}"

definition
"deleted_calls_sdw ctxt k \<equiv> {c\<in>dom (calls ctxt). 
  \<exists>d. Op ctxt d \<triangleq> DeleteKey k \<and> (d,c)\<notin>happensBefore ctxt}"

definition map_uw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_uw_spec \<equiv> map_spec deleted_calls_uw"

definition map_suw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_suw_spec \<equiv> map_spec deleted_calls_suw"

definition map_dw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_dw_spec \<equiv> map_spec deleted_calls_dw"

definition map_sdw_spec :: "('v::crdt_op,'r::{default,from_bool}) crdtSpec \<Rightarrow> (('k, 'v) mapOp, 'r) crdtSpec" where
"map_sdw_spec \<equiv> map_spec deleted_calls_sdw"
text_raw \<open>}%EndSnippet\<close>



lemma calls_ctxt_restrict_calls: "calls (ctxt_restrict_calls S ctxt) c = (calls ctxt |` S) c"
  by (auto simp add: ctxt_restrict_calls_def)

lemma calls_restrict_ctxt_op: "calls (restrict_ctxt_op f ctxt) c
  = (case calls ctxt c of None \<Rightarrow> None | Some (Call op r) \<Rightarrow> (case f op of None \<Rightarrow> None | Some op' \<Rightarrow> Some (Call op' r)))"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def' split: option.splits call.splits)

lemma calls_restrict_ctxt_op2: "calls (restrict_ctxt_op f ctxt)
  = (\<lambda>c. calls ctxt c \<bind> (\<lambda>call. f (call_operation call) \<bind> (\<lambda>op'. Some (Call op' (call_res call)))))"
  by (auto simp add: calls_restrict_ctxt_op split: option.splits call.splits)


lemma happensBefore_restrict_ctxt_op2:  "(c, c') \<in> happensBefore (restrict_ctxt_op f ctxt) \<longleftrightarrow> 
(\<exists>op r op' r'. (c, c') \<in> happensBefore ctxt 
  \<and> calls ctxt c \<triangleq> Call op r \<and> f op \<noteq> None 
  \<and> calls ctxt c' \<triangleq> Call op' r' \<and> f op' \<noteq> None)"
  by (auto simp add: restrict_ctxt_op_def restrict_ctxt_def restrict_relation_def  fmap_map_values_eq_some split: call.splits option.splits)
   (metis call.collapse)

lemma happensBefore_ctxt_restrict_calls: "(c, c') \<in> happensBefore (ctxt_restrict_calls S ctxt) \<longleftrightarrow> (c, c') \<in> happensBefore ctxt |r S"
  by (auto simp add: ctxt_restrict_calls_def)

lemma restrict_simp1:
"(restrict_ctxt_op (nested_op_on_key x11)
           (ctxt_restrict_calls (deleted_calls_uw (restrict_hb c) x) (restrict_hb c)))
= (restrict_hb (restrict_ctxt_op (nested_op_on_key x11) (ctxt_restrict_calls (deleted_calls_uw c x) c)))"
  by (auto simp add: fmap_map_values_def restrict_map_def restrict_relation_def restrict_ctxt_op_def
      restrict_hb_def restrict_ctxt_def ctxt_restrict_calls_def  intro!: ext split: option.splits call.splits)
    (auto simp add:  deleted_calls_uw_def cOp_def)


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
  by (auto simp add: deleted_calls_uw_def restrict_relation_def cOp_def intro!: ext, auto)



lemma deleted_calls_sdw_restrict_hb[simp]:
 "deleted_calls_sdw (restrict_hb c) = deleted_calls_sdw c"
  by (auto simp add: deleted_calls_sdw_def restrict_relation_def cOp_def intro!: ext, auto)


lemma map_uw_spec_wf_restrict_hb[simp]:
  assumes wf: "crdt_spec_wf nested"
  shows
"map_uw_spec nested op (restrict_hb c) r
\<longleftrightarrow> map_uw_spec nested op c r"
  by (simp add: map_uw_spec_def wf)

lemma map_sdw_spec_wf_restrict_hb[simp]:
  assumes wf: "crdt_spec_wf nested"
  shows
"map_sdw_spec nested op (restrict_hb c) r
\<longleftrightarrow> map_sdw_spec nested op c r"
  by (simp add: map_sdw_spec_def wf)


lemma map_uw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_uw_spec nested)"
  using crdt_spec_wf_def local.wf map_uw_spec_wf_restrict_hb by blast

lemma map_sdw_spec_wf: 
  assumes wf: "crdt_spec_wf nested"
  shows "crdt_spec_wf (map_sdw_spec nested)"
  using crdt_spec_wf_def local.wf map_sdw_spec_wf_restrict_hb by blast


subsection "Structs"

text_raw \<open>\DefineSnippet{struct_field}{\<close>
definition "select_field f x \<equiv> 
  if \<exists>y. x = f y then Some (inv f x) else None"

definition struct_field :: "('i \<Rightarrow> 'o) \<Rightarrow> ('i, 'r) crdtSpec \<Rightarrow> ('o, 'r) crdtSpec"  where
"struct_field f spec \<equiv> \<lambda>op ctxt r. 
    case select_field f op of 
      Some i_op \<Rightarrow> spec i_op (restrict_ctxt_op (select_field f) ctxt) r
    | None \<Rightarrow> False"

definition compose_struct :: "('o, 'r) crdtSpec \<Rightarrow> ('o, 'r) crdtSpec \<Rightarrow> ('o, 'r) crdtSpec" (infixr ".\<or>." 30) where
"A .\<or>. B \<equiv> \<lambda>op ctxt r. A op ctxt r \<or> B op ctxt r"
text_raw \<open>}%EndSnippet\<close>


lemma compose_struct_simp[simp]:
"(A .\<or>. B) op ctxt r \<longleftrightarrow> A op ctxt r \<or> B op ctxt r"
  by (auto simp add: compose_struct_def)


lemma select_field_reverse:
  assumes "inj f"
  shows "is_reverse (select_field f) f"
  by (auto simp add: is_reverse_def select_field_def assms)

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

qed


lemma map_uw_spec_queries_cannot_guess_ids[intro!]:
  assumes nested: "queries_cannot_guess_ids n"
  shows"queries_cannot_guess_ids (map_uw_spec n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_uw_spec_def nested)

lemma map_sdw_spec_queries_cannot_guess_ids[intro!]:
  assumes nested: "queries_cannot_guess_ids n"
  shows"queries_cannot_guess_ids (map_sdw_spec n) "
  by (simp add: map_spec_queries_cannot_guess_ids map_sdw_spec_def nested)


lemma latest_values_call:
  assumes "x \<in> latestValues ctxt"
  shows "\<exists>c. Op ctxt c \<triangleq> Assign x"
  using assms  by (auto simp add: latestValues_def2 cOp_def)

lemma register_spec_queries_cannot_guess_ids[intro]:
  assumes i_no: "uniqueIds i = {}"
  shows "queries_cannot_guess_ids (register_spec i)"
proof (auto simp add: queries_cannot_guess_ids_def2 register_spec_def i_no  split: registerOp.splits)
  fix ctxt res x xa
  assume a0: "res \<in> latestValues ctxt"
    and a1: "x \<in> uniqueIds res"
    and a2: "\<forall>cId opr. (\<forall>res. calls ctxt cId \<noteq> Some (Call opr res)) \<or> x \<notin> uniqueIds opr"
    and a3: "xa \<in> latestValues ctxt"

  from latest_values_call[OF a0]
  obtain a where "Op ctxt a \<triangleq> Assign res"
    by blast

  from this obtain r where "calls ctxt a \<triangleq> Call (Assign res) r"
    by (auto simp add: cOp_def)
     (metis call.collapse)

  with a1 a2
  show "False"
    by fastforce
qed




lemma query_cannot_guess_ids_struct_field2[intro!]:
  assumes a1: "queries_cannot_guess_ids spec"
    and a2: "\<And>op op'. uniqueIds op \<subseteq> uniqueIds (f op)"
    and "inj f"
  shows "queries_cannot_guess_ids (struct_field f spec)"
  unfolding queries_cannot_guess_ids_def query_cannot_guess_ids_def struct_field_def
proof (auto split: option.splits)
  fix opr ctxt res x2 x
  assume b0: "select_field f opr \<triangleq> x2"
    and b1: "spec x2 (restrict_ctxt_op (select_field f) ctxt) res"
    and b2: "x \<in> uniqueIds res"
    and b3: "\<forall>xa. (\<forall>cId c. xa = uniqueIds (call_operation c) \<longrightarrow> calls ctxt cId \<noteq> Some c) \<or> x \<notin> xa"

  from b0
  obtain y 
    where "opr = f y"
      and "x2 = inv f opr"
    unfolding select_field_def by (auto split: if_splits)

  have "\<nexists>cId opr res. calls (restrict_ctxt_op (select_field f) ctxt) cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr "
    using a2 assms(3) b3  
    by (auto  simp add: restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def option_bind_def select_field_def split: option.splits)
     fastforce



  with use_queries_cannot_guess_ids[OF a1 b1 b2]
  have r: "x \<in> uniqueIds x2"
    by blast

  then
  show "x \<in> uniqueIds opr"
    using \<open>opr = f y\<close> \<open>x2 = inv f opr\<close> a2 assms(3) by auto
qed

lemma queries_cannot_guess_ids_combine[intro!]:
  assumes "queries_cannot_guess_ids specA"
    and "queries_cannot_guess_ids specB"
  shows "queries_cannot_guess_ids (specA .\<or>. specB)"
  using assms by (auto simp add: compose_struct_def queries_cannot_guess_ids_def query_cannot_guess_ids_def)



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