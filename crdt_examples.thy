theory crdt_examples
  imports crdt_specs
begin

section "CRDT Examples"


text "Next we validate the specification on some examples"

subsection "Flags"


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
  by (auto simp add: flag_ew_spec_def latestOps_def example1_def Op_def)
lemma "flag_sew_spec ReadFlag example1 False"
  by (auto simp add: flag_sew_spec_def latestOps_def example1_def Op_def)
lemma "flag_dw_spec ReadFlag example1 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example1_def Op_def)
lemma "flag_sdw_spec ReadFlag example1 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example1_def Op_def)


lemma "flag_ew_spec ReadFlag example2 True"
  by (auto simp add: flag_ew_spec_def latestOps_def example2_def Op_def)
lemma "flag_sew_spec ReadFlag example2 True"
  by (auto simp add: flag_sew_spec_def latestOps_def example2_def Op_def)
lemma "flag_dw_spec ReadFlag example2 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example2_def Op_def cong: conj_cong)
lemma "flag_sdw_spec ReadFlag example2 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example2_def Op_def cong: conj_cong)


lemma "flag_ew_spec ReadFlag example3 True"
  by (auto simp add: flag_ew_spec_def latestOps_def example3_def Op_def cong: conj_cong)
   (smt callId.inject)
lemma "flag_sew_spec ReadFlag example3 True"
  by (auto simp add: flag_sew_spec_def latestOps_def example3_def Op_def cong: conj_cong)
   (smt callId.inject)
lemma "flag_dw_spec ReadFlag example3 True"
  by (auto simp add: flag_dw_spec_def latestOps_def example3_def Op_def cong: conj_cong)
   (smt callId.inject)
lemma "flag_sdw_spec ReadFlag example3 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example3_def Op_def cong: conj_cong)

lemma "flag_ew_spec ReadFlag example4 False"
  by (auto simp add: flag_ew_spec_def latestOps_def example4_def Op_def cong: conj_cong)
lemma "flag_sew_spec ReadFlag example4 True"
  by (auto simp add: flag_sew_spec_def latestOps_def example4_def Op_def cong: conj_cong)
lemma "flag_dw_spec ReadFlag example4 False"
  by (auto simp add: flag_dw_spec_def latestOps_def example4_def Op_def cong: conj_cong)
lemma "flag_sdw_spec ReadFlag example4 False"
  by (auto simp add: flag_sdw_spec_def latestOps_def example4_def Op_def cong: conj_cong)
   (smt callId.inject)+





subsection "Maps"


text \<open>We illustrate the different map semantics based on examples:\<close>

abbreviation "c \<equiv> CallId"

definition "hb r \<equiv> (\<lambda>(x,y). (c x, c y))`  r\<^sup>+"

definition "exampleA \<equiv> \<lparr>
  calls = [
    c 0 \<mapsto> Call (DeleteKey 1) default, 
    c 1 \<mapsto> Call (DeleteKey 1) default,
    c 2 \<mapsto> Call (NestedOp 1 (Increment 1)) default
  ],
  happensBefore = hb {(0,2)}
\<rparr>"


definition "exampleB \<equiv> \<lparr>
  calls = [
    c 0 \<mapsto> Call (DeleteKey 1) default, 
    c 1 \<mapsto> Call (DeleteKey 1) default,
    c 2 \<mapsto> Call (NestedOp 1 (Increment 1)) default,
    c 3 \<mapsto> Call (NestedOp 1 (Increment 1)) default
  ],
  happensBefore = hb {(0,2), (1,3)}
\<rparr>"

definition "exampleC \<equiv> \<lparr>
  calls = [
    c 0 \<mapsto> Call (NestedOp 1 (Increment 1)) default, 
    c 1 \<mapsto> Call (NestedOp 1 (Increment 1)) default,
    c 2 \<mapsto> Call (DeleteKey 1) default
  ],
  happensBefore = hb {(0,2)}
\<rparr>"

definition "exampleD \<equiv> \<lparr>
  calls = [
    c 0 \<mapsto> Call (NestedOp 1 (Increment 1)) default, 
    c 1 \<mapsto> Call (NestedOp 1 (Increment 1)) default,
    c 2 \<mapsto> Call (DeleteKey 1) default,
    c 3 \<mapsto> Call (DeleteKey 1) default
  ],
  happensBefore = hb {(0,2), (1,3)}
\<rparr>"


definition "dom_subset A m \<equiv> A \<inter> dom m"

lemma dom_subset_empty[simp]: "dom_subset {} m = {}"
  by (simp add: dom_subset_def)

lemma dom_subset_insert[simp]: "dom_subset (insert x A) m = (case m x of Some y \<Rightarrow> {x} | None \<Rightarrow> {}) \<union> dom_subset A m"
  by (auto simp add: dom_subset_def split: option.splits)

lemma dom_subset_ex:
  assumes "\<And>x y. m x \<triangleq> y \<Longrightarrow>  x \<in> {c 0, c 1, c 2, c 3}"
  shows "dom m = dom_subset {c 0, c 1, c 2, c 3} m"
  using assms by (auto simp add: dom_subset_def)

method eval_example_auto = (auto simp add: map_dw_spec_def map_spec_def
    counter_spec_def sub_context_def restrict_ctxt_op_def
    restrict_ctxt_def fmap_map_values_def ctxt_restrict_calls_def
    restrict_map_def deleted_calls_dw_def 
    exampleA_def exampleB_def exampleC_def exampleD_def 
    Op_def hb_def
    is_update_counterOp_def sum_map_def map_uw_spec_def deleted_calls_uw_def
    option_bind_def trancl_insert  increments_def nested_op_on_key_def
    rtrancl_insert
    map_suw_spec_def deleted_calls_suw_def
    map_sdw_spec_def deleted_calls_sdw_def
    split: option.splits if_splits)

method eval_example = (eval_example_auto; (subst dom_subset_ex)?)+

lemma "map_uw_spec counter_spec (NestedOp 1 GetCount) exampleA (from_int 1)"
  by eval_example

lemma "map_suw_spec counter_spec (NestedOp 1 GetCount) exampleA (from_int 1)"
  by eval_example

lemma "map_dw_spec counter_spec (NestedOp 1 GetCount) exampleA (from_int 0)"
  by eval_example

lemma "map_sdw_spec counter_spec (NestedOp 1 GetCount) exampleA (from_int 0)"
  by eval_example
    (metis callId.inject)


lemma "map_uw_spec counter_spec (NestedOp 1 GetCount) exampleB (from_int 2)"
  by eval_example

lemma "map_suw_spec counter_spec (NestedOp 1 GetCount) exampleB (from_int 2)"
  by eval_example

lemma "map_dw_spec counter_spec (NestedOp 1 GetCount) exampleB (from_int 2)"
  by eval_example

lemma "map_sdw_spec counter_spec (NestedOp 1 GetCount) exampleB (from_int 0)"
  by eval_example
    (metis callId.inject)




lemma "map_uw_spec counter_spec (NestedOp 1 GetCount) exampleC (from_int 1)"
  by eval_example

lemma "map_suw_spec counter_spec (NestedOp 1 GetCount) exampleC (from_int 2)"
  by eval_example
    (smt callId.inject)


lemma "map_dw_spec counter_spec (NestedOp 1 GetCount) exampleC (from_int 0)"
  by eval_example

lemma "map_sdw_spec counter_spec (NestedOp 1 GetCount) exampleC (from_int 0)"
  by eval_example
    (smt callId.inject)+



lemma "map_uw_spec counter_spec (NestedOp 1 GetCount) exampleD (from_int 0)"
  by eval_example
    (smt callId.inject)

lemma "map_suw_spec counter_spec (NestedOp 1 GetCount) exampleD (from_int 2)"
  by eval_example
    (smt callId.inject)


lemma "map_dw_spec counter_spec (NestedOp 1 GetCount) exampleD (from_int 0)"
  by eval_example
    (smt callId.inject)+

lemma "map_sdw_spec counter_spec (NestedOp 1 GetCount) exampleD (from_int 0)"
  by eval_example
    (smt callId.inject)+

subsection \<open>Struct example\<close>

text \<open>This is a struct with two fields: a counter and a set.\<close>

datatype val =
    I int
  | Bool bool
  | ListVal "val list"

instance val :: countable
  by countable_datatype

definition [simp]: "uniqueIds_val_r (x::val) = ({}::uniqueId set)" 

instantiation val :: valueType begin
definition [simp]: "uniqueIds_val \<equiv> uniqueIds_val_r"
definition [simp]: "default_val \<equiv> I 0"

instance by (standard, auto)
end

instantiation val :: from_bool begin
definition [simp]: "from_bool_val \<equiv> Bool"

instance by (standard, auto)
end

instantiation val :: from_int begin
definition [simp]: "from_int_val \<equiv> I"

instance by (standard, auto)
end

text_raw \<open>\DefineSnippet{struct_example1}{\<close>
datatype structOp = 
    A counterOp
  | B \<open>int setOp\<close>
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{struct_example2}{\<close>
definition crdtSpec :: "(structOp, val) crdtSpec" where
"crdtSpec \<equiv> (\<lambda>oper.
  case oper of
    A op \<Rightarrow> struct_field A (counter_spec op) 
  | B op \<Rightarrow> struct_field B (set_rw_spec op)
)"
text_raw \<open>}%EndSnippet\<close>


end
