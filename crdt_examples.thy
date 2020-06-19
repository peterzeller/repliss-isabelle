theory crdt_examples
  imports crdt_specs
begin

section "CRDT Examples"

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




end
