theory extra
imports crdt_specs
begin

section \<open>Extra Material\<close>

text \<open>Some checks for the text.\<close>

lemma set_rw_spec_Contains:
(*and "trans (happensBefore ctxt)"
   and "irrefl (happensBefore ctxt)"
   and "Field (happensBefore ctxt) \<subseteq> dom (calls ctxt)"
   and "finite (dom (calls ctxt))" *)
  shows "\<exists>(ctxt::('a setOp, 'b::{from_bool}) operationContext) res.
set_rw_spec (Contains x) ctxt res
\<and>  res \<noteq> from_bool ((\<exists>a. Op ctxt a \<triangleq> Add x)
                           \<and> (\<forall>r. Op ctxt r \<triangleq> Remove x
                                \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x
                                 \<and> (r,a)\<in>happensBefore ctxt)))"
proof -
  define ctxt :: "('a setOp, 'b) operationContext" where 
    "ctxt = \<lparr>calls = (\<lambda>c. Some (Call (Add x) ???)),
    happensBefore = {(CallId x, CallId y) | x y. x < y}\<rparr>"

  show ?thesis
  proof (intro exI conjI)

    show "set_rw_spec (Contains x) ctxt (from_bool False)"
    proof (auto simp add: set_rw_spec_def set_spec_def flag_dw_spec_def intro!: arg_cong[where f=from_bool])
      assume "Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
        and "Disable \<notin> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)"
      have "latestOps (restrict_ctxt_op (set_to_flag x) ctxt) = {}"
        apply (auto simp add: latestOps_def restrict_ctxt_op_def restrict_ctxt_def ctxt_def restrict_hb_def Op_def fmap_map_values_def set_to_flag_def restrict_relation_def split: option.splits)
        by (metis callId.exhaust gt_ex)

      with `Enable \<in> latestOps (restrict_ctxt_op (set_to_flag x) ctxt)`
      show False
        by auto
    qed

    have no_remove: "Op ctxt r \<noteq> Some (Remove x)" for r
      by (auto simp add: ctxt_def Op_def)

    have "((\<exists>a. Op ctxt a \<triangleq> Add x) \<and>
        (\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)))"
    proof (intro conjI impI allI exI)
      show "Op ctxt (CallId 0) \<triangleq> Add x"
        by (simp add: Op_def ctxt_def)
    qed (simp add: no_remove)+

    thus "from_bool False \<noteq>
    from_bool
     ((\<exists>a. Op ctxt a \<triangleq> Add x) \<and>
      (\<forall>r. Op ctxt r \<triangleq> Remove x \<longrightarrow> (\<exists>a. Op ctxt a \<triangleq> Add x \<and> (r, a) \<in> happensBefore ctxt)))"
      using from_bool_eq_simp  by auto
  qed
qed

end