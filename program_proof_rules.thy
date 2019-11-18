theory program_proof_rules
  imports 
    invariant_simps 
    unique_ids
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language
begin

thm execution_s_correct_def
  (*
 execution_s_correct ?progr ?S ?i \<equiv> \<forall>trace S'. ?S ~~ (?i, trace) \<leadsto>\<^sub>S* S' \<longrightarrow> traceCorrect_s ?progr trace
*)

definition execution_s_check where
  "execution_s_check 
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  vis
  tx
  ls
 \<equiv> s_invocationOp i \<noteq> None
  \<and> (\<forall>trace S' x_ls x_cp x_vis x_txn x_txns x_gids. 
      let S  = \<lparr>
        calls = s_calls,
        happensBefore = s_happensBefore,
        callOrigin = s_callOrigin,
        transactionOrigin = s_transactionOrigin,
        knownIds = s_knownIds,
        invocationOp = s_invocationOp,
        invocationRes = s_invocationRes,
        prog = progr,
        transactionStatus = x_txns,
        generatedIds = x_gids,
        localState = x_ls(i \<mapsto> ls),
        currentProc = x_cp(i \<mapsto> toImpl),
        visibleCalls = x_vis(i \<mapsto> vis),
        currentTransaction = x_txn(i := tx)
      \<rparr>
      in (S ~~ (i, trace) \<leadsto>\<^sub>S* S') \<longrightarrow> traceCorrect_s progr trace)"


text "It is sufficient to check with execution_s_check to ensure that the procedure is correct:"

lemma execution_s_check_sound:
  assumes "localState S i \<triangleq> ls"
    and "visibleCalls S i \<triangleq> vis"
    and "localState S i \<triangleq> ls"
    and "prog S = progr"
    and "currentProc S i \<triangleq> toImpl"
    and c: "execution_s_check 
  progr 
  i
  (calls S)
  (happensBefore S)
  (callOrigin S)
  (transactionOrigin S)
  (knownIds S)
  (invocationOp S)
  (invocationRes S)
  vis
  (currentTransaction S i)
  ls"
  shows "execution_s_correct progr S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume a0: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  from c
  show "traceCorrect_s progr trace"
    by (auto simp add: execution_s_check_def, 
        smt a0 assms fun_upd_triv old.unit.exhaust state.surjective)
qed

lemma traceCorrect_s_empty: "traceCorrect_s progr [] "
  by (simp add: traceCorrect_s_def) 

lemma case_trace_not_empty:
  assumes  "\<And>a trace'. trace = a#trace' \<Longrightarrow> traceCorrect_s progr (a#trace')"
shows "traceCorrect_s progr trace"
using assms by (cases trace, auto simp add: traceCorrect_s_empty)

(*
lemma proof_rule_soundness:

  assumes "\<And>x v. \<lbrakk>P x v\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  (s_calls' x)
  (s_happensBefore' x)
  (s_callOrigin' x)
  (s_transactionOrigin' x)
  (s_knownIds' x)
  (s_invocationOp' x)
  (s_invocationRes' x)
  (vis' x)
  (tx' x)
  (cont v)"

shows"execution_s_check
  progr 
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  vis
  tx
  (A \<bind> cont)
"
*)

lemma 
  assumes "\<not>finite (Collect P)"
(* TODO add properties about uniqueness of v:
  - not in calls
  - not in ops/results
  - not known
  - not generated in current 
*)
and cont: "\<And>v. \<lbrakk>P v\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  vis
  tx
  (cont v)"

shows"execution_s_check
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  vis
  tx
  (newId P \<bind> cont)
"
proof -

  obtain v where "P v"
    using assms(1) infinite_imp_nonempty by auto

  from this and cont 
  have "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes vis tx   (cont v)"
    by blast


  from this
  obtain currentInvocationOp 
    where [simp]: "s_invocationOp i \<triangleq> currentInvocationOp"
    by (auto simp add: execution_s_check_def)

  show ?thesis

    apply (auto simp add: execution_s_check_def)

    apply (rule case_trace_not_empty)
    apply (auto simp add: steps_s_cons_simp)
    apply (erule step_s.cases)
          apply (auto split: if_splits)
    apply (smt Pair_inject cont execution_s_check_def insert_iff list.simps(15) traceCorrect_s_def)
    done
qed



end