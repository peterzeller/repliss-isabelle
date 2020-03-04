section "Completeness"
theory completeness
  imports single_invocation_reduction
single_invocation_correctness
begin


lemma false_step_invarariant_false:
  assumes "S ~~ (i, a, False) \<leadsto>\<^sub>S S'"
  shows "\<not>invariant_all S' \<or> a = ALocal False"
  using assms by (auto simp add: step_s.simps)

lemma completeness_1:
  assumes step_s: "S ~~ (i, a, False) \<leadsto>\<^sub>S S'"
    and wf: "state_wellFormed S"
  shows "\<exists>tr. (initialState (prog S) ~~ tr \<leadsto>* S') \<and> (i,a) \<in> set tr" 
proof (cases a)
next
  case AEndAtomic
  with step_s
  have "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step_s.simps step.simps)
  obtain tr where "initialState (prog S) ~~ tr \<leadsto>* S"
    using local.wf state_wellFormed_def by blast

  with `S ~~ (i, a) \<leadsto> S'`
  have "initialState (prog S) ~~ tr@[(i,a)] \<leadsto>* S'"
    using wf state_wellFormed_def steps_step by blast

  thus ?thesis
    by auto
next
  case (AReturn r)
  with step_s
  have "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step_s.simps step.simps)
  obtain tr where "initialState (prog S) ~~ tr \<leadsto>* S"
    using local.wf state_wellFormed_def by blast

  with `S ~~ (i, a) \<leadsto> S'`
  have "initialState (prog S) ~~ tr@[(i,a)] \<leadsto>* S'"
    using wf state_wellFormed_def steps_step by blast

  thus ?thesis
    by auto
next
  case (AInvoc p)
  show ?thesis
  proof (rule ccontr)
    assume "\<nexists>tr. (initialState (prog S) ~~ tr \<leadsto>* S') \<and> (i, a) \<in> set tr "

    from AInvoc step_s
    show False
    proof (auto simp add: step_s.simps, fuzzy_goal_cases InvocStep)
      case (InvocStep initState impl S_invoc)
      
      have h1: "localState S_invoc i = None"
        by (simp add: InvocStep.invocationOp_eq2 InvocStep.state_wellFormed wf_localState_needs_invocationOp)

      have "\<And>x. x \<in> uniqueIds p \<Longrightarrow> x \<in> knownIds S_invoc"
        using InvocStep.less_eq by blast

      from h1 
      have "S_invoc ~~ (i,a) \<leadsto> S'"
        by (auto simp add: step.simps  InvocStep)

      from `state_wellFormed S_invoc`
      obtain tr1 where "initialState (prog S) ~~ tr1 \<leadsto>* S_invoc"
        using state_wellFormed_def ` prog S_invoc = prog S` by metis

      with `S_invoc ~~ (i,a) \<leadsto> S'`
      show ?case
        using \<open>\<nexists>tr. (initialState (prog S) ~~ tr \<leadsto>* S') \<and> (i, a) \<in> set tr\<close> steps_step by force
    qed
  qed
next
  case (ALocal ok)

  from ALocal `S ~~ (i, a, False) \<leadsto>\<^sub>S S'`
  have "ok = False"
    by (auto simp add: step_s.simps)

  from ALocal `S ~~ (i, a, False) \<leadsto>\<^sub>S S'` 
  have a: "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step_s.simps step.simps)

  obtain tr where b: "initialState (prog S) ~~ tr \<leadsto>* S"
    using local.wf state_wellFormed_def by blast

  with `S ~~ (i, a) \<leadsto> S'`
  have "initialState (prog S) ~~ tr@[(i, a)] \<leadsto>* S'"
    using steps_step by blast


  thus "?thesis"
    by auto
qed (insert assms, auto simp add: step_s.simps)


theorem completeness:
  assumes correct: "programCorrect program"
    and inv_init: "invariant_all (initialState program)"
  shows "programCorrect_s program"
proof (rule ccontr)
  assume "\<not> programCorrect_s program"
  from this
  obtain trace i S_final
    where "\<not> traceCorrect_s trace"
      and "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_final"
    by (auto simp add: programCorrect_s_def)


  from `\<not> traceCorrect_s trace`
  obtain tr1 a tr2
    where "trace = tr1 @ [(a, False)] @ tr2"
    by (auto simp add: traceCorrect_s_def dest: split_list)


  obtain S S' 
    where "initialState program ~~ (i, tr1) \<leadsto>\<^sub>S* S"
      and "S ~~ (i, a, False) \<leadsto>\<^sub>S S'" 
    using `initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_final` 
      and `trace = tr1 @ [(a, False)] @ tr2`
    by (auto simp add: steps_s_append_simp steps_s_cons_simp)

  have "state_wellFormed S"
    using \<open>initialState program ~~ (i, tr1) \<leadsto>\<^sub>S* S\<close> state_wellFormed_s_def state_wellFormed_s_to_wf by blast  

  have "prog S = program"
    using \<open>initialState program ~~ (i, tr1) \<leadsto>\<^sub>S* S\<close> prog_initial unchangedProg by fastforce


  from this obtain tr
    where "initialState program ~~ tr \<leadsto>* S'" and "(i,a) \<in> set tr"
    using \<open>S ~~ (i, a, False) \<leadsto>\<^sub>S S'\<close> \<open>state_wellFormed S\<close> completeness_1 by blast

  have "\<not>invariant_all S' \<or> a = ALocal False"
    using \<open>S ~~ (i, a, False) \<leadsto>\<^sub>S S'\<close> false_step_invarariant_false by blast

  thus False
  proof
    assume "\<not>invariant_all S'"

    hence "S' ~~ (i, AInvcheck False) \<leadsto> S'" 
      by (auto simp add: step.simps)

    with `initialState program ~~ tr \<leadsto>* S'`
    have "initialState program ~~ tr@[(i, AInvcheck False)] \<leadsto>* S'"
      using steps_step by blast

    have "\<not>traceCorrect (tr@[(i, AInvcheck False)])"
      by (simp add: actionCorrect_def traceCorrect_def)

    with `programCorrect program` and `initialState program ~~ tr@[(i, AInvcheck False)] \<leadsto>* S'`
    show False
      by (auto simp add: programCorrect_def traces_def)
  next 
    assume "a = ALocal False"

    hence "\<not>traceCorrect tr"
      using \<open>(i, a) \<in> set tr\<close> actionCorrect_def traceCorrect_def by fastforce

    with `programCorrect program` and `initialState program ~~ tr \<leadsto>* S'`
    show False
      by (auto simp add: programCorrect_def traces_def)
  qed
qed



end