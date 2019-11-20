theory single_invocation_correctness2
  imports single_invocation_correctness
    single_invocation_reduction
begin

text "Checks that a procedure with initial state S on invocation i is correct."

definition "execution_s_correct" where
"execution_s_correct progr S i \<equiv> \<forall>trace S'. (S ~~ (i, trace) \<leadsto>\<^sub>S* S') \<longrightarrow> traceCorrect_s trace"

definition "procedureCorrect" where
"procedureCorrect progr S i \<equiv> invariant_all' S \<and> execution_s_correct progr S i"

lemma show_program_correct_single_invocation:
  assumes initialCorrect: "\<And>S i. S\<in>initialStates program i \<Longrightarrow> invariant_all' S "
    and check: "\<And>S i. \<lbrakk>S\<in>initialStates program i; invariant_all' S; state_wellFormed S\<rbrakk> \<Longrightarrow> procedureCorrect program S i"
  shows "programCorrect_s program"
proof (auto simp add: programCorrect_s_def)
  fix trace i S_fin
  assume steps: "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"

  {
    fix a tr
    assume trace_def: "trace = a#tr"

    with steps
    obtain S_init 
      where step1: "initialState program ~~ (i, a) \<leadsto>\<^sub>S S_init"
        and steps': "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S_fin"
      using steps_s_cons_simp by blast

    find_theorems isAInvoc

    thm invocations_only_in_beginning[OF steps, where j=0, simplified]
    have "isAInvoc (fst (trace ! 0))"
    proof (rule invocations_only_in_beginning[OF steps, where j=0, simplified])
      show "state_wellFormed_s (initialState program) i"
        using state_wellFormed_s_def steps_s_refl by blast
      show "invocationOp (initialState program) i = None"
        by (simp add: initialState_def)
      show "trace \<noteq> [] "
        by (simp add: trace_def)
    qed
    from this
    obtain p invInitial where a_def: "a = (AInvoc p, invInitial)"
      by (cases a, auto simp add: trace_def isAInvoc_def split: action.splits)

    have invContext_same: "invContext S = invContext' S"  if  "S \<in> initialStates program i"  for S
      using initialState_noTxns1 initialStates_wellFormed invContext_same_allCommitted that by blast


    from initialCorrect[where i=i]
    have initialCorrect': "invariant progr (invContext S)" if "S \<in> initialStates program i" and "progr = prog S" for S progr
      using that invContext_same by fastforce 


    have "invariant_all' S_init"
    proof (rule initialCorrect[where i=i])
      show "S_init \<in> initialStates program i"
        using step1 and a_def apply (auto simp add: step_s.simps initialStates_def )
        by (auto simp add: state_ext prog_initial)
    qed

    with step1 and a_def
    have "invInitial"
    proof (auto simp add: initialState_def step_s.simps)
      fix initState impl S'
      assume a0: "a = (AInvoc p, False)"
        and a1: "invariant (prog S')          (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')            (invocationOp S'(i \<mapsto> p)) (invocationRes S'))"
        and a2: "procedure (prog S') p = (initState, impl)"
        and a3: "uniqueIds p \<subseteq> knownIds S'"
        and a4: "state_wellFormed S'"
        and a5: "\<forall>x. transactionStatus S' x \<noteq> Some Uncommitted"
        and a6: "invariant_all S'"
        and a7: "invocationOp S' i = None"
        and a8: "program = prog S'"
        and a9: "S_init = S'         \<lparr>localState := localState S'(i \<mapsto> initState), currentProc := currentProc S'(i \<mapsto> impl), visibleCalls := visibleCalls S'(i \<mapsto> {}),            invocationOp := invocationOp S'(i \<mapsto> p)\<rparr>"
        and a10: "\<forall>x. transactionOrigin S' x \<noteq> Some i"
        and a11: "\<not> invInitial"
        and a12: "\<not> invariant (prog S')             (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')               (invocationOp S'(i \<mapsto> p)) (invocationRes S'))"

      have "(invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')            (invocationOp S'(i \<mapsto> p)) (invocationRes S'))
          = (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')               (invocationOp S'(i \<mapsto> p)) (invocationRes S'))"
      proof (subst invContextH_same_allCommitted)
        show "invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')
     (invocationOp S'(i \<mapsto> p)) (invocationRes S') =
    invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S')
     (invocationOp S'(i \<mapsto> p)) (invocationRes S')"
          by auto

        show "\<And>c. (calls S' c = None) = (callOrigin S' c = None)"
          by (simp add: a4 wellFormed_callOrigin_dom3)

        show "\<And>c tx. callOrigin S' c \<triangleq> tx \<Longrightarrow> transactionStatus S' tx \<noteq> None"
          by (simp add: a4 wellFormed_state_callOrigin_transactionStatus)

        show "\<And>a b. (a, b) \<in> happensBefore S' \<Longrightarrow> calls S' a \<noteq> None"
          by (simp add: a4 wellFormed_happensBefore_calls_l)

        show "\<And>a b. (a, b) \<in> happensBefore S' \<Longrightarrow> calls S' b \<noteq> None"
          by (simp add: a4 wellFormed_happensBefore_calls_r)

        show "\<And>c. (transactionOrigin S' c = None) = (transactionStatus S' c = None)"
          by (simp add: a4 wf_transactionOrigin_and_status)

        show "\<And>t. transactionStatus S' t \<noteq> Some Uncommitted"
          using a5 by auto
      qed

      thus False
        using a1 a12 by auto
    qed


    have "S_init\<in>initialStates program i"
      using step1 by (auto simp add: step_s.simps initialStates_def a_def initialState_def; blast)


    { 
      assume "0 < length tr"
      have "traceCorrect_s  tr"
        by (meson \<open>S_init \<in> initialStates program i\<close> \<open>invariant_all' S_init\<close> assms(2) execution_s_correct_def initialStates_wellFormed procedureCorrect_def steps')
    } 
    moreover
    {
      assume "0 = length tr"
      have "traceCorrect_s  tr"
        using \<open>0 = length tr\<close> traceCorrect_s_def by force
    }
    ultimately have "traceCorrect_s  trace" 
      by (auto simp add: traceCorrect_s_def trace_def a_def \<open>invInitial\<close>, fastforce)
  }
  moreover 
  {
    assume "trace = []"
    then have "traceCorrect_s  trace" 
      by (simp add: traceCorrect_s_def)
  }
  ultimately
  show "traceCorrect_s  trace"
    using list.exhaust by blast
qed  


lemma show_programCorrect_using_checkCorrect1:
  assumes initalStatesCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> invariant_all' S"
    and invInitial: "invariant_all' (initialState progr)"
   and stepsCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> procedureCorrect progr S i"
 shows "programCorrect progr"
proof (rule show_correctness_via_single_session)
  show "invariant_all (initialState progr)"
    using invInitial
    by (auto simp add: invContext_same_allCommitted state_wellFormed_init transactionStatus_initial)



  show "programCorrect_s progr"
  proof (rule show_program_correct_single_invocation)

    show "invariant_all' S"
      if c0: "S \<in> initialStates progr i"
      for  S i
      using initalStatesCorrect that by auto

    show "\<And>S i. \<lbrakk>S \<in> initialStates progr i; invariant_all' S; state_wellFormed S\<rbrakk> \<Longrightarrow> procedureCorrect progr S i"
      by (simp add: stepsCorrect)


  qed
qed



lemma no_more_invoc:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and ls: "localState S i \<noteq> None"
    and wf: "state_wellFormed S"
  shows "(AInvoc p, t) \<notin> set trace"
proof -

  from ls have no_invoc: "invocationOp S (fst (i, trace)) \<noteq> None"
    by (simp add: wf wf_localState_to_invocationOp)


  have "(AInvoc p, t) \<notin> set (snd (i, trace))"
    using steps no_invoc
  proof (induct rule: steps_s.induct)
    case (steps_s_refl S s)
    then show ?case 
      by auto

  next
    case (steps_s_step S s tr S' a S'')
    then show ?case 
      by (auto simp add: step_s.simps has_invocationOp_forever)
  qed
  thus ?thesis
    by auto
qed

lemma local_state_None_no_more_steps:
assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
and "localState S i = None"
and "\<And>p t. (AInvoc p, t) \<notin> set trace"
shows "trace = []"
proof -
  have "snd (i,trace) = []" if  "localState S (fst (i,trace)) = None" and "\<And>p t. (AInvoc p, t) \<notin> set (snd (i,trace))"
    using steps that by (induct, auto simp add: step_s.simps steps_s_empty)
  thus ?thesis
    using assms by auto
qed


end