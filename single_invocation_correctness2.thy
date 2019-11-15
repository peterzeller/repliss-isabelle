theory single_invocation_correctness2
  imports single_invocation_correctness
    single_invocation_reduction
begin

text "Checks that a procedure with initial state S on invocation i is correct."

definition "execution_s_correct" where
"execution_s_correct progr S i \<equiv> \<forall>trace S'. (S ~~ (i, trace) \<leadsto>\<^sub>S* S') \<longrightarrow> traceCorrect_s progr trace"

definition "procedureCorrect" where
"procedureCorrect progr S i \<equiv> invariant_all' S \<and> execution_s_correct progr S i"



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


    show "checkCorrect progr S i"
      if c0: "S \<in> initialStates progr i"
        and c1: "invariant_all' S"
        and c2: "state_wellFormed S"
      for  S i
      using c0 c1 checkCorrect_eq2' stepsCorrect
      using c2 initialState_noTxns1 invContext_same_allCommitted by fastforce 

  qed
qed


  assume "ct' \<equiv> \<lambda>pos name. (name, pos, []) # ct"
    and a1: "invariant_all' (initialState progr)"
    and a2: "\<And>S i. S \<in> initialStates' progr i \<Longrightarrow> procedureCorrect progr S i"
  show "programCorrect progr"
  proof (rule show_correctness_via_single_session)
    show "invariant_all (initialState progr)"
      using a1
      by (metis initialState_def invContext_same_allCommitted invariantContext.select_convs(1) invariantContext.select_convs(4) state_wellFormed_init transactionStatus_initial wellFormed_currentTransaction_back4 wellFormed_invoc_notStarted(1) wf_callOrigin_implies_transactionStatus_defined)

    show "programCorrect_s progr"
    proof (auto simp add: programCorrect_s_def)

      show "traceCorrect_s progr trace"
        if c0: "initialState progr ~~ (s, trace) \<leadsto>\<^sub>S* x"
        for  trace s x
        using a2



  show "programCorrect progr"
      if c0: "S \<in> initialStates' progr i \<Longrightarrow> procedureCorrect progr S i"
     for  S i



  thm show_correctness_via_single_session
  apply (auto simp add: procedureCorrect_def procedureCorrect_def)




end