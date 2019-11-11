theory single_invocation_correctness2
  imports single_invocation_correctness
    single_invocation_reduction
begin


lemma show_programCorrect_using_checkCorrect1:
  assumes initalStatesCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> invariant_all' S"
    and invInitial: "invariant_all' (initialState progr)"
   and stepsCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> \<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
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

lemma show_programCorrect_using_checkCorrect:
  assumes initialStatesCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates' progr i\<rbrakk> \<Longrightarrow> invariant_all' S"
    and invInitial: "invariant_all' (initialState progr)"
   and stepsCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates' progr i\<rbrakk> \<Longrightarrow> \<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
 shows "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect1)

  from invInitial
  show "invariant_all' (initialState progr)".

  from stepsCorrect
  show "\<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
    if c0: "S\<in>initialStates progr i"
    for  S i
    using initialStates'_same that by blast

  show "invariant_all' S"
    if c0: "S \<in> initialStates progr i"
    for  S i
    using initialStates'_same initialStatesCorrect that by blast
qed

end