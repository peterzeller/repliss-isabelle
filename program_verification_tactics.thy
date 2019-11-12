theory program_verification_tactics
  imports 
    invariant_simps 
    unique_ids
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    "HOL-Eisbach.Eisbach"
begin

context begin
interpretation Labeling_Syntax .

lemma increase_bound:
  assumes "\<exists>bound. (checkCorrect2F ^^Suc bound) bot (progr, {}, S, i)"
  shows "\<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
  using assms by blast


lemma DC_show_programCorrect_using_checkCorrect:
  fixes ct defines "ct' \<equiv> \<lambda>pos name. (name, pos,[]) # ct"
  assumes invInitial: "C\<langle>Suc n1, ct' n1 ''invariant_initial_state'', n2: invariant_all' (initialState progr)\<rangle>"
    and initialStatesCorrect: "\<And>S i. \<lbrakk>H\<langle>ct' n2 ''in_initial_state'': S\<in>initialStates' progr i\<rangle>\<rbrakk> 
          \<Longrightarrow> C\<langle>Suc n2, ct' n2 ''at_procedure_begin'', n3: invariant_all' S\<rangle>"
    and stepsCorrect: "\<And>S i. \<lbrakk>H\<langle>ct' n3 ''in_initial_state'': S\<in>initialStates' progr i\<rangle>\<rbrakk> \<Longrightarrow> 
        C\<langle>Suc n3, ct' n3 ''check_procedure'', n4:  (\<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i))\<rangle>"
  shows "C\<langle>n1,ct,n4: programCorrect progr\<rangle>"
  using assms
  unfolding LABEL_simps using show_programCorrect_using_checkCorrect by blast

lemma DC_final:
  assumes "V\<langle>(''g'',inp,[]), ct: a\<rangle>"
  shows "C\<langle>inp,ct,Suc inp: a\<rangle>"
  using assms unfolding LABEL_simps by auto

end



end