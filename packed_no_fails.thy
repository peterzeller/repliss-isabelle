section "Packed Traces without Failures"
theory packed_no_fails
imports packed_traces ignore_fails
begin


text \<open>
 To show that a program is correct, we only have to consider packed transactions without crashes.
\<close>
text_raw \<open>\DefineSnippet{show_programCorrect_noTransactionInterleaving}{\<close>
theorem show_programCorrect_noTransactionInterleaving:
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>
      initialState program ~~ trace \<leadsto>* s; 
      packed_trace trace; 
      \<And>s. (s, ACrash) \<notin> set trace
    \<rbrakk> \<Longrightarrow> traceCorrect trace"
shows "programCorrect program"
text_raw \<open>}%EndSnippet\<close>


  unfolding programCorrect_def proof -
  text "We only have to consider traces without ACrash actions"
  show "\<forall>trace\<in>traces program. traceCorrect trace"
  proof (subst can_ignore_fails, clarsimp)
    text "Let tr be some trace such that program executes trace to s."
    fix tr
    assume is_trace: "tr \<in> traces program" 
      and noFail: "\<forall>s. (s, ACrash) \<notin> set tr"

    from is_trace 
    obtain s where steps: "initialState program ~~ tr \<leadsto>* s"
      by (auto simp add: traces_def)

    show "traceCorrect tr" 
    proof (rule ccontr)
      assume "\<not> traceCorrect tr"
      with noFail steps
      obtain tr'' s''
        where "initialState program ~~ tr'' \<leadsto>* s''" 
          and "packed_trace tr''"
          and "\<not>traceCorrect tr''"
          and "\<forall>s. (s, ACrash) \<notin> set tr''"
        using pack_incorrect_trace
        by blast 
      then show False
        using packedTracesCorrect by blast
    qed
  qed  
qed



end