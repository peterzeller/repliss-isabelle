theory doc
  imports "repliss_sem"
    "repliss_sem_single_invocation"
    "HOL-Library.OptionalSugar"
    unique_ids
begin

section "Document Snippets"


notation (tab output)
  "HOL.eq"  ("(_) = (1_)" [50,49] 50) and
  "Pure.eq"  ("(_) \<equiv> (1_)" [1,1] 2)


text \<open>
\DefineSnippet{local}{
  @{thm [display] repliss_sem.local}
}%EndSnippet

\DefineSnippet{newId}{
  @{thm [display] repliss_sem.newId}
}%EndSnippet

\DefineSnippet{beginAtomic}{
  @{thm [display] repliss_sem.beginAtomic}
}%EndSnippet

\DefineSnippet{endAtomic}{
  @{thm [display] repliss_sem.endAtomic}
}%EndSnippet

\DefineSnippet{dbop}{
  @{thm [display] repliss_sem.dbop}
}%EndSnippet

\DefineSnippet{invocation}{
  @{thm [display] repliss_sem.invocation}
}%EndSnippet

\DefineSnippet{return}{
  @{thm [display] repliss_sem.return}
}%EndSnippet

\DefineSnippet{crash}{
  @{thm [display] repliss_sem.crash}
}%EndSnippet

\DefineSnippet{invCheck}{
  @{thm [display] repliss_sem.invCheck}
}%EndSnippet


\<close>



text \<open>
\DefineSnippet{s_local}{
  @{thm [display] repliss_sem_single_invocation.local}
}%EndSnippet

\DefineSnippet{s_newId}{
  @{thm [display] repliss_sem_single_invocation.newId}
}%EndSnippet

\DefineSnippet{s_beginAtomic}{
  @{thm [display] repliss_sem_single_invocation.beginAtomic[unfolded atomize_all]}
}%EndSnippet

\DefineSnippet{s_endAtomic}{
  @{thm [display] repliss_sem_single_invocation.endAtomic}
}%EndSnippet

\DefineSnippet{s_dbop}{
  @{thm [display] repliss_sem_single_invocation.dbop}
}%EndSnippet

\DefineSnippet{s_invocation}{
  @{thm [display] repliss_sem_single_invocation.invocation[unfolded atomize_all]}
}%EndSnippet

\DefineSnippet{s_return}{
  @{thm [display] repliss_sem_single_invocation.return}
}%EndSnippet

\<close>

text \<open>
\DefineSnippet{traces}{
  @{thm [display] traces_def}
}%EndSnippet

\DefineSnippet{actionCorrect_def}{
  @{thm [display] actionCorrect_def}
}%EndSnippet

\DefineSnippet{traceCorrect}{
  @{thm [display] traceCorrect_def}
}%EndSnippet


\DefineSnippet{programCorrect}{
  @{thm [display] programCorrect_def}
}%EndSnippet


\<close>

schematic_goal getContext_def: "visibleCalls S i \<triangleq> vis \<Longrightarrow> getContext S i = ?x"
  unfolding getContextH_def
  by auto


text \<open>\DefineSnippet{getContext_def}{
  @{thm [display] getContext_def}
}%EndSnippet\<close>


text \<open>\DefineSnippet{getContext_def_prem}{
  @{thm [display] (prem 1) getContext_def}
}%EndSnippet\<close>


text \<open>\DefineSnippet{getContext_def_concl}{
  @{thm  [display] (concl) getContext_def}
}%EndSnippet\<close>


schematic_goal invariant_all_def: "invariant_all S = ?x"
  unfolding invContextH_def
  by simp

text \<open>\DefineSnippet{invariant_all_def}{
  @{thm [display] invariant_all_def}
}%EndSnippet\<close>

lemma committedCalls_def: "committedCalls S = {c. \<exists>tx. callOrigin S c \<triangleq> tx \<and> txStatus S tx \<triangleq> Committed}"
  unfolding committedCallsH_def isCommittedH_def
  by simp


text \<open>\DefineSnippet{committedCalls_def}{
  @{thm [display] committedCalls_def}
}%EndSnippet\<close>


text \<open>\DefineSnippet{traceCorrect_s_def}{
  @{thm [display] traceCorrect_s_def}
}%EndSnippet\<close>


text \<open>\DefineSnippet{programCorrect_s_def}{
  @{thm [display] programCorrect_s_def}
}%EndSnippet\<close>


text \<open>\DefineSnippet{steps_s_refl}{
  @{thm [display] steps_s_refl}
}%EndSnippet\<close>

text \<open>\DefineSnippet{steps_s_step}{
  @{thm [display] steps_s_step}
}%EndSnippet\<close>


text \<open>\DefineSnippet{state_monotonicGrowth_def}{
  @{thm [display] state_monotonicGrowth_def}
}%EndSnippet\<close>



text \<open>\DefineSnippet{program_wellFormed_def}{
  @{thm [display] program_wellFormed_def}
}%EndSnippet\<close>



text \<open>\DefineSnippet{invocations_cannot_guess_ids_def}{
  @{thm [display] invocations_cannot_guess_ids_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{invocations_cannot_guess_ids_def2}{
  @{thm [display] invocations_cannot_guess_ids_def2}
}%EndSnippet\<close>

text \<open>\DefineSnippet{invocation_cannot_guess_ids_def}{
  @{thm [display] invocation_cannot_guess_ids_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{trace_outputs_def}{
  @{thm [display] trace_outputs_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{action_outputs_simps}{
  @{thm [display] action_outputs.simps}
}%EndSnippet\<close>

text \<open>\DefineSnippet{trace_inputs_def}{
  @{thm [display] trace_inputs_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{action_inputs_simps}{
  @{thm [display] action_inputs.simps}
}%EndSnippet\<close>

text \<open>\DefineSnippet{queries_cannot_guess_ids_def}{
  @{thm [display] queries_cannot_guess_ids_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{query_cannot_guess_ids_def}{
  @{thm [display] query_cannot_guess_ids_def}
}%EndSnippet\<close>

text \<open>\DefineSnippet{queries_cannot_guess_ids_def2}{
  @{thm [display] queries_cannot_guess_ids_def2}
}%EndSnippet\<close>



end