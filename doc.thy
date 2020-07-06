theory doc
  imports "repliss_sem"
    "repliss_sem_single_invocation"
    "HOL-Library.OptionalSugar"
begin

section "Document Snippets"



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
  @{thm [display] repliss_sem_single_invocation.beginAtomic}
}%EndSnippet

\DefineSnippet{s_endAtomic}{
  @{thm [display] repliss_sem_single_invocation.endAtomic}
}%EndSnippet

\DefineSnippet{s_dbop}{
  @{thm [display] repliss_sem_single_invocation.dbop}
}%EndSnippet

\DefineSnippet{s_invocation}{
  @{thm [display] repliss_sem_single_invocation.invocation}
}%EndSnippet

\DefineSnippet{s_return}{
  @{thm [display] repliss_sem_single_invocation.return}
}%EndSnippet

\<close>


text \<open>
\DefineSnippet{traces}{
  @{thm [display] traces_def}
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

end