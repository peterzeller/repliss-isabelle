theory doc
  imports "repliss_sem"
  "HOL-Library.OptionalSugar"
begin

section "Document Snippets"

text_raw "\\begin{comment} -- just some new notations"

notation (latex output)
  repliss_sem.step ("_  \<^latex>\<open>$\\xrightarrow{\\text{\<close> (\<open>unbreakable\<close>_) \<^latex>\<open>}}$\<close> (1_)")

text_raw "\\end{comment}"  
  

text \<open>
\DefineSnippet{local}{
  @{thm [display] local}
}%EndSnippet

\DefineSnippet{newId}{
  @{thm [display] newId}
}%EndSnippet

\DefineSnippet{beginAtomic}{
  @{thm [display] beginAtomic}
}%EndSnippet

\DefineSnippet{endAtomic}{
  @{thm [display] endAtomic}
}%EndSnippet

\DefineSnippet{dbop}{
  @{thm [display] dbop}
}%EndSnippet

\DefineSnippet{invocation}{
  @{thm [display] invocation}
}%EndSnippet

\DefineSnippet{return}{
  @{thm [display] return}
}%EndSnippet

\DefineSnippet{crash}{
  @{thm [display] crash}
}%EndSnippet

\DefineSnippet{invCheck}{
  @{thm [display] invCheck}
}%EndSnippet


\<close>




end