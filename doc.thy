theory doc
imports "repliss_sem"
begin

section "Document Snippets"

text_raw "\\begin{comment} -- just some new notations"

notation (latex output)
  repliss_sem.step ("_  \<^latex>\<open>$\\xrightarrow{\\text{\<close> (\<open>unbreakable\<close>_) \<^latex>\<open>}}$\<close> (1_)")

text_raw "\\end{comment}"  
  

 text \<open>
 \DefineSnippet{local}{
    @{thm [mode=Rule] local}
 }%EndSnippet

 \DefineSnippet{newId}{
    @{thm [mode=Rule] newId}
 }%EndSnippet

 \DefineSnippet{beginAtomic}{
    @{thm [mode=Rule] beginAtomic}
 }%EndSnippet

 \DefineSnippet{endAtomic}{
    @{thm [mode=Rule] endAtomic}
 }%EndSnippet

 \DefineSnippet{dbop}{
    @{thm [mode=Rule] dbop}
 }%EndSnippet

 \DefineSnippet{invocation}{
    @{thm [mode=Rule] invocation}
 }%EndSnippet

 \DefineSnippet{return}{
    @{thm [mode=Rule] return}
 }%EndSnippet

 \DefineSnippet{crash}{
    @{thm [mode=Rule] crash}
 }%EndSnippet

 \DefineSnippet{invCheck}{
    @{thm [mode=Rule] invCheck}
 }%EndSnippet


 \<close>




end