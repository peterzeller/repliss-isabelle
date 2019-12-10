theory doc
imports "repliss_sem"
  "HOL-Libary.LaTeXsugar"
begin

text_raw "\\begin{comment} -- just some new notations"

notation (latex output)
  replissSem1.step ("_  \<^latex>\<open>$\\xrightarrow{\\text{\<close> _ \<^latex>\<open>}}$\<close> _")

abbreviation state_update_1 where
"state_update_1 C ls ids \<equiv> C\<lparr>localState :=ls, generatedIds := ids\<rparr>"

notation (latex output)
  state_update_1 ("_ \<^latex>\<open>[ } \\\\ \\mbox{ localState :=\<close>_ \<^latex>\<open>} \\\\ \\mbox{  generatedIds :=\<close>_ \<^latex>\<open> ]\<close>  ")

text_raw "\\end{comment}"  
  
text \<open>@{thm[mode=Rule] step.intros}


\<close>


end