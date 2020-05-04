section "ZFC utilities"

theory ZFC_utils
  imports Main
    "ZFC_in_HOL.ZFC_Typeclasses"
begin



definition to_V :: "'a::embeddable \<Rightarrow> V" where
"to_V \<equiv> SOME f. inj f \<and> ((\<exists>(g::'a\<Rightarrow>V). inj g \<and> small (range g)) \<longrightarrow> small (range f))"

definition from_V :: "V \<Rightarrow> 'a::embeddable" where
"from_V \<equiv> the_inv to_V"


lemma to_V_property: "inj (to_V::'a::embeddable\<Rightarrow>V) \<and> ((\<exists>g::'a\<Rightarrow>V. inj g \<and> small (range g)) \<longrightarrow> small (range (to_V::'a::embeddable\<Rightarrow>V)))"
proof -

  have "\<exists>f::'a\<Rightarrow>V. inj f"
    using ex_inj by simp


  hence ex: "\<exists>f::'a\<Rightarrow>V. inj f \<and> ((\<exists>g::'a\<Rightarrow>V. inj g \<and> small (range g)) \<longrightarrow> small (range f))"
    by auto


  from someI_ex[OF ex, simplified to_V_def[symmetric]] [[show_sorts]]
  show "inj (to_V::'a\<Rightarrow>V) \<and> ((\<exists>g::'a\<Rightarrow>V. inj g \<and> small (range g)) \<longrightarrow> small (range (to_V::'a::embeddable\<Rightarrow>V)))"
    by auto
qed

lemma to_V_inj: "inj to_V"
  using to_V_property by auto


lemma to_V_use_inj: "to_V x = to_V y \<Longrightarrow> x = y"
  by (meson injD to_V_inj)


lemma from_V_rev[simp]: 
"from_V (to_V x) = x"
  by (simp add: from_V_def the_inv_f_f to_V_inj)

lemma to_V_small: "small (range (to_V::'a::small\<Rightarrow>V))"
  using to_V_property down small by auto 

lemma show_small_type_class:
  assumes "\<exists>V_of::'a\<Rightarrow>V. inj V_of \<and> small (range V_of)"
  shows "OFCLASS('a, small_class)"
  by (standard) (use assms in auto)

\<comment> \<open>TODO add methods to derive instances \<close>

end