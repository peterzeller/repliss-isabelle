theory relations
  imports Main
begin

section \<open>Relations\<close>

text "Some useful lemmas and definitions about relations."

definition restrict_relation :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "|r"  110)
  where "r |r A \<equiv> r \<inter> (A \<times> A)"


definition downwardsClosure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"  (infixr "\<down>" 100)  where 
  "S \<down> R \<equiv> S \<union> {x | x y . (x,y)\<in>R \<and> y\<in>S}"

lemma downwardsClosure_in:
  "x \<in> S \<down> R \<longleftrightarrow> (x\<in>S \<or> (\<exists>y\<in>S. (x,y)\<in>R))"
  by (auto simp add: downwardsClosure_def)

lemma downwardsClosure_subset:
  "S \<down> R \<subseteq> S \<union> fst ` R"
  apply (auto simp add: downwardsClosure_in)
  using image_iff tranclD by fastforce

lemma downwardsClosure_subset2:
  "x \<in> S \<down> R \<Longrightarrow> x \<in> S \<union> fst ` R"
  by (meson downwardsClosure_subset subsetCE)

end
