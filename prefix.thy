section \<open>Prefixes\<close>

theory prefix
  imports Main
begin


text \<open>This Function describes that a list is a prefix of another list.\<close>

definition
  "isPrefix xs ys \<equiv> xs = take (length xs) ys"

lemma isPrefix_append:
  "isPrefix xs ys \<Longrightarrow> isPrefix xs (ys@zs)"
  using take_all by (fastforce simp add: isPrefix_def)

lemma isPrefix_refl: "isPrefix xs xs"
  by (simp add: isPrefix_def)

lemma isPrefix_empty: "isPrefix xs [] \<longleftrightarrow> xs = []"
  by (simp add: isPrefix_def)

lemma isPrefix_empty_first: "isPrefix [] xs"
  by (simp add: isPrefix_def)

lemma isPrefix_appendI:
  "isPrefix xs (xs@ys)"
  by (simp add: isPrefix_def)

lemma isPrefix_len:
  "isPrefix tr tr' \<Longrightarrow> length tr \<le> length tr'"
  by (metis isPrefix_def nat_le_linear take_all)

lemma isPrefix_trans:
  "isPrefix xs ys \<Longrightarrow> isPrefix ys zs \<Longrightarrow> isPrefix xs zs"
  by (auto simp add: isPrefix_def, metis length_take take_take)


lemma isPrefix_appendPrefix:
  "isPrefix (xs@ys) zs \<Longrightarrow> isPrefix xs zs"
  using isPrefix_appendI isPrefix_trans by blast

lemma isPrefix_subset:
  "isPrefix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (metis isPrefix_def set_take_subset)

lemma isPrefix_subset2:
  "isPrefix xs ys \<Longrightarrow> x\<in>set xs \<Longrightarrow> x\<in> set ys"
  using isPrefix_subset by auto




lemma isPrefix_same: 
  assumes "isPrefix tr tr'"
    and "i<length tr"
  shows "tr!i = tr'!i"
  using assms by (auto simp add: isPrefix_def, metis nth_take)


end