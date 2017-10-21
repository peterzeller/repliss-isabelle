theory prefix
  imports Main
begin

section {* Prefixes *}

text {* This Function describes that a list is a prefix of another list.  *}

definition
  "isPrefix xs ys \<equiv> xs = take (length xs) ys"

lemma isPrefix_append:
  "isPrefix xs ys \<Longrightarrow> isPrefix xs (ys@zs)"
  using take_all by (fastforce simp add: isPrefix_def)

lemma isPrefix_refl[simp]: "isPrefix xs xs"
  by (simp add: isPrefix_def)

lemma isPrefix_empty[simp]: "isPrefix xs [] \<longleftrightarrow> xs = []"
  by (simp add: isPrefix_def)

lemma isPrefix_appendI[simp]:
  "isPrefix xs (xs@ys)"
  by (simp add: isPrefix_def)

end