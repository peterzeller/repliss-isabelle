theory utils
  imports Main
begin


abbreviation todo ("???") where "??? \<equiv> undefined"

abbreviation eqsome :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<triangleq>" 69) where
  "x \<triangleq> y \<equiv> x = Some y"

abbreviation orElse :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "orElse" 70) where
  "x orElse y \<equiv> case x of Some a \<Rightarrow> a | None \<Rightarrow> y"

lemma iffI2: "\<lbrakk>A \<Longrightarrow> B; \<not>A \<Longrightarrow> \<not>B\<rbrakk> \<Longrightarrow> A \<longleftrightarrow> B"
  by auto

lemma if_cases:
  "\<lbrakk>c \<Longrightarrow> P t; \<not>c \<Longrightarrow> P f\<rbrakk> \<Longrightarrow>  P (if c then t else f)"
  by auto


lemma subset_h1: "X \<subseteq> Y \<Longrightarrow> \<forall>x. x\<in>X \<longrightarrow> x\<in>Y"
  by blast


lemma LeastI2:
  "\<lbrakk>x = (LEAST x::nat. P x); P y\<rbrakk> \<Longrightarrow> P x"
  by (simp add: LeastI)

lemma append_eq_conv_conj2: 
  "(xs = ys @ zs) \<longleftrightarrow> (take (length ys) xs = ys \<and> (drop (length ys) xs) = zs)"  for xs ys zs
  by (metis append_eq_conv_conj)


lemma cons_eq_conv_conj: 
  "(xs = y # ys) \<longleftrightarrow> (xs \<noteq> [] \<and> y = hd xs \<and> ys = tl xs)"  for xs ys zs
  by force

lemma hd_drop_conv_nth2:  "\<lbrakk>i<length xs; a = hd (drop i xs)\<rbrakk> \<Longrightarrow> xs ! i = a"
  by (simp add: hd_drop_conv_nth)      

lemma eq_tl: "\<lbrakk>xs \<noteq> []; \<And>a as. xs = a#as \<Longrightarrow> drop i ys = as\<rbrakk> \<Longrightarrow> drop i ys = tl xs"
  by (case_tac xs, auto)


lemma sumSplit:
  fixes f :: "nat \<Rightarrow> nat"
  shows "(\<Sum>i<x+y . f i) = (\<Sum>i<x . f i) + (\<Sum>i<y . f (x+i))"
  by (induct y, auto)




lemma usePropertyOfLeast:
  fixes x :: "'a :: wellorder"
  assumes wellDefined: "Q x"
    and weakerProperty: "\<And>x. Q x \<Longrightarrow> P x"
  shows "P (LEAST x. Q x)"
  using LeastI weakerProperty wellDefined by auto

lemma showIsLeast: 
  fixes x :: "'a :: wellorder"
  assumes "P x"
    and "\<And>y. P y \<Longrightarrow> x \<le> y"
  shows "x = (LEAST x. P x)"
  using Least_equality assms(1) assms(2) by auto

lemma nth_secondHalf_eq:
  assumes "i\<ge>length xs"
    and "length xs = length ys"
  shows "(xs@zs)!i = (ys@zs)!i"
  using assms by (auto simp add: nth_append)

lemma nth_append_second:
  "i \<ge> length xs \<Longrightarrow> (xs@ys)!i = ys!(i - length xs)"
  by (auto simp add:  nth_append split: if_splits)

lemma nth_cons_tail:
  "i > 0 \<Longrightarrow> (x#xs)!i = xs!(i - 1)"
  by (auto simp add:  nth_Cons split: nat.splits)

lemma nth_append_first:
  "i < length xs \<Longrightarrow> (xs@ys)!i = xs!i"
  by (auto simp add:  nth_append split: if_splits)


lemma show_appendEqH: 
  "\<lbrakk>n \<le> length ys; length xs \<ge> n; take n xs = take n ys; drop n xs = zs\<rbrakk> \<Longrightarrow> xs = (take n ys) @ zs"
  by (metis append_take_drop_id) 


definition max_natset :: "nat set \<Rightarrow> nat" where
  "max_natset S \<equiv> if S = {} then 0 else Suc (Max S)"

lemma max_natset_empty: "max_natset S = 0 \<longleftrightarrow> S = {}"
  by (simp add: max_natset_def)



lemma max_natset_Collect_Suc: 
  assumes "max_natset {x. P x} = Suc i"
    and "finite {x. P x}"
  shows "P i"
    and "\<And>j. P j \<Longrightarrow> j\<le>i"
  using assms  by (auto simp add: max_natset_def  split: if_splits,
      insert Max_in, blast)

lemma show_max_natset_smaller:
  assumes "i \<in> S"
    and "finite S"
    and "\<And>j. j\<in>S' \<Longrightarrow> j < i"
  shows "max_natset S' < max_natset S"
  using assms by (auto simp add: max_natset_def,
   metis Max_gr_iff Max_in all_not_in_conv bounded_nat_set_is_finite)

lemma show_max_natset_smaller_Collect:
  assumes "P i"
    and "finite {i. P i}"
    and "\<And>j. P' j \<Longrightarrow> j < i"
  shows "max_natset {i. P' i} < max_natset {i. P i}"
  by (rule show_max_natset_smaller, 
      insert assms, force+)


lemma finiteH: 
  "finite {x::nat. 0 < x \<and> x < A \<and> P x}"
  by simp



lemma exists_greatest:
  assumes example: "P j"
    and bounded: "\<And>j. P j \<Longrightarrow> j \<le> bound"
  shows "\<exists>j::nat. P j \<and> (\<forall>j'. P j' \<longrightarrow> j' \<le> j)"
  using example proof (induct "bound - j" arbitrary: j)
  case 0
  with bounded
  have "j = bound"
    by force
  then show ?case
    using "0.prems" bounded by blast 
next
  case (Suc i)
  then show ?case
    by (metis bounded bounded_Max_nat)
qed


lemma exists_greatest':
  assumes example: "\<exists>j. P j"
    and bounded: "\<exists>bound. \<forall>j. P j \<longrightarrow> j \<le> bound"
  shows "\<exists>j::nat. P j \<and> (\<forall>j'. P j' \<longrightarrow> j' \<le> j)"
  using bounded example exists_greatest by auto    

lemma split_take:
  assumes "ys = drop i xs"
  shows "xs = take i xs @ ys"
  by (simp add: assms)



lemma use_Greatest:
  assumes "\<exists>x. P x"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
  shows "P (GREATEST x::nat. P x)
\<and> (\<forall>y. P y \<longrightarrow> y \<le> (GREATEST x::nat. P x))"
  using GreatestI_nat Greatest_le_nat assms by auto

lemma Greatest_smaller:
  assumes "\<exists>x::nat. P x"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
    and "\<And>y. P y \<Longrightarrow> y < x"
  shows "Greatest P < x"
  using assms
  using GreatestI_nat by auto  

lemma Greatest_bigger:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P y"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
    and "x < y"
  shows "x < Greatest P"
proof -
  from \<open>P y\<close> have "\<exists>x. P x" by auto

  from use_Greatest[OF \<open>\<exists>x. P x\<close> \<open>\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound\<close>] assms
  show "x < Greatest P"
    by auto
qed

lemma nth_drop_if: 
"drop n xs ! i = (if n \<le> length xs then xs ! (n + i) else [] ! i)"
  by auto


lemma flip: "(\<not>Q \<Longrightarrow> \<not>P) \<Longrightarrow> P \<longrightarrow> Q"
  by auto

lemma in_dom:
  assumes "S \<subseteq> dom T" and "x \<in> S" 
  shows "\<exists>y. T x \<triangleq> y"
  using assms by blast



lemma in_img_simp: "y\<in>f`S \<longleftrightarrow> (\<exists>x\<in>S. f x = y)"
  by auto

definition "in_sequence xs x y \<equiv> \<exists>i j. i<j \<and> j<length xs \<and> xs!i = x \<and> xs!j=y "


lemma in_sequence_nil[simp]: "in_sequence [] = (\<lambda>x y. False)"
  apply (rule ext)+
  by (auto simp add: in_sequence_def)


lemma in_sequence_cons:
  "in_sequence (x # xs) a b \<longleftrightarrow> (x=a \<and> b\<in>set xs \<or> in_sequence xs a b)"
  apply (auto simp add: in_sequence_def)
    apply (metis (no_types, lifting) Suc_diff_eq_diff_pred Suc_less_eq Suc_pred gr_implies_not_zero not_gr_zero nth_Cons' zero_less_diff)
   apply (metis Suc_mono in_set_conv_nth nth_Cons_0 nth_Cons_Suc zero_less_Suc)
  by (meson Suc_mono nth_Cons_Suc)



lemma in_sequence_in1: "in_sequence xs x y \<Longrightarrow> x\<in>set xs"
  by (metis in_sequence_def in_set_conv_nth less_imp_le less_le_trans)


lemma in_sequence_in2: "in_sequence xs x y \<Longrightarrow> y\<in>set xs"
  by (metis in_sequence_def nth_mem)



end