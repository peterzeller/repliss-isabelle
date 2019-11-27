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


lemma domExists_simp: "x \<in> dom f \<longleftrightarrow> (\<exists>y. f x \<triangleq> y)"
  by (auto)


definition "before_in_list xs x y \<equiv> \<exists>i j. i < j \<and> j < length xs \<and> xs!i=x \<and> xs!j=y"

lemma before_in_list_def2:
  "before_in_list xs x y \<longleftrightarrow> (\<exists>xsa xsb. xs = xsa@xsb \<and> x\<in>set xsa \<and> y\<in>set xsb)"
  unfolding before_in_list_def
proof (intro iffI  conjI; elim exE conjE)

  show "\<exists>xsa xsb. xs = xsa @ xsb \<and> x \<in> set xsa \<and> y \<in> set xsb"
    if c0: "i < j"
      and c1: "j < length xs"
      and c2: "xs ! i = x"
      and c3: "xs ! j = y"
    for  i j
  proof (intro exI conjI)

    show "xs = take j xs @ drop j xs"
      by simp

    show "x \<in> set (take j xs)"
      using c0 c1 c2 in_set_conv_nth by fastforce
    show " y \<in> set (drop j xs)"
      by (metis Cons_nth_drop_Suc c1 c3 list.set_intros(1))
  qed

  show "\<exists>i j. i < j \<and> j < length xs \<and> xs ! i = x \<and> xs ! j = y"
    if c0: "xs = xsa @ xsb"
      and c1: "x \<in> set xsa"
      and c2: "y \<in> set xsb"
    for  xsa xsb
  proof -
    from c1 obtain i where "xsa ! i = x" and "i < length xsa"
      by (meson in_set_conv_nth)
    from c2 obtain j where "xsb ! j = y" and "j < length xsb"
      by (meson in_set_conv_nth)
    show ?thesis
    proof (intro exI conjI)
      show "i < length xsa +j"
        by (simp add: \<open>i < length xsa\<close> add.commute trans_less_add2)
      show "length xsa + j < length xs"
        by (simp add: \<open>j < length xsb\<close> c0)
      show " xs ! i = x"
        by (simp add: \<open>i < length xsa\<close> \<open>xsa ! i = x\<close> c0 nth_append_first)
      show "xs ! (length xsa + j) = y"
        by (simp add: \<open>xsb ! j = y\<close> c0)
    qed
  qed
qed




lemma before_in_list_cons:
  "before_in_list (x#xs) a b \<longleftrightarrow> (if x = a then b\<in>set xs else before_in_list xs a b )"
proof (auto simp add: before_in_list_def2)

  show "b \<in> set xs"
    if c0: "x = a"
      and c1: "a # xs = xsa @ xsb"
      and c2: "a \<in> set xsa"
      and c3: "b \<in> set xsb"
    for  xsa xsb
    using that by (metis Un_iff empty_iff empty_set list.sel(3) set_append tl_append2)

  show "\<exists>xsa xsb. a # xs = xsa @ xsb \<and> a \<in> set xsa \<and> b \<in> set xsb"
    if c0: "x = a"
      and c1: "b \<in> set xs"
  proof (intro exI conjI)
    show "a # xs = [a] @ xs" by simp
  qed (auto simp add: c1)


  show "\<exists>xsa xsb. xs = xsa @ xsb \<and> a \<in> set xsa \<and> b \<in> set xsb"
    if c0: "x \<noteq> a"
      and c1: "x # xs = xsa @ xsb"
      and c2: "a \<in> set xsa"
      and c3: "b \<in> set xsb"
    for  xsa xsb
  proof (intro exI conjI)
    show "xs = tl xsa @ xsb"
      by (metis c1 c2 equals0D list.sel(3) set_empty tl_append2)
    show "a \<in> set (tl xsa)"
      by (metis c0 c1 c2 hd_append list.collapse list.sel(1) set_ConsD tl_Nil)
  qed (simp add: c3)


  show "\<exists>xsaa xsba. x # xsa @ xsb = xsaa @ xsba \<and> a \<in> set xsaa \<and> b \<in> set xsba"
    if c0: "x \<noteq> a"
      and c1: "xs = xsa @ xsb"
      and c2: "a \<in> set xsa"
      and c3: "b \<in> set xsb"
    for  xsa xsb
  proof (intro exI conjI)
    show "x # xsa @ xsb = (x#xsa) @ xsb" by simp
  qed(auto simp add: that)
qed

lemma before_in_list_contains_l: "before_in_list cs x y \<Longrightarrow> x\<in>set cs"
  by (metis before_in_list_def dual_order.strict_trans in_set_conv_nth)

lemma  before_in_list_contains_r: "before_in_list cs x y \<Longrightarrow> y\<in>set cs"
  by (metis before_in_list_def in_set_conv_nth)


lemma before_in_list_empty[simp]: "\<not>before_in_list [] x y"
  by (simp add: before_in_list_def)


definition 
"map_update_all s_callOrigin localCalls tx \<equiv>  s_callOrigin ++ (Map.map_of (map (\<lambda>c. (c, tx)) localCalls))"

lemma map_update_all_empty[simp]: "map_update_all co [] t = co"
  by (simp add: map_update_all_def) 

lemma map_update_all_get: 
"map_update_all co cs tx c = (if c\<in>set cs then Some tx else co c)"
 using split_list by (auto simp add: map_update_all_def map_add_def  dest: map_of_SomeD split: option.splits, fastforce)

lemma map_update_all_None:
"map_update_all m xs y x = None \<longleftrightarrow> (x\<notin>set xs \<and> m x = None)"
  by (induct xs, auto simp add: map_update_all_def)

lemma map_update_all_Some_same:
"map_update_all m xs y x \<triangleq> y \<longleftrightarrow> (x\<in>set xs \<or> m x \<triangleq> y)"
  by (induct xs, auto simp add: map_update_all_def)

lemma map_update_all_Some_other:
  assumes "y' \<noteq> y"
  shows "map_update_all m xs y x \<triangleq> y' \<longleftrightarrow> (x\<notin>set xs \<and> m x \<triangleq> y')"
  using assms  by (induct xs, auto simp add: map_update_all_def)


lemma map_of_None: "map_of xs x = None \<longleftrightarrow> (\<forall>y. (x,y)\<notin>set xs)"
  by (induct xs, auto)
lemma map_of_Some: "\<lbrakk>distinct (map fst xs)\<rbrakk> \<Longrightarrow>  map_of xs x = Some y \<longleftrightarrow> ((x,y)\<in>set xs)"
  by (induct xs, auto, (metis map_of_eq_None_iff map_of_is_SomeI option.simps(3)))


lemma exists_cases1: 
  shows "(\<exists>x. (x = A \<longrightarrow> P x) \<and> (x \<noteq> A \<longrightarrow> Q x)) 
    \<longleftrightarrow>  (P A) \<or> (\<exists>x. x \<noteq> A \<and> Q x)"
  by auto

lemma exists_cases2: 
  shows "(\<exists>x. (x \<noteq> A \<longrightarrow> Q x) \<and> (x = A \<longrightarrow> P x)) 
    \<longleftrightarrow>  (P A) \<or> (\<exists>x. x \<noteq> A \<and> Q x)"
  by auto




end