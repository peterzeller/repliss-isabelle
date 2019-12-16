section "Various Utilities"

theory utils
  imports Main
    "HOL-Library.Monad_Syntax"
begin



text "This theory contains definition and Lemmas that could be in the standard library."

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
  by (cases xs, auto)


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


text "Like @{thm[mode=Rule] less_induct}, but reversed with an upper bound. 
We only need it for natural numbers, but it could probably be generalized.
"
lemma greater_induct [case_names greater]: 
  assumes  step: "\<And>x. \<lbrakk>\<And>y. \<lbrakk>y > x; y < bound\<rbrakk> \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P x" 
  shows "P (a::nat)"
proof (induct "bound - a" arbitrary: a  rule: less_induct)
  case less
  show "P a"
  proof (rule step)
    show "P y" if "a < y" and "y < bound" for y
    proof (rule less)

      show "bound - y < bound - a"
        using diff_less_mono2 dual_order.strict_trans that by blast
    qed
  qed
qed



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

lemma use_Greatest2:
  assumes "P x"
    and "\<forall>x. P x \<longrightarrow> x \<le> bound"
  shows "P (GREATEST x::nat. P x)
\<and> (\<forall>y. P y \<longrightarrow> y \<le> (GREATEST x::nat. P x))"
  by (rule use_Greatest, insert assms, auto)

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


text "Like @{thm[mode=Rule] less_induct}, but reversed with an upper bound. 
We only need it for natural numbers, but it could probably be generalized.
"
lemma greater_induct2 [case_names bounded greater]: 
  assumes "a < bound"  
    and  step: "\<And>x. \<lbrakk>\<And>y. \<lbrakk>y > x; y < bound\<rbrakk> \<Longrightarrow> P y; x < bound\<rbrakk> \<Longrightarrow> P x"
  shows "P (a::nat)"
  using `a < bound`
proof (induct "bound - a" arbitrary: a  rule: less_induct)
  case less
  show "P a"
  proof (rule step)
    show "P y" if "a < y" and "y < bound" for y
    proof (rule less)

      show "bound - y < bound - a"
        using diff_less_mono2 dual_order.strict_trans that by blast

      show " y < bound"
        by (simp add: that(2))
    qed

    show "a < bound"
      using less.prems by auto

  qed
qed

definition "is_bounded S bound \<equiv> \<forall>x\<in>S. x < bound"

lemma use_is_bounded:
  assumes "is_bounded S bound" and "x \<in> S"
  shows "x < bound"
  using assms is_bounded_def by blast


lemma min_set_induct[consumes 1, induct set: is_bounded, case_names empty step[not_empty bounded IH]]:
  fixes S :: "nat set"
  assumes bounded: "is_bounded S bound"
    and empty: "P {}"
    and step: "\<And>S. \<lbrakk>S \<noteq> {}; is_bounded S bound; (\<And>S'. \<lbrakk>S' \<noteq> {} \<Longrightarrow> Inf S' > Inf S; is_bounded S' bound\<rbrakk> \<Longrightarrow> P S')\<rbrakk> \<Longrightarrow> P S"
  shows "P S"
  using bounded
proof (induct "if S = {} then 0 else bound - (Inf S)" arbitrary: S rule: less_induct)
  case less
  show ?case 
  proof (cases "S = {}")
    case True
    then show ?thesis
      by (simp add: empty) 
  next
    case False
    show ?thesis 
    proof (rule step)  

      from ` S \<noteq> {}` obtain x where "x \<in> S"
        by blast

      moreover have "x < bound"
        using calculation less.prems use_is_bounded by blast

      ultimately have "Inf S < bound"
        by (meson False Inf_nat_def1 is_bounded_def less.prems)

      show "S \<noteq> {}"
        by (simp add: False)
      show "is_bounded S bound"
        using less.prems by blast

      show "P S'"
        if  c1: "S' \<noteq> {} \<Longrightarrow> Inf S < Inf S'"
          and c2: "is_bounded S' bound"
        for  S'
      proof (rule less)
        show "(if S' = {} then 0 else bound - Inf S') < (if S = {} then 0 else bound - Inf S)"
          by (auto simp add:  \<open>Inf S < bound\<close> \<open>S \<noteq> {}\<close> c1 diff_less_mono2)

        show "is_bounded S' bound"
          using c2 by blast
      qed
    qed  
  qed
qed

lemma forward_induct[case_names zero step[given broken bound]]:
  assumes init: "Q 0"
    and step: "\<And>i::nat. \<lbrakk>Q i; \<not>Q (Suc i);  i < bound\<rbrakk> \<Longrightarrow> \<exists>j>i. Q j "
  shows "\<exists>i\<ge>bound. Q i"
proof (rule ccontr, clarsimp)
  assume "\<forall>i\<ge>bound. \<not> Q i"
  hence bounded: "\<forall>y. Q y \<longrightarrow> y < bound"
    using not_le_imp_less by blast
  hence bounded2: "\<forall>y. Q y \<longrightarrow> y \<le> bound - 1"
    by auto



  from use_Greatest2[OF init bounded2]
  have "Q (GREATEST x. Q x)"
    and  "(\<forall>y. Q y \<longrightarrow> y \<le> (GREATEST x. Q x))"
    by auto


  from `Q (GREATEST x. Q x)`
  have "(GREATEST x. Q x) < bound"
    by (simp add: bounded)


  obtain i 
    where "Q i"
      and "\<forall>j>i. \<not>Q j"
      and "i < bound"
    using \<open>(GREATEST x. Q x) < bound\<close> \<open>Q (GREATEST x. Q x) \<and> (\<forall>y. Q y \<longrightarrow> y \<le> (GREATEST x. Q x))\<close> leD by auto



  have "\<exists>j>i. Q j"
    using `Q i` 
  proof (rule step)

    show "i < bound" using `i < bound` .

    show "\<not> Q (Suc i)"
      by (simp add: \<open>\<forall>j>i. \<not> Q j\<close>)
  qed

  thus False
    using \<open>\<forall>j>i. \<not> Q j\<close> by blast
qed





lemma show_Inf_smaller:
  assumes "(i::nat) \<in> S"
    and "\<And>i'. i'\<in>S' \<Longrightarrow> i < i'"
    and "S' \<noteq> {}"
  shows "Inf S < Inf S'"
  by (metis Inf_nat_def1 assms(1) assms(2) assms(3) bdd_above_bot cInf_less_iff empty_iff)


lemma rewrite_and_implies:
  shows "a \<and> b \<longrightarrow> c \<longleftrightarrow> a \<longrightarrow> b \<longrightarrow> c"
  by auto



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



definition restrict_relation :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "|r"  110)
  where "r |r A \<equiv> Restr r A" \<comment> \<open>This is a definition because Restr is just an abbreviation 
                                 and does not behave well when using methods like auto.\<close>

definition downwardsClosure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"  (infixr "\<down>" 100)  where 
  "S \<down> R \<equiv> S \<union> {x | x y . (x,y)\<in>R \<and> y\<in>S}"

lemma downwardsClosure_in:
  "x \<in> S \<down> R \<longleftrightarrow> (x\<in>S \<or> (\<exists>y\<in>S. (x,y)\<in>R))"
  by (auto simp add: downwardsClosure_def)

lemma downwardsClosure_subset:
  "S \<down> R \<subseteq> S \<union> fst ` R"
  by (auto simp add: downwardsClosure_in Domain.DomainI fst_eq_Domain)



lemma restrict_map_noop: "dom m \<subseteq> S \<Longrightarrow> m |` S = m"
   using domIff by (auto simp add: restrict_map_def intro!: ext, force)


lemma restrict_map_noop2[simp]: "m |` dom m = m"
  by (simp add: restrict_map_noop)

lemma restrict_relation_noop: "Field r \<subseteq> S \<Longrightarrow> r |r S = r"
  by (auto simp add: restrict_relation_def FieldI1 FieldI2 subset_h1)


text "A definition that is not automatically expanded:" 
definition Def (infix "::=" 50) where
"x ::= y \<equiv> x = y"

definition DefSome (infix "::\<triangleq>" 50) where
"x ::\<triangleq> y \<equiv> y = Some x"


lemma exists_nat_split: "(\<exists>n::nat. P n) \<longleftrightarrow> (P 0 \<or> (\<exists>n. P (Suc n)))"
  using zero_induct by blast



lemma infinite_if_mappable_to_nat:
  assumes mapping: "\<And>n::nat. \<exists>x\<in>S. f x \<ge> n"
  shows "infinite S"
proof auto
  assume "finite S"
  hence "finite (f ` S)"
    by force

  define m where "m \<equiv> Max (f ` S)"

  from mapping[where n="Suc m"] obtain x where
    "x\<in>S" and "f x \<ge> Suc m"
    by auto

  have "f x \<in> (f ` S)"
    using \<open>x \<in> S\<close> by blast

  have "f x > m"
    using Suc_le_eq \<open>Suc m \<le> f x\<close> by blast
  hence "f x > Max (f ` S)"
    using m_def by blast
  thus False
    using Max_ge \<open>f x \<in> f ` S\<close> \<open>finite (f ` S)\<close> leD by blast
qed


subsection "Well orders"

text "All types have an implicit well order that can be used when deterministically picking an 
arbitrary element from a set."

definition some_well_order :: "'a rel" where
 "some_well_order \<equiv> (SOME ord. well_order ord)"

lemma some_well_order_is_well_order: "well_order some_well_order"
  by (metis someI_ex some_well_order_def well_ordering)

lemma some_well_order_is_linear_order: "linear_order some_well_order"
  using some_well_order_is_well_order well_order_on_def by blast

lemma some_well_order_is_wo_rel: "wo_rel some_well_order"
  using some_well_order_is_well_order well_order_on_Well_order wo_rel_def by blast

lemma some_well_order_includes_all: "S \<subseteq> Field some_well_order"
  using some_well_order_is_well_order well_order_on_Field by fastforce


definition firstValue :: "'a \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> 'a" where
"firstValue d m \<equiv> if m = Map.empty then d else 
  let maxK = wo_rel.minim some_well_order (dom m) in
  the (m maxK)
  "


lemma firstValue_in_ran:
  assumes "finite (dom m)"
and not_default: "firstValue d m \<noteq> d"
shows "firstValue d m \<in> Map.ran m"
  using not_default proof (auto simp add: firstValue_def )
  assume "m \<noteq> Map.empty"
  have "(wo_rel.minim some_well_order (dom m)) \<in> dom m"
    by (simp add: \<open>m \<noteq> Map.empty\<close> some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)


  from this
  show "the (m (wo_rel.minim some_well_order (dom m))) \<in> ran m"
    by (meson domIff option.exhaust_sel ranI)
qed


subsection "Option Type"

text "We define some nicer syntax for working with options and maps."

lemma option_bind_def:
"(x \<bind> f) = (case x of None \<Rightarrow> None | Some a \<Rightarrow> f a)"
  by (metis bind.bind_lunit bind_eq_None_conv option.case_eq_if option.exhaust_sel)

definition map_chain ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" (infixr "\<ggreater>" 54) where
"(f \<ggreater> g) \<equiv> \<lambda>x. f x \<bind> g"

definition map_map ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" where
"(map_map f g) \<equiv> \<lambda>x. map_option g (f x)"

lemma dom_map_chain: 
"dom (f \<ggreater> g) = {x | x y z. f x \<triangleq> y \<and> g y \<triangleq> z}"
  by (auto simp add: map_chain_def option_bind_def split: option.splits)

lemma dom_map_map[simp]: 
"dom (map_map f g) = dom f"
  by (auto simp add: map_map_def)

lemma map_map_apply_eq_some[simp]:
"(map_map f g x \<triangleq> z) \<longleftrightarrow> (\<exists>y. f x \<triangleq> y \<and> g y = z)"
  by (auto simp add: map_map_def split: option.splits)

lemma map_map_apply_eq_none[simp]:
"(map_map f g x = None) \<longleftrightarrow> (f x = None)"
  by (auto simp add: map_map_def split: option.splits)


lemma map_map_apply:
"map_map f g x = (case f x of None \<Rightarrow> None | Some y \<Rightarrow> Some (g y))"
  by (auto simp add: map_map_def split: option.splits)



definition is_reverse :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
"is_reverse f_in f_out \<equiv> 
  (\<forall>x y. ((f_in x) \<triangleq> y) \<longrightarrow> (f_out y = x))
  \<and> (\<forall>x.  (f_in (f_out x)) \<triangleq> x)"

lemma is_reverse_1:
  assumes "is_reverse f_in f_out"
    and "f_in x \<triangleq> y"
  shows "f_out y = x"
  by (meson assms is_reverse_def)


lemma is_reverse_2:
  assumes "is_reverse f_in f_out"
  shows "f_in (f_out x) \<triangleq> x"
  by (meson assms is_reverse_def)


lemma is_reverse_combine:
  assumes is_rev: "is_reverse C_in C_out"
    and is_rev': "is_reverse C_in' C_out'"
    shows "is_reverse (C_in' \<ggreater> C_in) (C_out' \<circ> C_out)"
  by (smt bind_eq_Some_conv comp_apply is_rev is_rev' is_reverse_def map_chain_def)

lemma is_reverse_trivial: "is_reverse Some id"
  by (simp add: is_reverse_def)


subsection "Almost the Same"

text "Sometimes we want to express that two maps or relations are almost
the same (just on a subset)."

definition "map_same_on Cs op op' \<equiv> \<forall>c\<in>Cs. op c = op' c"
definition "rel_same_on Cs hb hb' \<equiv> \<forall>x\<in>Cs.\<forall>y\<in>Cs. (x,y)\<in>hb \<longleftrightarrow> (x,y)\<in>hb'"

lemma map_same_on_trivial[simp]:
"map_same_on Cs x x"
  by (simp add: map_same_on_def)

lemma rel_same_on_trivial[simp]:
"rel_same_on Cs x x"
  by (simp add: rel_same_on_def)





definition
"is_from x initial S \<equiv> if S = {} then x = initial else x \<in> S"

lemma is_from_exists:
  assumes "\<exists>x. x\<in>S"
  shows "is_from x initial S \<longleftrightarrow> x \<in> S"
  by (metis assms empty_iff is_from_def)

subsection "Minimums and Maximums"

text "A finite set with an acyclic order has minimal elements."

lemma exists_min:
  assumes fin: "finite S"
    and nonempty: "x\<in>S"
    and acyclic: "acyclic r"
  shows "\<exists>x. x\<in>S \<and> (\<forall>y\<in>S. \<not>(y,x)\<in>r)"
proof -
  have "wf (Restr r S)"
  proof (rule finite_acyclic_wf)
    show "finite (Restr r S)"
      using fin by simp 
    show "acyclic (Restr r S)"
      using acyclic by (meson Int_lower1 acyclic_subset) 
  qed

  show ?thesis
    by (smt IntI \<open>wf (Restr r S)\<close> mem_Sigma_iff nonempty wfE_min)
qed

text "A finite set with an acyclic order has maximal elements."

lemma exists_max:
  assumes fin: "finite S"
    and nonempty: "x\<in>S"
    and acyclic: "acyclic r"
  shows "\<exists>x. x\<in>S \<and> (\<forall>y\<in>S. \<not>(x,y)\<in>r)"
proof -

  have "\<exists>x. x\<in>S \<and> (\<forall>y\<in>S. \<not>(y,x)\<in>r\<inverse>)"
    using fin nonempty
  proof (rule exists_min)
    show "acyclic (r\<inverse>)"
      by (simp add: acyclic)
  qed
  thus ?thesis
    by simp
qed

subsection "Maps"

lemma ran_empty_iff[simp] :"(ran F = {}) \<longleftrightarrow> F = Map.empty"
  by (metis  empty_iff option.exhaust_sel ranI ran_empty)

lemma eq_map_empty[simp] :"(M = Map.empty) \<longleftrightarrow> (\<forall>x. M x = None)"
  by (rule fun_eq_iff)


subsection "Paths in Relations"

text "A list can be a path in a relation where subsequent elements are in relation."

definition is_path
  where "is_path path r \<equiv> (\<forall>i<length path - 1. (path!i, path!(Suc i))\<in>r)"

lemma is_path_empty[simp]:
  shows "is_path [] r"
  by (auto simp add: is_path_def)

lemma is_path_single[simp]:
  shows "is_path [x] r"
  by (auto simp add: is_path_def)

lemma is_path_cons:
  shows "is_path (x#y#xs) r \<longleftrightarrow> (x,y)\<in>r \<and> is_path (y#xs) r"
  using less_Suc_eq_0_disj by (auto simp add: is_path_def)

lemma is_path_cons2:
  shows "is_path (x#xs) r \<longleftrightarrow> (xs = [] \<or> (x,hd xs)\<in>r \<and> is_path xs r)"
  by (metis is_path_cons is_path_single list.collapse)



lemma is_path_append:
  assumes "xs \<noteq> []" and "ys \<noteq> []"
  shows
"is_path (xs@ys) r \<longleftrightarrow> is_path xs r \<and> (last xs, hd ys)\<in>r \<and> is_path ys r"
  using assms by (induct xs, auto simp add: is_path_cons2)




lemma is_path_trans_cl:
  shows "(x,y)\<in>r\<^sup>+ \<longleftrightarrow> (\<exists>path. length path > 1 \<and> is_path path r \<and> hd path = x \<and> last path = y)"
proof
  show "\<exists>path. 1 < length path \<and> is_path path r \<and> hd path = x \<and> last path = y" if "(x, y) \<in> r\<^sup>+"
    using that
  proof (induct)
    case (base y)
    show ?case 
    proof (intro conjI exI)
      show "hd [x,y] = x" by simp
      show "last [x, y] = y" by simp
      show "1 < length [x, y]" by simp
      show "is_path [x, y] r" by (auto simp add: is_path_def base)
    qed
  next
    case (step y z)
    from this
    obtain path 
      where "1 < length path"
        and "is_path path r"
        and "hd path = x"
        and "last path = y"
      by blast

    have "path \<noteq> []"
      using \<open>1 < length path\<close> by auto


    show ?case
    proof (intro conjI exI)
      show "hd (path @ [z]) = x" using `hd path = x` `path \<noteq> []` by simp
      show "1 < length (path @ [z])"  using \<open>1 < length path\<close> by auto 
      show "is_path (path @ [z]) r" using `is_path path r` `(y, z) \<in> r` apply (auto simp add: is_path_def nth_append)
        by (metis Suc_lessI \<open>last path = y\<close> \<open>path \<noteq> []\<close> diff_Suc_1 last_conv_nth)

      show "last (path @ [z]) = z" by simp
    qed
  qed

next
  assume "\<exists>path. 1 < length path \<and> is_path path r \<and> hd path = x \<and> last path = y"
  from this obtain path
    where "1 < length path"
      and "is_path path r"
      and "hd path = x"
      and "last path = y"
    by blast

  thus "(x, y) \<in> r\<^sup>+"
  proof (induct path arbitrary: x y rule: rev_induct)
    case Nil
    then show ?case by simp
  next
    case (snoc e path x y)
    show ?case
    proof (cases "1 < length path")
      case True
      have "(x, last path) \<in> r\<^sup>+"
        using `1 < length path`
      proof (rule snoc.hyps)
        show "is_path path r"
          by (metis True is_path_append less_numeral_extra(2) list.size(3) not_Cons_self2 snoc.prems(2))
        show "hd path = x"
          using True dual_order.strict_trans snoc.prems(3) by fastforce
        show "last path = last path" ..
      qed

      from `is_path (path @ [e]) r`
      have "(last path, e) \<in> r"
        by (metis One_nat_def True is_path_append length_greater_0_conv list.sel(1) not_Cons_self2 order.strict_trans zero_less_Suc)


      show "(x, y) \<in> r\<^sup>+"
        using \<open>(last path, e) \<in> r\<close> \<open>(x, last path) \<in> r\<^sup>+\<close> `last (path @ [e]) = y` by auto
    next
      assume "\<not> 1 < length path"
      hence "length path \<le> 1" by simp
      hence "length path = 1"
        using less_Suc_eq snoc.prems(1) by auto

      hence "(x,y)\<in>r"
        by (metis One_nat_def append_is_Nil_conv diff_Suc_1 hd_conv_nth is_path_def last_snoc length_append_singleton less_Suc_eq not_Cons_self nth_append_length snoc.prems(2) snoc.prems(3) snoc.prems(4))


      thus "(x, y) \<in> r\<^sup>+"
        by simp
    qed
  qed
qed



lemma acyclic_path:
"acyclic r \<longleftrightarrow> (\<nexists>path. length path > 1 \<and> is_path path r \<and> hd path = last path)"
  by (auto simp add: acyclic_def is_path_trans_cl)



lemma acyclic_union_disjoint:
  assumes "acyclic r"
    and "acyclic s"
    and "snd ` s \<inter> fst ` r = {}"
  shows "acyclic (r \<union> s)"
proof (auto simp add:  acyclic_path)
  fix path
  assume a0: "is_path path (r \<union> s)"
    and a1: "Suc 0 < length path"
    and a2: "hd path = last path"

 

  have all_following_in_s: 
    "(path!j, path!Suc j)\<in>s"
    if "(path!i, path!Suc i)\<in>s"
      and "j\<ge>i" 
      and "j < length path - 1"
      and "i < length path - 1"
    for i j
    using that
  proof (induct "j-i" arbitrary: j)
    case 0
    then show ?case 
      using `(path!i, path!Suc i)\<in>s`
      by auto
  next
    case (Suc n)
    have [simp]: "Suc (j - 1) = j"
      using Suc.hyps(2) by auto

    have [simp]: "Suc (j - Suc 0) = j"
      using Suc.hyps(2) by auto

    have "(path ! (j - 1), path ! Suc (j - 1)) \<in> s" 
    proof (rule Suc.hyps)
      show "n = j - 1 - i"
        using Suc.hyps(2) by auto
      show "i \<le> j - 1"
        using Suc.hyps(2) by linarith
      show "j - 1 < length path - 1"
        using Suc.prems less_imp_diff_less by blast
      show " i < length path - 1"
        using that by blast
      show " (path ! i, path ! Suc i) \<in> s"
        by (simp add: that)
    qed
    hence "path ! j \<in> snd ` s"
      by (simp add: rev_image_eqI)


    have "(path ! j, path ! Suc j) \<notin> r"
    proof (rule ccontr, simp)
      assume "(path ! j, path ! Suc j) \<in> r"
      hence "path ! j \<in> fst ` r"
        using image_iff by fastforce

      with \<open>snd ` s \<inter> fst ` r = {}\<close> \<open>path ! j \<in> snd ` s\<close>
      show False  by auto
    qed


    thus "(path ! j, path ! Suc j) \<in> s"
      by (meson Suc.prems Un_iff a0 is_path_def)
  qed

  have "(path!0, path!1)\<in>r"
  proof (rule ccontr)
    assume "(path ! 0, path ! 1) \<notin> r "
    hence "(path ! 0, path ! 1) \<in> s"
      by (metis One_nat_def Un_iff a0 a1 is_path_def zero_less_diff)
    have "is_path path s"
      apply (auto simp add: is_path_def)
      by (metis One_nat_def \<open>(path ! 0, path ! 1) \<in> s\<close> a1 all_following_in_s less_Suc0 not_le_imp_less not_less_iff_gr_or_eq zero_less_diff)
    thus False
      using `acyclic s`
      by (metis One_nat_def a1 a2 acyclic_path)
  qed


  obtain i 
    where "i < length path - 1"
      and "(path!i, path!Suc i)\<notin>r"
    apply (atomize_elim, rule ccontr)
    using `acyclic r` apply (auto simp add: acyclic_path)
    by (metis One_nat_def a1 a2 is_path_def)

  hence "(path!i, path!Suc i)\<in>s"
    by (meson Un_iff a0 is_path_def)

  hence "(path!(length path - 2),path!(Suc ((length path - 2))))\<in>s" 
  proof (rule all_following_in_s)
    show " i \<le> length path - 2"
      using \<open>i < length path - 1\<close> by linarith
    show "length path - 2 < length path - 1"
      by (simp add: a1 diff_less_mono2)
    show "i < length path - 1"
      using \<open>i < length path - 1\<close> by blast
  qed

  have "hd path \<in> fst ` r"
    by (metis One_nat_def \<open>(path ! 0, path ! 1) \<in> r\<close> a1 fst_conv hd_conv_nth image_iff list.size(3) not_one_less_zero)

  have "last path \<in> snd ` s"
    by (metis One_nat_def Suc_diff_Suc \<open>(path ! (length path - 2), path ! Suc (length path - 2)) \<in> s\<close> a1 image_iff last_conv_nth list.size(3) not_one_less_zero numeral_2_eq_2 snd_conv)


  from `hd path = last path` \<open>snd ` s \<inter> fst ` r = {}\<close>
  show "False"
    using \<open>hd path \<in> fst ` r\<close> \<open>last path \<in> snd ` s\<close>  by auto
qed

lemma acyclic_empty[simp]: "acyclic {}"
  by (simp add: wf_acyclic)

lemma acyclic_prod: "acyclic (A \<times> B) \<longleftrightarrow> A \<inter> B = {}"
  apply (auto simp add: acyclic_def)
  by (metis (no_types, lifting) SigmaD1 SigmaD2 disjoint_iff_not_equal tranclE)



  
lemma imp_assoc:
  shows "(a \<longrightarrow> (b \<longrightarrow> c)) \<longleftrightarrow> (b \<longrightarrow> (a \<longrightarrow> c))"
  by auto

lemma imp_assoc_elem:
  shows "(a \<longrightarrow> (x \<in> S \<longrightarrow> c)) \<longleftrightarrow> (x \<in> S \<longrightarrow> (a \<longrightarrow> c))"
  by auto

lemma rel_eqI:
  assumes lr: "\<And>x y. (x,y) \<in> A \<Longrightarrow> (x,y) \<in> B"
    and rl: "\<And>x y. (x,y) \<in> B \<Longrightarrow> (x,y) \<in> A"
  shows "A = B"
  using lr rl by auto



lemma min_nat_induct[case_names step[bound hyp]]:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "\<And>i. \<lbrakk>i<bound; \<And>j. j < i \<Longrightarrow> P j  \<rbrakk> \<Longrightarrow> P i"
  shows "\<forall>i<bound. P i"
  by (metis assms dual_order.strict_trans infinite_descent0 nat_neq_iff not_less_zero)



lemma fix_smallest_induct:
  assumes "P x"
and step: "\<And>x (i::nat). \<lbrakk>P x; \<And>j. j<i \<Longrightarrow> Q x j; \<not>Q x i; i < bound\<rbrakk> \<Longrightarrow> \<exists>x'. (\<forall>j\<le>i. Q x' j) \<and> P x'"
shows "\<exists>x'. (\<forall>i<bound. Q x' i) \<and> P x'"
proof (rule ccontr)
  assume a: "\<nexists>x'. (\<forall>i<bound. Q x' i) \<and> P x'  "



  obtain i x_i
    where i1: "P x_i"
      and i2: "\<forall>j<i. Q x_i j"
      and i3: "\<not>Q x_i i"
    by (metis a `P x` nat_less_induct)

  define indexes where "indexes \<equiv> {i. \<exists>x_i. P x_i \<and> (\<forall>j<i. Q x_i j) \<and> \<not>Q x_i i }"

  have "\<exists>i_max. i_max \<in> indexes \<and> (\<forall>y\<in>indexes. (i_max, y) \<notin> {(x,y). x < y})"
  proof (rule exists_max)
    show "finite indexes"
    proof (rule finite_subset)
      show "indexes \<subseteq> {i. i\<le>bound}"
        apply (auto simp add: indexes_def)
        by (metis (no_types, lifting) a dual_order.strict_trans le_eq_less_or_eq less_SucI not_less_eq_eq)
      show "finite {i. i \<le> bound}" by force
    qed
    show "acyclicP ((<) :: nat \<Rightarrow> nat => bool)"
      by (simp add: wf_acyclic wf_less)

    show "i \<in> indexes"
      using i1 i2 i3 by (auto simp add: indexes_def )
  qed

  from this obtain i_max 
    where "i_max \<in> indexes"
      and "(\<forall>y\<in>indexes. (i_max, y) \<notin> {(x,y). x < y})"
    by blast

  from this
  obtain  x_i_max
    where "P x_i_max"
      and "\<forall>j<i_max. Q x_i_max j"
      and "\<not>Q x_i_max i_max"
    by (auto simp add: indexes_def)


  from `(\<forall>y\<in>indexes. (i_max, y) \<notin> {(x,y). x < y})`
  have i_max_max: "\<forall>i'>i_max. \<forall>x'. \<not>(P x' \<and> (\<forall>j<i'. Q x' j) \<and> \<not>Q x' i')"
    by (auto simp add: indexes_def)


  have "\<exists>x'. (\<forall>j\<le>i_max. Q x' j) \<and> P x' "
    using `P x_i_max`
  proof (rule step)
    show "\<And>j. j < i_max \<Longrightarrow> Q x_i_max j"
      by (simp add: \<open>\<forall>j<i_max. Q x_i_max j\<close>)
    show "\<not> Q x_i_max i_max"
      by (simp add: \<open>\<not> Q x_i_max i_max\<close>)
    show "i_max < bound"
      by (metis \<open>P x_i_max\<close> \<open>\<forall>j<i_max. Q x_i_max j\<close> a dual_order.strict_trans linorder_neqE_nat)
  qed

  with i_max_max
  show False
    by (auto, smt a min_nat_induct not_le_imp_less)
qed



end