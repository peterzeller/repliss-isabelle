section "Topological Sorting"

theory topological_sort
  imports Main "HOL-Library.Multiset"
    "fuzzyrule.fuzzyrule"
begin


text "A list is sorted by a partial order, if no element in the list is followed by a smaller
element with respect to the relation."

definition sorted_by where
"sorted_by rel xs \<equiv> \<forall>i j. i<j \<longrightarrow> j<length xs \<longrightarrow> (xs!j,xs!i)\<notin>rel"

lemma sorted_by_empty:
"sorted_by R []"
  by (auto simp add: sorted_by_def)

lemma sorted_by_single:
"sorted_by R [x]"
  by (auto simp add: sorted_by_def)

lemma sorted_by_prepend_smallest:
  assumes "\<forall>y\<in>set xs. (y,x)\<notin>R"
    and "sorted_by R xs"
  shows "sorted_by R (x#xs)"
  using assms by (auto simp add: sorted_by_def nth_Cons split: nat.splits)

lemma sorted_by_sublist_left:
  assumes a: "sorted_by R (xs@ys)"
  shows "sorted_by R xs"
  using a by (auto simp add: sorted_by_def nth_append split: if_splits)

lemma sorted_by_sublist_right:
  assumes a: "sorted_by R (xs@ys)"
  shows "sorted_by R ys"
  using a by (auto simp add: sorted_by_def nth_append split: if_splits,
      metis add.commute add_diff_cancel_left' add_less_cancel_right add_less_same_cancel1 not_less_zero)

lemma sorted_by_append:
  assumes "sorted_by R (xs @ ys)"
      and c1: "x \<in> set xs"
      and c2: "y \<in> set ys"
    shows "(y, x) \<notin> R"
  using assms apply (auto simp add: sorted_by_def nth_append in_set_conv_nth split: if_splits)
  by (smt add_diff_cancel_left' add_diff_cancel_right' diff_le_self less_diff_conv less_le_trans not_add_less2)


lemma sorted_by_append_iff:
  shows "sorted_by R (xs@ys) \<longleftrightarrow> (sorted_by R xs \<and> sorted_by R ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. (y,x)\<notin>R))"
proof auto
  show "sorted_by R (xs @ ys) \<Longrightarrow> sorted_by R xs"
    using sorted_by_sublist_left by blast
  show "sorted_by R (xs @ ys) \<Longrightarrow> sorted_by R ys"
    using sorted_by_sublist_right by blast

  show "False"
    if c0: "sorted_by R (xs @ ys)"
      and c1: "x \<in> set xs"
      and c2: "y \<in> set ys"
      and c3: "(y, x) \<in> R"
    for  x y
    by (meson c0 c1 c2 c3 sorted_by_append)


  show "sorted_by R (xs @ ys)"
    if c0: "sorted_by R xs"
      and c1: "sorted_by R ys"
      and c2: "\<forall>x\<in>set xs. \<forall>y\<in>set ys. (y, x) \<notin> R"
    apply (auto simp add: sorted_by_def nth_append)
    using c0 sorted_by_def apply blast
    apply (simp add: c2)
    by (metis add_diff_inverse_nat c1 dual_order.strict_trans nat_add_left_cancel_less sorted_by_def)
qed

lemma sorted_by_cons_iff:
  shows "sorted_by R (x#xs) \<longleftrightarrow> (sorted_by R xs \<and> (\<forall>y\<in>set xs. (y,x)\<notin>R))"
  using sorted_by_append_iff[where R=R and xs="[x]" and ys="xs"]
  by (auto simp add: sorted_by_single)


text "For strict linear orders, @{term sorted_by} is the same as @{term sorted}:"

lemma sorted_by_eq_sorted:
"sorted_by {(x::'a::linorder,y). x < y} xs = sorted xs"
  by (induct xs, auto simp add: sorted_by_empty sorted_by_cons_iff)



fun top_sort where
  "top_sort R [] = []"
| "top_sort R (x#xs) = (
    let (greater, not_greater) = partition (\<lambda>y. R x y) xs in
    top_sort R not_greater @ x # top_sort R greater)"

value "top_sort (\<subset>) [{1,2,3}, {1}, {1}, {2,3,4}, {2}, {1,3::int}, {}]"

lemma top_sort_mset[simp]:
"mset (top_sort R xs) = mset xs"
proof (induct R xs rule: top_sort.induct)
  case (1 R)
  show "mset (top_sort R []) = mset [] "
    by simp
next
  case (2 R x xs)
  show " mset (top_sort R (x # xs)) = mset (x # xs)"
    using 2 by auto
qed

lemma top_sort_set[simp]:
"set (top_sort R xs) = set xs"
  by (metis set_mset_mset top_sort_mset)


lemma top_sort_sorts_irrefl:
  assumes trans: "trans {(x,y). R x y}"
    and irrefl: "irrefl {(x,y). R x y}"
  shows "sorted_by {(x,y). R x y} (top_sort R xs)"
using trans irrefl proof (induct R xs rule: top_sort.induct)
case (1 R)
  then show ?case 
    by (auto simp add: sorted_by_empty)
next
  case (2 R x xs)
  show ?case 
  proof (auto simp add: sorted_by_append_iff sorted_by_cons_iff)
    show "sorted_by {(x, y). R x y} (top_sort R (filter (Not \<circ> R x) xs))"
      by (simp add: 2)
    show "sorted_by {(x, y). R x y} (top_sort R (filter (R x) xs))"
      by (simp add: 2)
    show "\<And>y. \<lbrakk>y \<in> set xs; R x y; R y x\<rbrakk> \<Longrightarrow> False"
      by (metis "2.prems"(1) "2.prems"(2) case_prodI irrefl_def mem_Collect_eq trans_def)
    show "\<And>xa y. \<lbrakk>xa \<in> set xs; \<not> R x xa; y \<in> set xs; R x y; R y xa\<rbrakk> \<Longrightarrow> False"
      by (smt "2.prems"(1) case_prodD case_prodI mem_Collect_eq transE)
  qed
qed

lemma top_sort_sorts_distinct:
  assumes trans: "trans {(x,y). R x y}"
    and irrefl: "\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> R x y \<Longrightarrow> x\<noteq>y \<Longrightarrow> \<not>R y x"
    and distinct: "distinct xs"
  shows "sorted_by {(x,y). R x y} (top_sort R xs)"
using trans irrefl distinct proof (induct R xs rule: top_sort.induct)
case (1 R)
  then show ?case 
    by (auto simp add: sorted_by_empty)
next
  case (2 R x xs)
  have irrefl: "\<And>x y. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> R x y \<Longrightarrow> x\<noteq>y \<Longrightarrow> \<not>R y x"
    by (simp add: "2.prems"(2))

  show ?case 
  proof (auto simp add: sorted_by_append_iff sorted_by_cons_iff)
    show "sorted_by {(x, y). R x y} (top_sort R (filter (Not \<circ> R x) xs))"
      by (rule 2, insert "2.prems"(3) irrefl, auto simp add: "2.prems"(1))
    show "sorted_by {(x, y). R x y} (top_sort R (filter (R x) xs))"
      by (rule 2, insert "2.prems"(3) irrefl, auto simp add: "2.prems"(1))
    show "\<And>y. \<lbrakk>y \<in> set xs; R x y; R y x\<rbrakk> \<Longrightarrow> False"
      using "2.prems"(2) "2.prems"(3) by auto
    show "\<And>xa y. \<lbrakk>xa \<in> set xs; \<not> R x xa; y \<in> set xs; R x y; R y xa\<rbrakk> \<Longrightarrow> False"
      by (smt "2.prems"(1) case_prodD case_prodI mem_Collect_eq transE)
  qed
qed

lemma exists_sorted_by:
  assumes fin: "finite S"
    and trans: "trans R"
    and irrefl2: "\<And>x y. x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> x\<noteq>y \<Longrightarrow> (y,x)\<notin>R"
shows "\<exists>l. set l = S \<and> sorted_by R l"
proof -
  obtain ul where "set ul = S" and "distinct ul"
    using fin finite_distinct_list by auto

  have "sorted_by R (top_sort (\<lambda>x y. (x,y)\<in>R) ul)"
    by (fuzzy_rule top_sort_sorts_distinct; (simp add: trans `distinct ul`  \<open>set ul = S\<close> irrefl2)?)

  thus ?thesis
    by (metis \<open>set ul = S\<close> top_sort_set)
qed

lemma exists_sorted_by_irrefl:
  assumes fin: "finite S"
    and trans: "trans R"
    and irrefl: "irrefl R"
  shows "\<exists>l. set l = S \<and> sorted_by R l"
  by (meson exists_sorted_by fin irrefl irrefl_def local.trans transE)

lemma exists_sorted_by_antisym:
  assumes fin: "finite S"
    and trans: "trans R"
    and irrefl: "antisym R"
  shows "\<exists>l. set l = S \<and> sorted_by R l"
  by (meson antisym_def exists_sorted_by fin irrefl local.trans)



end