theory fixedpoints
  imports Main
begin


lemma exists_maximal_element:
  fixes S :: "'a::complete_lattice set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>max. max \<in> S \<and> (\<forall>v\<in>S. \<not>(v>max))"
  using `finite S` `S \<noteq> {}` proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  show ?case 
  proof (cases "F = {}")
    case True
    then show ?thesis by simp
  next
    case False
    from this
    obtain F_max where "F_max \<in> F" and "\<forall>v\<in>F. \<not>(v > F_max)"
      using insert.hyps(3) by blast

    show ?thesis
    proof (cases "x > F_max")
      case True
      then show ?thesis
        by (metis \<open>\<forall>v\<in>F. \<not> F_max < v\<close> insert_iff le_less_trans less_le) 

    next
      case False
      then show ?thesis
        using \<open>F_max \<in> F\<close> \<open>\<forall>v\<in>F. \<not> F_max < v\<close> by blast 
    qed

  qed
qed


lemma exists_fixpoint:
  fixes s :: "nat \<Rightarrow> 'a::{complete_lattice}"
  assumes incr_seq: "\<And>i j. i\<le>j \<Longrightarrow> s i \<le> s j"
    and finite_range: "finite (range s)"
  shows "\<exists>i. \<forall>j\<ge>i. s j = s i"

proof (rule ccontr)
  assume "\<nexists>i. \<forall>j\<ge>i. s j = s i"
  hence ex_bigger: "\<exists>j\<ge>i. s j > s i" for i 
    using incr_seq by fastforce

  from `finite (range s)`
  obtain maxVal where "maxVal \<in> range s" and "\<forall>v\<in>range s. \<not>(v > maxVal)"
    by (metis exists_maximal_element finite.emptyI image_is_empty infinite_UNIV_nat)

  from ex_bigger
  obtain maxVal' where "maxVal' \<in> range s" and "maxVal' > maxVal"
    by (metis \<open>maxVal \<in> range s\<close> image_iff rangeI)

  thus False
    using \<open>\<forall>v\<in>range s. \<not> maxVal < v\<close> by blast
qed




lemma exists_fix1:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "mono f"
  shows "\<exists>i. (f ^^ Suc i) bot x = (f ^^ i) bot x"
  by (metis (mono_tags, lifting) assms funpow_decreasing le_Suc_eq rev_predicate1D)

lemma  exists_fix2:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "mono f"
  shows "\<exists>i. \<forall>j\<ge>i. (f ^^ j) bot x = (f ^^ i) bot x"
  by (metis (mono_tags, hide_lams) assms funpow_decreasing rev_predicate1D)

lemma iterate_to_lfp:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "mono f"
    and "(f ^^ i) bot x"
  shows "lfp f x"
  by (metis (mono_tags, lifting) Kleene_iter_lpfp assms(1) assms(2) lfp_greatest rev_predicate1D)

(* the function f only depends on finitely many values *)
definition finite_branching :: "(('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"finite_branching f \<equiv> \<forall>f' x. f f' x \<longrightarrow> (\<exists>S. finite S \<and> (\<forall>f''. (\<forall>x\<in>S. f'' x = f' x) \<longrightarrow> f f'' x))"


lemma 
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "(f ^^ i) bot x"
and "mono f"
shows "f ((f ^^ i) bot) x"
  by (metis (mono_tags, lifting) assms(1) assms(2) bot.extremum funpow_swap1 mono_def mono_pow rev_predicate1D)



lemma lfp_to_iterate:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono: "mono f"
    and finite_branching: "finite_branching f"
    and lfp_x: "lfp f x"
  shows "\<exists>i. (f ^^ i) bot x"
proof -


  from `lfp f x`
  have "f (lfp f) x"
    using def_lfp_unfold mono by fastforce

  with `finite_branching f`
  obtain S where "finite S" and "(\<forall>f''. (\<forall>x\<in>S. f'' x = lfp f x) \<longrightarrow> f f'' x)"
    by (metis finite_branching_def)

  from this
  show "\<exists>i. (f ^^ i) bot x"
  proof (induct arbitrary: x rule: finite_induct)
    case empty
    hence "f bot x"
      by simp
    hence "(f ^^ 1) bot x"
      by simp
    thus "\<exists>i. (f ^^ i) bot x"
      by blast
  next
    case (insert y A)
    then show ?case 





    oops
(*
definition lfp2 :: "(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> bool)" where
"lfp2 f \<equiv> SUP i. (f ^^ i) bot"


lemma lfp2_fixpoint:
  assumes mono: "mono f"
  shows "f (lfp2 f) = lfp2 f"
  apply (auto simp add: lfp2_def)
proof (rule antisym)
  show "(SUP i. (f ^^ i) bot) \<le> f (SUP i. (f ^^ i) bot)"
    using [[smt_solver=cvc4]]
    by (smt SUP_least Sup_le_iff assms bot_least funpow_swap1 monoD mono_def mono_pow order_refl order_trans range_eqI)

  show "f (SUP i. (f ^^ i) bot) \<le> (SUP i. (f ^^ i) bot)"



lemma lfp2_to_iterate:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes lfp_x: "lfp2 f x"
    and mono: "mono f"
  shows "\<exists>i. (f ^^ i) bot x"
  oops
*)

(*
definition lfp2 :: "(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> bool)" where
"lfp2 f \<equiv> \<lambda>x. \<exists>i. (f ^^ i) bot x"

lemma lfp2_to_iterate:
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes lfp_x: "lfp2 f x"
  shows "\<exists>i. (f ^^ i) bot x"
  by (meson lfp2_def lfp_x)




thm lfp_fixpoint

lemma lfp2_fixpoint:
  assumes "mono f"
  shows "f (lfp2 f) = lfp2 f"
  unfolding lfp2_def
proof (auto intro!: ext)


  show "\<exists>i. (f ^^ i) bot x"
    if c0: "f (\<lambda>x. \<exists>i. (f ^^ i) bot x) x"
    for  x

    sorry

  show "f (\<lambda>x. \<exists>i. (f ^^ i) bot x) x"
    if c0: "(f ^^ i) bot x"
    for  x i
    sorry
qed





lemma lfp2_unfold:
  assumes "mono f"
  shows "lfp2 f = f (lfp2 f)"
  by (simp add: assms lfp2_fixpoint)

*)


end