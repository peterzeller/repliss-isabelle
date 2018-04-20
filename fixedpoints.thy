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



end