theory fixedpoints
  imports Main
begin


lemma exists_maximal_element:
  fixes S :: "'a::complete_lattice set"
  assumes "finite S"
    and "S \<noteq> {}"
  shows "\<exists>max. max \<in> S \<and> (\<forall>v\<in>S. \<not>(v>max))"
  using \<open>finite S\<close> \<open>S \<noteq> {}\<close> proof (induct rule: finite_induct)
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
  then have ex_bigger: "\<exists>j\<ge>i. s j > s i" for i 
    using incr_seq by fastforce

  from \<open>finite (range s)\<close>
  obtain maxVal where "maxVal \<in> range s" and "\<forall>v\<in>range s. \<not>(v > maxVal)"
    by (metis exists_maximal_element finite.emptyI image_is_empty infinite_UNIV_nat)

  from ex_bigger
  obtain maxVal' where "maxVal' \<in> range s" and "maxVal' > maxVal"
    by (metis \<open>maxVal \<in> range s\<close> image_iff rangeI)

  then show False
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

\<comment> \<open>the function f only depends on finitely many values\<close>
definition finite_branching :: "(('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"finite_branching f \<equiv> \<forall>f' x. f f' x \<longrightarrow> (\<exists>S. finite S \<and> (\<forall>f''. (\<forall>x\<in>S. f'' x = f' x) \<longrightarrow> f f'' x))"


lemma 
  fixes f :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "(f ^^ i) bot x"
and "mono f"
shows "f ((f ^^ i) bot) x"
  by (metis (mono_tags, lifting) assms(1) assms(2) bot.extremum funpow_swap1 mono_def mono_pow rev_predicate1D)





datatype check_result = check_fail | check_ok nat | check_ok_infinite

definition [simp]: "less_eq_check_result' x y \<equiv> case x of 
   check_fail \<Rightarrow> True
 | check_ok n \<Rightarrow> (case y of check_fail \<Rightarrow> False | check_ok m \<Rightarrow> n \<le> m | check_ok_infinite \<Rightarrow> True)
 | check_ok_infinite \<Rightarrow> y = check_ok_infinite"

definition [simp]: "less_check_result' x y \<equiv> case x of 
   check_fail \<Rightarrow> y \<noteq> check_fail
 | check_ok n \<Rightarrow> (case y of check_fail \<Rightarrow> False | check_ok m \<Rightarrow> n < m | check_ok_infinite \<Rightarrow> True)
 | check_ok_infinite \<Rightarrow> False"

definition "is_ok check \<equiv> check \<noteq> check_fail"


instantiation check_result :: linorder begin
definition "less_eq_check_result \<equiv> less_eq_check_result'"
definition "less_check_result \<equiv> less_check_result'"


instance 
  by (standard, auto simp add: less_eq_check_result_def less_check_result_def split: check_result.splits)
end

lemma check_ok0_less: "x < check_ok 0 \<longleftrightarrow> x = check_fail"
  by (auto simp add: less_check_result_def split: check_result.splits)


instance check_result :: wellorder 
proof


  show "P a"
    if ind: "(\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x)"
    for P and a::check_result
  proof -
    have "P check_fail"
    proof (rule ind)
      show "\<And>y. y < check_fail \<Longrightarrow> P y"
        by (simp add: leD less_eq_check_result_def)
    qed

    moreover have "P (check_ok n)" for n
    proof (induct n rule: less_induct)
      case (less m)
      show "P (check_ok m)"
      proof (rule ind)
        show "P y" if "y < check_ok m" for y
        proof (cases y)
          case check_fail
          then show ?thesis
            using \<open>P check_fail\<close> by blast 
        next
          case (check_ok i)
          then show ?thesis
            using less.hyps less_check_result_def that by auto 
        next
          case check_ok_infinite
          then show ?thesis
            using less_check_result_def that by auto 
        qed
      qed
    qed

    moreover have "P check_ok_infinite"
    proof (rule ind)
      show "P y" if "y < check_ok_infinite" for y
      proof (cases y)
        case check_fail
        then show ?thesis
          using \<open>P check_fail\<close> by blast 
      next
        case (check_ok i)
        then show ?thesis
          by (simp add: \<open>\<And>n. P (check_ok n)\<close>)
      next
        case check_ok_infinite
        then show ?thesis
          using less_check_result_def that by auto 
      qed
    qed

    ultimately
    show "P a"
      by (case_tac a, auto)
  qed
qed






lemma "(LEAST a::'a::wellorder. a = x \<or> a = y) \<le> x"
  by (simp add: Least_le)


lemma least_check_fail: "A \<noteq> {} \<Longrightarrow> (LEAST x::check_result. x \<in> A) = check_fail \<longleftrightarrow> (check_fail \<in>A)"
  apply auto
  using LeastI apply force
  by (meson Least_le check_ok0_less le_less_trans)


lemma least_check_result: "A \<noteq> {} \<Longrightarrow> (LEAST x::check_result. x \<in> A) = y \<longleftrightarrow> (y\<in>A \<and> (\<forall>y'\<in>A. y \<le> y'))"
  apply auto
  apply (meson LeastI)
  apply (simp add: Least_le)
  by (metis (full_types) LeastI less_le not_less_Least)

lemma least_check_result': "x\<in>A \<Longrightarrow> (LEAST x::check_result. x \<in> A) = y \<longleftrightarrow> (y\<in>A \<and> (\<forall>y'\<in>A. y \<le> y'))"
  by (rule least_check_result, auto)

lemma least_check_result_less_eq: "P a \<Longrightarrow> (z \<le> (LEAST x::check_result. P x)) \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> z \<le> x)"
  by (meson LeastI Least_le order_trans)

lemma least_check_result_not_less_eq: "P a \<Longrightarrow> (\<not> (z \<le> (LEAST x::check_result. P x))) \<longleftrightarrow> (\<exists>x. P x \<and> z > x)"
  by (simp add: least_check_result_less_eq not_le)
  


lemma check_ok_infinite_max[simp]: "z \<le> check_ok_infinite"
  by (simp add: leI less_check_result_def)


lemma GreatestI:
  assumes example: "\<exists>m. P m \<and> Q m \<and> (\<forall>x. P x \<longrightarrow> x \<le> m)"
  shows "Q (Greatest P)"
  apply (unfold Greatest_def)
  apply (rule the1I2)
  using antisym example apply blast
  using dual_order.antisym example by blast



lemma GreatestI_nat2:
  assumes example: "\<exists>m::nat. P m"
    and bound: "\<forall>m. P m \<longrightarrow> m \<le> bound"
    and impl: "\<forall>x. P x \<longrightarrow> Q x"
  shows "Q (Greatest P)"
proof -
  obtain m where "P m"
    using example by auto

  then have "P (Greatest P)"
  proof (rule GreatestI_nat)
    show "\<forall>y. P y \<longrightarrow> y \<le> bound"
      using bound by simp
  qed
  then show "Q (Greatest P)"
    by (simp add: impl)
qed

thm GreatestI_nat

lemma check_fail_least[simp]: "check_fail \<le> x"
  by (simp add: less_eq_check_result_def)

lemma check_fail_least2[simp]: "x \<le> check_fail \<longleftrightarrow> x = check_fail"
  by (case_tac x, auto simp add: less_eq_check_result_def)

lemma check_inf_greatest[simp]: "x \<le> check_ok_infinite"
  by (case_tac x, auto simp add: less_eq_check_result_def)

lemma check_inf_greatest2[simp]: "check_ok_infinite \<le> x \<longleftrightarrow> x = check_ok_infinite"
  by (case_tac x, auto simp add: less_eq_check_result_def)

lemma check_ok_compare[simp]: "check_ok x \<le> check_ok y \<longleftrightarrow> x \<le> y"
  by (case_tac x, auto simp add: less_eq_check_result_def)

lemma GreatestI_check_result:
  assumes example: "\<exists>m::check_result. P m"
    and bound: "\<forall>m. P m \<longrightarrow> m \<le> check_ok bound"
  shows "P (Greatest P)"
proof (cases "\<exists>n. P (check_ok n)")
  case True
  from this obtain k where "P (check_ok k)" by force


  define P' where "P' \<equiv> (\<lambda>x. P (check_ok x))"

  have "P' (Greatest P')"
  proof (rule GreatestI_nat)
    show "P' k"
      by (simp add: P'_def \<open>P (check_ok k)\<close>)
    show "\<forall>y. P' y \<longrightarrow> y \<le> bound"
      using P'_def assms(2) less_eq_check_result_def by auto
  qed

  have "Greatest P = check_ok (Greatest P')"
  proof (subst Greatest_def, rule the_equality, auto)
    show " P (check_ok (Greatest P'))"
      using P'_def \<open>P' (Greatest P')\<close> by auto
    show "\<And>y. P y \<Longrightarrow> y \<le> check_ok (Greatest P')"
      apply (case_tac y, auto)
       apply (rule Greatest_le_nat[where b=bound])
      using bound by (auto simp add: P'_def )
    show "\<And>x. \<lbrakk>P x; \<forall>y. P y \<longrightarrow> y \<le> x\<rbrakk> \<Longrightarrow> x = check_ok (Greatest P')"
      by (simp add: \<open>P (check_ok (Greatest P'))\<close> \<open>\<And>y. P y \<Longrightarrow> y \<le> check_ok (Greatest P')\<close> eq_iff)
  qed

  then show "P (Greatest P)"
    using P'_def \<open>P' (Greatest P')\<close> by auto
next
  case False
  from bound
  have "\<not>P check_ok_infinite"
    using check_inf_greatest2 by blast

  with False
  have "P x \<longleftrightarrow> x = check_fail" for x
    using example apply (case_tac x, auto)
    by (case_tac xa, auto)

  then show ?thesis
    by (metis GreatestI2_order eq_refl)
qed



lemma GreatestI_check_result2:
  assumes example: "\<exists>m::check_result. P m"
    and bound: "\<forall>m. P m \<longrightarrow> m \<le> check_ok bound"
    and impl: "\<forall>x. P x \<longrightarrow> Q x"
  shows "Q (Greatest P)"
proof -
  obtain m where "P m"
    using example by auto

  from example
  have "P (Greatest P)"
  proof (rule GreatestI_check_result)
    show "\<forall>y. P y \<longrightarrow> y \<le> check_ok bound"
      using bound by simp
  qed
  then show "Q (Greatest P)"
    by (simp add: impl)
qed


lemma Greatest_leq:
  assumes example: "\<exists>m. P m \<and> (\<forall>x. P x \<longrightarrow> x \<le> m)"
    and Px: "P x"
  shows "x \<le> (Greatest P)"
  apply (unfold Greatest_def)
  apply (rule the1I2)
  using antisym example apply blast
  using Px by auto

lemma check_fail_smaller[simp]: "check_fail \<le> x"
  by (simp add: less_eq_check_result_def)

lemma check_ok_infinite_max'[simp]: "check_ok_infinite \<le> z \<longleftrightarrow> z = check_ok_infinite"
  by (simp add: dual_order.antisym)


lemma exists_greatest_check_result:
  assumes i_greatest:"\<forall>j>i. check_ok j \<notin> A"
and example: "a \<in> A"
shows "\<exists>m. m \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x \<le> m)"
proof (cases "check_ok_infinite \<in> A")
  case True
  then have "check_ok_infinite \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x \<le> check_ok_infinite)"
    by auto
  then show ?thesis ..
next
  case False
  show ?thesis
  proof (cases "\<exists>i'. check_ok i' \<in> A")
    case True
    then have exists_ok: "\<exists>m. check_ok m \<in> A \<and> m \<le> i"
      using i_greatest not_le_imp_less by blast

    show "\<exists>m. m \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x \<le> m)"
    proof (rule ccontr)
      assume a: "\<nexists>m. m \<in> A \<and> (\<forall>x. x \<in> A \<longrightarrow> x \<le> m)"

      obtain i_max where "check_ok i_max \<in> A" and "i_max \<le> i" and "\<forall>i'. check_ok i' \<in> A \<and> i' \<le> i \<longrightarrow> i' \<le> i_max"
        apply atomize_elim
        apply (rule_tac x="GREATEST i'. check_ok i' \<in> A \<and> i' \<le> i" in exI)
        apply auto
          apply (rule GreatestI_nat2[where bound=i])
            apply (auto simp add: exists_ok)
         apply (rule GreatestI_nat2[where bound=i])
           apply (auto simp add: exists_ok)
        apply (rule Greatest_le_nat[where b=i])
         apply (auto simp add: exists_ok)
        done

      with a show False
        apply auto
        apply (drule_tac x="check_ok i_max" in spec) 
        apply auto
        apply (case_tac x, auto)
        using i_greatest not_le_imp_less apply blast
        using False by blast
    qed
  next
    case False
    then show ?thesis
      by (metis check_ok_infinite_max check_result.exhaust check_result.simps(8) example less_eq_check_result'_def less_eq_check_result_def) 
  qed
qed



definition [simp]: "Inf_check_result' S \<equiv> if S = {} then check_ok_infinite else LEAST x. x \<in> S"
definition [simp]: "Sup_check_result' S  \<equiv> if S = {} then check_fail else if check_ok_infinite \<in> S \<or> (\<forall>i. \<exists>j>i. check_ok j \<in> S) then check_ok_infinite else GREATEST x. x \<in> S"




instantiation check_result :: complete_lattice begin
  definition "Inf_check_result \<equiv> Inf_check_result'"
  definition "Sup_check_result  \<equiv> Sup_check_result'"
  definition "bot_check_result \<equiv> check_fail"
  definition "sup_check_result (x::check_result) (y::check_result) \<equiv> if y \<le> x then x else y"
  definition "top_check_result \<equiv> check_ok_infinite"
  definition "inf_check_result (x::check_result) (y::check_result) \<equiv> if x \<le> y then x else y"
instance
proof

  fix x y z :: check_result
  show "inf x y \<le> x" and "inf x y \<le> y"
    by (auto simp add: inf_check_result_def less_eq_check_result_def split: check_result.splits)

  show "\<lbrakk>x \<le> y; x \<le> z\<rbrakk> \<Longrightarrow> x \<le> inf y z"
    by (auto simp add: inf_check_result_def less_eq_check_result_def split: check_result.splits)

  show "x \<le> sup x y" "y \<le> sup x y"
    by (auto simp add: sup_check_result_def less_eq_check_result_def split: check_result.splits)

  show "\<lbrakk>y \<le> x; z \<le> x\<rbrakk> \<Longrightarrow> sup y z \<le> x"
    by (auto simp add: sup_check_result_def less_eq_check_result_def split: check_result.splits)

  show "x \<in> A \<Longrightarrow> Inf A \<le> x" for A
    using Inf_check_result'_def Inf_check_result_def Least_le by fastforce

  show "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" for A
    by (auto simp add: Inf_check_result_def least_check_result_not_less_eq leD)

  show "x \<in> A \<Longrightarrow> x \<le> Sup A" for A
    apply (auto simp add: Sup_check_result_def )
    apply (erule_tac P="x \<le> (GREATEST x. x \<in> A)" in notE)
    apply (rule Greatest_leq)
    by (auto simp add: exists_greatest_check_result)



  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z" for A
    apply (auto simp add: Sup_check_result_def )
    using check_ok_infinite_max' apply blast
     apply (case_tac z)
       apply auto
    using check_ok_compare leD apply blast
    apply (erule_tac P=" (GREATEST x. x \<in> A) \<le> z" in notE)
    apply (case_tac z)
      apply auto
     apply (metis GreatestI_check_result check_fail_least2 le_cases)
    by (metis (full_types) GreatestI_check_result) 

qed (auto simp add: Inf_check_result_def top_check_result_def  Sup_check_result_def  bot_check_result_def)
end




\<comment> \<open>if result is false, result depends on a set S of recursive calls -- result is determined by checking conjunction of all recursive calls\<close>
definition tailrec :: "(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> bool" where
"tailrec F \<equiv> \<forall>g x. \<not>F g x \<longrightarrow> (\<exists>S. \<forall>g'. F g' x \<longleftrightarrow> (\<forall>x'\<in>S. g' x'))"

lemma tailrec_is_mono:
  assumes "tailrec f"
shows "mono f"
proof

  show "f x \<le> f y"
    if c0: "x \<le> y"
    for  x y
    using \<open>tailrec f\<close>
    by (smt le_fun_def order_refl tailrec_def that)
qed

find_theorems name: countable

definition even :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
"even g x \<equiv> if x = 0 then True else if x = 1 then False else g (x - 2)"

lemma f_mono: "mono even"
  by (smt even_def monoI predicate1I rev_predicate1D)


lemma "lfp even 0"
  by (subst lfp_unfold[OF f_mono], auto simp add: even_def)+

lemma "\<not>lfp even 1"
  by (subst lfp_unfold[OF f_mono], auto simp add: even_def)+

lemma "lfp even 10"
  by (subst lfp_unfold[OF f_mono], auto simp add: even_def)+







definition lfp2 :: "(('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)) \<Rightarrow> ('a \<Rightarrow> bool)" where
"lfp2 f \<equiv> (\<lambda>x. \<exists>n. (f^^n) bot x)"


lemma lfp2_leq_lfp:
  assumes mono: "mono f"
  shows "lfp2 f \<le> lfp f"
  by (meson iterate_to_lfp lfp2_def mono predicate1I)



end