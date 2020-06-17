theory implication_subst
  imports Main
    "HOL-Eisbach.Eisbach"
    "fuzzyrule.fuzzyrule"
begin

section "Implication Subst"

text "Here we define a method to do subsitution with implications instead of equalities."


text "The theorem collection pos_cong includes theorems for rewriting.
Each of these theoremy has 2 assumptions.
The first one is the implication to use.
The left hand side of the implication should not contain any negations.
The second one represents the conclusion after rewriting."
named_theorems pos_cong


subsection "Quantifiers"

lemma implication_subst_exists[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> Q x"
    and "\<exists>x. P x"
  shows "\<exists>x. Q x"
  using assms  by blast

lemma implication_subst_not_exists[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> \<not>Q x"
    and "\<not>(\<exists>x. \<not>P x)"
  shows "\<not>(\<exists>x. Q x)"
  using assms  by blast

lemma implication_subst_forall[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> Q x"
    and "\<forall>x. P x"
  shows "\<forall>x. Q x"
  using assms  by blast

lemma implication_subst_not_forall[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> \<not>Q x"
    and "\<not>(\<forall>x. \<not>P x)"
  shows "\<not>(\<forall>x. Q x)"
  using assms  by blast



lemma implication_subst_bexists[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> Q x"
    and "\<exists>x\<in>S. P x"
  shows "\<exists>x\<in>S. Q x"
  using assms by blast

lemma implication_subst_not_bexists[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> \<not>Q x"
    and "\<not>(\<exists>x\<in>S. \<not>P x)"
  shows "\<not>(\<exists>x\<in>S. Q x)"
  using assms  by blast

lemma implication_subst_bforall[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> Q x"
    and "\<forall>x\<in>S. P x"
  shows "\<forall>x\<in>S. Q x"
  using assms  by blast

lemma implication_subst_not_bforall[pos_cong]: 
  assumes "\<And>x. P x \<Longrightarrow> \<not>Q x"
    and "\<not>(\<forall>x\<in>S. \<not>P x)"
  shows "\<not>(\<forall>x\<in>S. Q x)"
  using assms  by blast




subsection "Conjunction"

lemma implication_subst_conjl[pos_cong]:
  assumes "P \<Longrightarrow> Q"
 and "P \<and> A"
shows "Q \<and> A"
  using assms  by blast

lemma implication_subst_conjr[pos_cong]:
  assumes "P \<Longrightarrow> Q"
 and "A \<and> P"
shows "A \<and> Q"
  using assms  by blast

lemma implication_subst_not_conjl[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
 and "\<not>(\<not>P \<and> A)"
shows "\<not>(Q \<and> A)"
  using assms  by blast

lemma implication_subst_not_conjr[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
 and "\<not>(A \<and> \<not>P)"
shows "\<not>(A \<and> Q)"
  using assms  by blast

subsection "Double negation"

lemma implication_subst_neg[pos_cong]:
  assumes "P \<Longrightarrow> Q"
    and "P"
  shows "\<not>\<not>Q"
  using assms by auto

subsection "Implication"

lemma implication_subst_impl[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
    and "\<not>P \<longrightarrow> A"
  shows "Q \<longrightarrow> A"
  using assms by auto

lemma implication_subst_impr[pos_cong]:
  assumes "P \<Longrightarrow> Q"
    and "A \<longrightarrow> P"
  shows "A \<longrightarrow> Q"
  using assms by auto

lemma implication_subst_not_impl[pos_cong]:
  assumes "P \<Longrightarrow> Q"
    and "\<not>(P \<longrightarrow> A)"
  shows "\<not>(Q \<longrightarrow> A)"
  using assms by auto

lemma implication_subst_not_impr[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
    and "\<not>(A \<longrightarrow> \<not>P)"
  shows "\<not>(A \<longrightarrow> Q)"
  using assms by auto

subsection "Disjunction"


lemma implication_subst_disj_l[pos_cong]:
  assumes "P \<Longrightarrow> Q"
    and "P \<or> A"
  shows "Q \<or> A"
  using assms by auto

lemma implication_subst_r[pos_cong]:
  assumes "P \<Longrightarrow> Q"
    and "A \<or> P"
  shows "A \<or> Q"
  using assms by auto

lemma implication_subst_not_disj_l[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
    and "\<not>(\<not>P \<or> A)"
  shows "\<not>(Q \<or> A)"
  using assms by auto

lemma implication_subst_not_disj_r[pos_cong]:
  assumes "P \<Longrightarrow> \<not>Q"
    and "\<not>(A \<or> \<not>P)"
  shows "\<not>(A \<or> Q)"
  using assms by auto



method implication_subst_h uses r declares pos_cong = (
      rule r 
      | (rule pos_cong, implication_subst_h r: r, assumption))

method implication_subst uses r declares pos_cong =
  (implication_subst_h r: r pos_cong: pos_cong, (unfold not_not)?)


method implication_subst_fuzzy_h uses r declares pos_cong = (
      fuzzy_rule r 
      | (rule pos_cong, implication_subst_h r: r, assumption))

method implication_subst_fuzzy uses r declares pos_cong =
  (implication_subst_fuzzy_h r: r pos_cong: pos_cong, (unfold not_not)?)




end