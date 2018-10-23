theory invariant_simps
  imports approach single_invocation_correctness
begin

section {* Invariant simplifications *}

text {* 
 This theory includes helpers for working with invariants.
*}


definition 
  "i_callOriginI_h callOrig transactionOrig \<equiv> \<lambda>c.
  case callOrig c of Some t \<Rightarrow> transactionOrig t | None \<Rightarrow> None"

lemma i_callOriginI_h_simp[simp]: "co c \<triangleq> t \<Longrightarrow> i_callOriginI_h co to c = to t"
  by (auto simp add: i_callOriginI_h_def)

lemma i_callOriginI_h_simp2: "i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) c \<triangleq> i"
  by auto


lemma i_callOriginI_h_simp_update_co:
  shows "i_callOriginI_h (co(c \<mapsto> t)) to c'
  = (if c = c' then to t else i_callOriginI_h co to c')"
  by (auto simp add: i_callOriginI_h_def split: option.splits)

lemma i_callOriginI_h_update_to:
  assumes "\<And>c. co c \<noteq> Some t"
  shows "i_callOriginI_h co (to(t \<mapsto> i)) c'
  = i_callOriginI_h co to c'"
  by (auto simp add: i_callOriginI_h_def  assms split: option.splits)

lemma i_callOriginI_h_update_to2:
  shows "i_callOriginI_h co (to(t \<mapsto> i)) c
  = (if co c \<triangleq> t then Some i else  i_callOriginI_h co to c)"
  by (auto simp add: i_callOriginI_h_def split: option.splits)

lemmas i_callOriginI_h_simps = i_callOriginI_h_simp_update_co i_callOriginI_h_update_to2

abbreviation 
  "i_callOriginI ctxt \<equiv> i_callOriginI_h (i_callOrigin ctxt) (i_transactionOrigin ctxt)"

text {* lifting the happensBefore relation on database-calls to the level of invocations. *}
definition 
  "invocation_happensBeforeH origin hb \<equiv> 
  {(ix,iy). (\<exists>c. origin c \<triangleq> ix) 
          \<and> (\<exists>c. origin c \<triangleq> iy) 
          \<and> ix \<noteq> iy
          \<and> (\<forall>cx cy. origin cx \<triangleq> ix
                 \<and> origin cy \<triangleq> iy
                 \<longrightarrow> (cx,cy)\<in>hb)}"

abbreviation 
  "invocation_happensBefore ctxt \<equiv> invocation_happensBeforeH (i_callOriginI ctxt) (happensBefore ctxt)"

lemma invocation_happensBeforeH_one_transaction_simp:
  assumes cs_nonempty: "cs \<noteq> []"
    and cs_distinct: "distinct cs"
    and co'_t: "\<forall>c\<in>set cs. co' c \<triangleq> t"
    and co_none: "\<forall>c\<in>set cs. co c = None"
    and co'_same: "\<And>c. c\<notin>set cs \<Longrightarrow> co' c = co c"
    and to_t: "to t = None"
    and i_fresh: "\<And>t. to t \<noteq> Some i"
    and t_fresh: "\<And>c. co c \<noteq> Some t"
    and wf_co_to: "\<And>c t. co c \<triangleq> t \<Longrightarrow> \<exists>i. to t \<triangleq> i"
    and wf_hb1: "\<And>c c'. (c,c')\<in>hb \<Longrightarrow> \<exists>t. co c \<triangleq> t"
    and wf_hb2: "\<And>c c'. (c,c')\<in>hb \<Longrightarrow> \<exists>t. co c' \<triangleq> t"
  shows "invocation_happensBeforeH (i_callOriginI_h co' (to(t \<mapsto> i))) (updateHb hb vis' cs)
                      = invocation_happensBeforeH (i_callOriginI_h co to) hb 
                        \<union> {i'. \<exists>t' c'. c' \<in> vis' \<and> co c' \<triangleq> t' \<and> to t' \<triangleq> i' \<and> (\<forall>c'' t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> i' \<longrightarrow> c'' \<in> vis' )} \<times> {i}"
proof (standard; standard; case_tac x; auto)
  fix x y
  assume a0: "(x, y) \<in> invocation_happensBeforeH (i_callOriginI_h co' (to(t \<mapsto> i))) (updateHb hb vis' cs)"
    and a1: "(x, y) \<notin> invocation_happensBeforeH (i_callOriginI_h co to) hb"

  from a0 obtain cx tx cy ty
    where cx: "co' cx \<triangleq> tx"
      and tx: "(to(t \<mapsto> i)) tx \<triangleq> x"
      and cy: "co' cy \<triangleq> ty"
      and ty: "(to(t \<mapsto> i)) ty \<triangleq> y"
      and "x \<noteq> y"
      and cx_before_cy: "(cx, cy) \<in> updateHb hb vis' cs"
    by (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: if_splits option.splits)

  have "tx \<noteq> ty" and "ty \<noteq> tx"
    using \<open>x \<noteq> y\<close> tx ty by auto

  have "cx \<noteq> cy" and "cy \<noteq> cx"
    using \<open>tx \<noteq> ty\<close> cx cy by auto


  {
    assume "x = i"
    hence "tx = t"
      using tx
      by (auto simp add: i_fresh split: if_splits )

    have "y \<noteq> i"
      using \<open>x = i\<close> \<open>x \<noteq> y\<close> by blast
    hence "ty \<noteq> t"
      using \<open>tx = t\<close> \<open>ty \<noteq> tx\<close> by auto

    hence "cy \<notin> set cs"
      using co'_t cy by auto

    from a1 `tx = t`
    have "(cx, cy) \<notin> hb"
      apply (auto simp add: invocation_happensBeforeH_def `x \<noteq> y`  i_callOriginI_h_def split: if_splits option.splits)
      apply (metis co'_same co_none cx option.distinct(1) t_fresh wf_hb1)
      apply (metis co'_same co_none cx option.simps(3) t_fresh wf_hb1)
      by (simp add: \<open>x = i\<close> i_fresh)

    with `(cx, cy) \<in> updateHb hb vis' cs`
    have False
      using \<open>cy \<notin> set cs\<close>  by (auto simp add:  updateHb_simp_distinct[OF `distinct cs`])

  }
  moreover
  {
    assume "y = i"
    hence "ty = t"
      by (metis fun_upd_apply i_fresh ty)

    have "x \<noteq> i"
      using \<open>y = i\<close> \<open>x \<noteq> y\<close> by blast
    hence "tx \<noteq> t"
      using \<open>ty = t\<close> \<open>ty \<noteq> tx\<close> by auto

    have "co cx \<triangleq> tx" 
      by (metis \<open>tx \<noteq> ty\<close> \<open>ty = t\<close> co'_same co'_t cx option.inject)
    moreover have "to tx \<triangleq> x" 
      using \<open>tx \<noteq> t\<close> tx by auto
    moreover have "cx \<in> vis'"
      by (metis \<open>ty = t\<close> calculation(1) co'_same co_none cx_before_cy cy option.distinct(1) t_fresh updateHb_simp1 wf_hb2)

    moreover have "(\<forall>c''. (\<exists>t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> x) \<longrightarrow> c'' \<in> vis')"
      using a0 \<open>y = i\<close>  apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits if_splits)
      apply (metis co'_same co_none domI domIff t_fresh updateHb_simp1 wf_hb2)
      using i_fresh by auto

    ultimately have " \<exists>t' c'. c' \<in> vis' \<and> co c' \<triangleq> t' \<and> to t' \<triangleq> x \<and> (\<forall>c''. (\<exists>t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> x) \<longrightarrow> c'' \<in> vis')" 
      by blast

  }
  moreover 
  {
    assume "x\<noteq>i" and "y \<noteq> i" 

    hence "tx \<noteq> t"
      using tx by auto

    have "ty \<noteq> t"
      using \<open>y \<noteq> i\<close> ty by auto

    have "cy \<notin> set cs"
      using \<open>ty \<noteq> t\<close> co'_t cy by auto


    from a0 a1
    have False
      using \<open>x \<noteq> i\<close>  \<open>y \<noteq> i\<close>  apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def \<open>x \<noteq> y\<close> updateHb_simp2 split: option.splits if_splits)
      apply (metis co'_same co'_t option.inject)
      using \<open>cy \<notin> set cs\<close> \<open>ty \<noteq> t\<close> co'_same cy ty apply auto[1]
      by (metis co'_same co_none option.distinct(1) to_t updateHb_simp2)
  }
  ultimately show  " \<exists>t' c'. c' \<in> vis' \<and> co c' \<triangleq> t' \<and> to t' \<triangleq> x \<and> (\<forall>c''. (\<exists>t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> x) \<longrightarrow> c'' \<in> vis')" 
    by blast

  show "y = i"
    using \<open>\<lbrakk>x \<noteq> i; y \<noteq> i\<rbrakk> \<Longrightarrow> False\<close> \<open>x = i \<Longrightarrow> False\<close> by blast
next
  fix x y
  assume a0: "(x, y) \<in> invocation_happensBeforeH (i_callOriginI_h co to) hb"

  show "(x, y) \<in> invocation_happensBeforeH (i_callOriginI_h co' (to(t \<mapsto> i))) (updateHb hb vis' cs)"
    using a0 apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)
    apply (metis co'_same co_none i_callOriginI_h_simp option.distinct(1) t_fresh)
    apply (metis co'_same co_none option.distinct(1) option.sel t_fresh)
    using i_fresh apply blast
    using i_fresh apply blast
    by (metis co'_same co'_t option.inject updateHb_simp2)

next
  fix i' t' c'
  assume a0: "to t' \<triangleq> i'"
    and a1: "co c' \<triangleq> t'"
    and a2: "\<forall>c''. (\<exists>t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> i') \<longrightarrow> c'' \<in> vis'"

  show "(i', i) \<in> invocation_happensBeforeH (i_callOriginI_h co' (to(t \<mapsto> i))) (updateHb hb vis' cs)"
    using a0 a1 a2 i_fresh apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)
    apply (metis co'_same co_none domI domIff option.sel t_fresh)
     apply (metis all_not_in_conv co'_t cs_nonempty option.inject set_empty)
    apply (auto simp add:  updateHb_simp_distinct[OF `distinct cs`])
    apply (metis co'_same co'_t option.inject)
    using co'_same t_fresh by fastforce
qed

lemma i_invocationOp_simps:
  "(i_invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes ) r \<triangleq> Op) \<longleftrightarrow> (state_invocationOp r \<triangleq> Op)"
  by (auto simp add: invContextH_def)

lemma invocation_happensBefore_simps:
  "((x,y) \<in> invocation_happensBefore (invContextH state_callOrigin state_transactionOrigin ts state_happensBefore cs ki io ir )) 
\<longleftrightarrow> ((\<exists>c t. state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> x) 
        \<and> (\<exists>c t.  state_callOrigin c \<triangleq> t \<and> state_transactionOrigin t \<triangleq> y) 
        \<and> (\<forall>cx tx cy ty. state_callOrigin cx \<triangleq> tx \<and> state_transactionOrigin tx \<triangleq> x
                 \<and> state_callOrigin cy \<triangleq> ty \<and> state_transactionOrigin ty \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>state_happensBefore))"
  apply auto                 
     apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def committedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
    apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def committedCallsH_def restrict_relation_def split: option.splits if_splits)[1]
   apply (auto simp add: invContextH_def invocation_happensBeforeH_def 
      i_callOriginI_h_def restrict_map_def committedCallsH_def restrict_relation_def split: option.splits if_splits)[1]   
    apply (drule_tac x=cx in spec)
    apply auto[1]
  oops


lemmas invariant_simps = 
  i_invocationOp_simps




lemma new_invocation_cannot_happen_before:
  assumes "state_wellFormed S'"
    and "invocationOp S' i = None"
  shows "(i,g) \<notin> invocation_happensBeforeH (i_callOriginI_h (callOrigin S') (transactionOrigin S')) (happensBefore S')"
proof (auto simp add: invocation_happensBeforeH_def)
  fix c ca
  assume a0: "\<forall>cx. i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> i \<longrightarrow> (\<forall>cy. i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> g \<longrightarrow> (cx, cy) \<in> happensBefore S')"
    and a1: "i_callOriginI_h (callOrigin S') (transactionOrigin S') c \<triangleq> i"
    and a2: "i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> g"

  from `state_wellFormed S'` `invocationOp S' i = None`
  have "transactionOrigin S' tx \<noteq> Some i" for tx
    by (simp add: wf_no_invocation_no_origin)


  with a1
  show "False"
    by (auto simp add:  i_callOriginI_h_def restrict_map_def split: option.splits if_splits)
qed

lemma new_invocation_cannot_happen_after:
  assumes "state_wellFormed S'"
    and "invocationOp S' i = None"
  shows "(g,i) \<notin> invocation_happensBeforeH (i_callOriginI_h (callOrigin S') (transactionOrigin S')) (happensBefore S')"
proof (auto simp add: invocation_happensBeforeH_def)
  fix c ca
  assume a0: "\<forall>cx. i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> g \<longrightarrow> (\<forall>cy. i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> i \<longrightarrow> (cx, cy) \<in> happensBefore S')"
    and a1: "i_callOriginI_h (callOrigin S') (transactionOrigin S') c \<triangleq> g"
    and a2: "i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> i"


  from `state_wellFormed S'` `invocationOp S' i = None`
  have "transactionOrigin S' tx \<noteq> Some i" for tx
    by (simp add: wf_no_invocation_no_origin)


  with a2
  show "False"
    by (auto simp add:  i_callOriginI_h_def restrict_map_def split: option.splits if_splits)
qed

schematic_goal checkCorrect2F_step:
  "\<lbrakk>b>0; ?F (checkCorrect2F ^^ (b - 1)) bot S\<rbrakk> \<Longrightarrow> (checkCorrect2F ^^ b) bot S"
  apply (case_tac b)
   apply simp
  apply (rule_tac t=b and s="Suc nat" in ssubst, assumption)
  apply (subst funpow.simps)
  apply (subst o_apply)
  apply (subst checkCorrect2F_def)
  apply (rule_tac t=nat and s="b - 1" in ssubst)
   apply simp
  apply assumption
  done


(*

  i_visibleCalls :: "callId set"
  i_callOrigin :: "callId \<rightharpoonup> txid"
  i_transactionOrigin :: "txid \<rightharpoonup> invocId"
  i_knownIds :: "'any set"
  i_invocationOp :: "invocId \<rightharpoonup> (procedureName \<times> 'any list)"
  i_invocationRes :: "invocId \<rightharpoonup> 'any"
*)

end