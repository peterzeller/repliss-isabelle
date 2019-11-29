theory invariant_simps
  imports single_invocation_correctness "fuzzyrule.fuzzyrule"
begin

section \<open>Invariant simplifications\<close>

text \<open>
 This theory includes helpers for working with invariants.
\<close>


definition 
  "i_callOriginI_h callOrig transactionOrig \<equiv> \<lambda>c.
  case callOrig c of Some t \<Rightarrow> transactionOrig t | None \<Rightarrow> None"

lemma i_callOriginI_h_simp: "co c \<triangleq> t \<Longrightarrow> i_callOriginI_h co to c = to t"
  by (auto simp add: i_callOriginI_h_def)

lemma i_callOriginI_h_simp2: "i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) c \<triangleq> i"
  by (simp add: i_callOriginI_h_simp)


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

lemma i_callOriginI_h_update_to3:
  shows "i_callOriginI_h (map_update_all co cs t) (to(t \<mapsto> i)) c
  = (if c\<in>set cs then Some i else (if co c \<triangleq> t then Some i else i_callOriginI_h co to c))"
  by (auto simp add: i_callOriginI_h_def map_update_all_None map_update_all_Some_other map_update_all_Some_same split: option.splits)

lemma i_callOriginI_h_update_to4:
  "i_callOriginI_h (map_update_all co cs tx) to c = 
        (if c\<in>set cs then to tx else i_callOriginI_h co to c)" for co cs tx to
          by (auto simp add: i_callOriginI_h_def map_update_all_get split: option.splits)


lemmas i_callOriginI_h_simps = i_callOriginI_h_simp_update_co i_callOriginI_h_update_to2

abbreviation 
  "i_callOriginI ctxt \<equiv> i_callOriginI_h (callOrigin ctxt) (transactionOrigin ctxt)"

text \<open>lifting the happensBefore relation on database-calls to the level of invocations.\<close>
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
    and i_fresh: "\<And>c t. co c \<triangleq> t \<Longrightarrow>  to t \<noteq> Some i"
    and t_fresh: "\<And>c. co c \<noteq> Some t"
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
    then have "tx = t"
      using tx
      by (metis co'_same co'_t cx fun_upd_apply i_fresh option.inject)


    have "y \<noteq> i"
      using \<open>x = i\<close> \<open>x \<noteq> y\<close> by blast
    then have "ty \<noteq> t"
      using \<open>tx = t\<close> \<open>ty \<noteq> tx\<close> by auto

    then have "cy \<notin> set cs"
      using co'_t cy by auto

    from a1 \<open>tx = t\<close>
    have "(cx, cy) \<notin> hb"
      apply (auto simp add: invocation_happensBeforeH_def \<open>x \<noteq> y\<close>  i_callOriginI_h_def split: if_splits option.splits)
      apply (metis co'_same co_none cx option.distinct(1) t_fresh wf_hb1)
      apply (metis co'_same co_none cx option.simps(3) t_fresh wf_hb1)
      by (simp add: \<open>x = i\<close> i_fresh)

    with \<open>(cx, cy) \<in> updateHb hb vis' cs\<close>
    have False
      using \<open>cy \<notin> set cs\<close>  by (auto simp add:  updateHb_simp_distinct[OF \<open>distinct cs\<close>])

  }
  moreover
  {
    assume "y = i"
    then have "ty = t"
      by (metis co'_same co'_t cy i_fresh map_upd_Some_unfold option.inject ty)

    have "x \<noteq> i"
      using \<open>y = i\<close> \<open>x \<noteq> y\<close> by blast
    then have "tx \<noteq> t"
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
      by (metis co'_same co'_t i_fresh option.sel)

    ultimately have " \<exists>t' c'. c' \<in> vis' \<and> co c' \<triangleq> t' \<and> to t' \<triangleq> x \<and> (\<forall>c''. (\<exists>t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> x) \<longrightarrow> c'' \<in> vis')" 
      by blast

  }
  moreover 
  {
    assume "x\<noteq>i" and "y \<noteq> i" 

    then have "tx \<noteq> t"
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
    apply (auto simp add:  updateHb_simp_distinct[OF \<open>distinct cs\<close>])
       apply (metis co'_same co'_t option.inject)
    using co'_same t_fresh apply fastforce
    apply (metis co'_same co'_t option.sel)
    using co'_same t_fresh by fastforce
qed

lemma invocation_happensBeforeH_one_transaction_simp2:
  assumes cs_nonempty: "cs \<noteq> []"
    and cs_distinct: "distinct cs"
    and co_none: "\<forall>c\<in>set cs. co c = None"
    and to_t: "to t = None"
    and i_fresh: "\<And>c t. co c \<triangleq> t \<Longrightarrow>  to t \<noteq> Some i"
    and t_fresh: "\<And>c. co c \<noteq> Some t"
    and wf_hb1: "\<And>c c'. (c,c')\<in>hb \<Longrightarrow> \<exists>t. co c \<triangleq> t"
    and wf_hb2: "\<And>c c'. (c,c')\<in>hb \<Longrightarrow> \<exists>t. co c' \<triangleq> t"
  shows "invocation_happensBeforeH (i_callOriginI_h (map_update_all co cs t) (to(t \<mapsto> i))) (updateHb hb vis' cs)
      = invocation_happensBeforeH (i_callOriginI_h co to) hb 
        \<union> {i'. \<exists>c'. c' \<in> vis' \<and> i_callOriginI_h co to c' \<triangleq> i' \<and> (\<forall>c''. i_callOriginI_h co to c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis' )} \<times> {i}"
  using  cs_nonempty cs_distinct co_none to_t i_fresh  t_fresh  
proof (fuzzy_rule(noabs) invocation_happensBeforeH_one_transaction_simp)
  show "\<forall>c\<in>set cs. map_update_all co cs t c \<triangleq> t"
    by (simp add: map_update_all_get)
  show "\<And>c. c \<notin> set cs \<Longrightarrow> map_update_all co cs t c = co c"
    by (simp add: map_update_all_get)

  show "\<And>c c'. (c, c') \<in> hb \<Longrightarrow> \<exists>t. co c \<triangleq> t"
    using wf_hb1 by auto

  show "\<And>c c'. (c, c') \<in> hb \<Longrightarrow> \<exists>t. co c' \<triangleq> t"
    using wf_hb2 by auto

  show "(\<lambda>i'. \<exists>t' c'. c' \<in> vis' \<and> co c' \<triangleq> t' \<and> to t' \<triangleq> i' \<and> (\<forall>c'' t''. co c'' \<triangleq> t'' \<and> to t'' \<triangleq> i' \<longrightarrow> c'' \<in> vis')) =
    (\<lambda>i'. \<exists>c'. c' \<in> vis' \<and> i_callOriginI_h co to c' \<triangleq> i' \<and> (\<forall>c''. i_callOriginI_h co to c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis'))"
    by (auto simp add: i_callOriginI_h_def intro!:ext split: option.splits, blast)

  show "\<And>c t. co c \<triangleq> t \<Longrightarrow> co c \<triangleq> t"
    by simp


qed



lemma i_invocationOp_simps:
  "(invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes ) r \<triangleq> Op) \<longleftrightarrow> (state_invocationOp r \<triangleq> Op)"
  by (auto simp add: invContextH_def)



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

  from \<open>state_wellFormed S'\<close> \<open>invocationOp S' i = None\<close>
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


  from \<open>state_wellFormed S'\<close> \<open>invocationOp S' i = None\<close>
  have "transactionOrigin S' tx \<noteq> Some i" for tx
    by (simp add: wf_no_invocation_no_origin)


  with a2
  show "False"
    by (auto simp add:  i_callOriginI_h_def restrict_map_def split: option.splits if_splits)
qed





lemma updateHb_cases: 
  "(cx, cy) \<in> updateHb Hb vis cs \<longleftrightarrow> ((cx,cy)\<in>Hb \<or> cx\<in>vis \<and> cy\<in>set cs \<or> in_sequence cs cx cy)"
  by (induct cs arbitrary: Hb vis, auto simp add: updateHb_cons in_sequence_cons)



lemma i_callOriginI_h_update_simp:
  assumes "\<And>c. co c \<noteq> Some tx"
shows "(i_callOriginI_h (map_update_all co cs tx) (to(tx \<mapsto> i)))
       = map_update_all (i_callOriginI_h co to) cs i"
  using assms  by (auto simp add: i_callOriginI_h_def map_update_all_get  split: option.splits if_splits)




text "If there already are transactions in the current invocation, then adding a new transaction means
that we have to remove all i' that were previously after the current invocation.
There cannot be any new relations, since the first transaction already established all possible relations.
"

lemma invocation_happensBeforeH_more_transactions_simp2:
  assumes cs_nonempty: "cs \<noteq> []"
    and co_none: "\<forall>c\<in>set cs. co c = None"
    and i_old: "to old_t \<triangleq> i"
    and t_old: "co old_c \<triangleq> old_t"
    and t_fresh: "\<And>c. co c \<noteq> Some t" 
    and wf_hb1: "\<And>c c'. (c,c')\<in>hb \<Longrightarrow> \<exists>t. co c \<triangleq> t"

    and a7: "Field hb \<inter> set cs = {}"
    and a11: "\<And>c. i_callOriginI_h co to c \<triangleq> i \<Longrightarrow> c \<in> vis"
    and a13: "\<And>c c'. \<lbrakk>c' \<in> vis; (c,c')\<in>hb\<rbrakk> \<Longrightarrow> c \<in> vis "

  shows "invocation_happensBeforeH (i_callOriginI_h (map_update_all co cs t) (to(t \<mapsto> i))) (updateHb hb vis cs)
      = invocation_happensBeforeH (i_callOriginI_h co to) hb 
        - {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h co to) hb }" (is "?left = ?right")
proof -

  have "old_c \<in> vis"
    by (simp add: a11 i_callOriginI_h_simp i_old t_old)

  have not_refl_l: "(i1,i1)\<notin>?left" for i1
    by (auto simp add: invocation_happensBeforeH_def)

  have not_refl_r: "(i1,i1)\<notin>?right" for i1
    by (auto simp add: invocation_happensBeforeH_def)


  have h0: "(i1,i2)\<in>?left \<longleftrightarrow> (i1,i1)\<in>?right" if "i1=i2" for i1 i2
    by (auto simp add: invocation_happensBeforeH_def that)

  have ico_simp:
    "i_callOriginI_h (map_update_all co cs t) (to(t \<mapsto> i)) c
      = (if c\<in>set cs then Some i else i_callOriginI_h co to c)" for c
    by (auto simp add: i_callOriginI_h_def map_update_all_None map_update_all_get t_fresh split: option.splits)



  have h1: "(i',i) \<in> ?left \<longleftrightarrow> (i',i) \<in> ?right"
    if  "i' \<noteq> i"
    for i'
    apply (auto simp add: invocation_happensBeforeH_def ico_simp updateHb_cases)
        apply (metis i_callOriginI_h_simp i_old t_old)
       apply (auto simp add: i_callOriginI_h_def split: option.splits)
       apply (metis co_none domI domIff in_sequence_in2)
      apply (metis co_none domI domIff in_sequence_in2)
    using co_none apply auto[1]
    using \<open>old_c \<in> vis\<close> a13 i_old t_old by blast

  have h2: "(i,i') \<in> ?left \<longleftrightarrow> (i,i') \<in> ?right"
    if [simp]: "i' \<noteq> i"
    for i'
  proof
    show "(i,i') \<in> ?right" if "(i,i') \<in> ?left"
      using that
      apply (auto simp add: invocation_happensBeforeH_def ico_simp updateHb_cases)
         apply (metis i_callOriginI_h_simp i_old t_old)
        apply (auto simp add: i_callOriginI_h_def split: option.splits if_splits)
         apply (metis co_none domI domIff in_sequence_in2)
      using co_none in_sequence_in2 wf_hb1 apply fastforce
       apply (metis FieldI1 a7 disjoint_iff_not_equal in_sequence_in2)
      by (metis all_not_in_conv co_none cs_nonempty in_sequence_in2 option.simps(3) set_empty wf_hb1)

    show "(i,i') \<in> ?left" if "(i,i') \<in> ?right"
      using that by (auto)
  qed

  have h3: "(i1,i2) \<in> ?left \<longleftrightarrow> (i1,i2) \<in> ?right"
    if  "i1 \<noteq> i" and "i2 \<noteq> i" and "i1\<noteq>i2"
    for i1 i2
    apply (auto simp add: invocation_happensBeforeH_def ico_simp updateHb_cases that that[symmetric])
      apply (auto simp add: i_callOriginI_h_def split: option.splits)
    apply (metis co_none domI domIff in_sequence_in2)
    using co_none in_sequence_in2 wf_hb1 apply fastforce
    using co_none by auto

  have  "(i1,i2) \<in> ?left \<longleftrightarrow> (i1,i2) \<in> ?right"    for i1 i2
    by (cases "i1=i2"; cases "i1=i"; cases "i2=i"; clarify?; rule h0 h1 h2 h3; force)


  thus ?thesis
    by auto
qed



end