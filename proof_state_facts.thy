theory proof_state_facts
imports program_proof_rules_loops
begin


lemma ps_wellFormed_to_wf:
  assumes wf: "proof_state_wellFormed S"
  obtains CS where "proof_state_rel S CS" and "state_wellFormed CS"
  using local.wf proof_state_rel_wf proof_state_wellFormed_def by blast


lemma ps_wellFormed_state_causality:
  assumes wf: "proof_state_wellFormed S"
  shows "causallyConsistent (happensBefore S) (ps_vis S)"
  by (smt FieldI1 FieldI2 Un_iff causallyConsistent_def disjoint_iff_not_equal local.wf proof_state_rel_facts(1) proof_state_rel_hb proof_state_rel_vis proof_state_wellFormed_def proof_state_wellFormed_disjoint_happensBefore_localCalls updateHb_simp2 wf_vis_downwards_closed2)


lemma ps_wellFormed_state_hb_trans:
  assumes wf: "proof_state_wellFormed S"
  shows "trans (happensBefore S)"
  by (smt FieldI2 disjoint_iff_not_equal happensBefore_transitive local.wf proof_state_rel_facts(1) proof_state_rel_hb proof_state_wellFormed_def proof_state_wellFormed_disjoint_happensBefore_localCalls trans_def updateHb_simp2)

lemma ps_localCalls_no_origin:
  assumes wf: "proof_state_wellFormed S"
    and "c \<in> set (ps_localCalls S)"
  shows "callOrigin S c = None"
  by (meson assms(2) disjoint_iff_not_equal domIff local.wf proof_state_rel_callOrigin_localCalls_disjoint ps_wellFormed_to_wf)

lemma ps_not_localCalls_not_tx:
  assumes wf: "proof_state_wellFormed S"
    and "c \<notin> set (ps_localCalls S)"
    and "ps_tx S \<triangleq> tx"
  shows "callOrigin S c \<noteq> Some tx"
  by (metis (mono_tags, lifting) assms(2) assms(3) local.wf map_update_all_get mem_Collect_eq option.simps(5) proof_state_rel_callOrigin proof_state_rel_localCalls ps_wellFormed_to_wf)


lemma rel_callOrigin_vis:
  assumes rel: "proof_state_rel S CS"
    and "c \<in> ps_vis S"
  shows "callOrigin CS c = callOrigin S c" 
proof -
  have co: "callOrigin CS = map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S))"
    using proof_state_rel_def rel by blast
  show ?thesis
    using `c \<in> ps_vis S`
    by (metis Set.set_insert co disjoint_insert(1) map_update_all_get proof_state_rel_vis_localCalls_disjoint rel)
qed

lemma rel_callOrigin_ls:
  assumes rel: "proof_state_rel S CS"
    and "c \<in> set (ps_localCalls S)"
  shows "callOrigin CS c = ps_tx S"
  using assms(2) map_update_all_Some_same proof_state_rel_callOrigin proof_state_wellFormed_localCalls rel show_proof_state_wellFormed by fastforce 

lemma rel_callOrigin_ls_rev:
  assumes rel: "proof_state_rel S CS"
    and "callOrigin CS c \<triangleq> tx"
    and "ps_tx S \<triangleq> tx"
  shows "c \<in> set (ps_localCalls S)"
  by (metis (no_types, lifting) assms(2) assms(3) map_update_all_get proof_state_rel_callOrigin ps_not_localCalls_not_tx rel show_proof_state_wellFormed)



lemma rel_callOrigin_vis2:
  assumes  rel: "proof_state_rel S CS"
    and sameOrigin: "callOrigin S c = callOrigin S c'"
    and \<open>c \<in> ps_vis S\<close>
  shows "callOrigin CS c = callOrigin CS c'"
  by (metis (no_types, lifting) assms(3) map_update_all_get option.distinct(1) proof_state_rel_callOrigin proof_state_rel_calls proof_state_rel_wf proof_state_wellFormed_vis_subset_calls' ps_localCalls_no_origin rel rel_callOrigin_vis sameOrigin show_proof_state_wellFormed wf_callOrigin_and_calls)


lemma ps_wellFormed_state_transaction_consistent1:
  assumes wf: "proof_state_wellFormed S"
    and c_vis: "c\<in>ps_vis S"
    and sameOrigin: "callOrigin S c = callOrigin S c'"
  shows "c'\<in>ps_vis S"
proof (rule ps_wellFormed_to_wf[OF wf])
  fix CS
  assume rel: "proof_state_rel S CS"
    and CS_wf: "state_wellFormed CS"

  have vis: "visibleCalls CS (ps_i S) \<triangleq> (ps_vis S \<union> set (ps_localCalls S))"
    by (simp add: proof_state_rel_vis rel)

  have "c' \<in> (ps_vis S \<union> set (ps_localCalls S))"
    using CS_wf vis
  proof (rule wellFormed_state_transaction_consistent(2))
    show "c \<in> ps_vis S \<union> set (ps_localCalls S)"
      by (simp add: c_vis)
    show "callOrigin CS c = callOrigin CS c'"
      by (smt CS_wf \<open>c \<in> ps_vis S \<union> set (ps_localCalls S)\<close> c_vis disjoint_iff_not_equal in_dom local.wf map_update_all_None map_update_all_get proof_state_rel_callOrigin proof_state_rel_vis_localCalls_disjoint ps_localCalls_no_origin rel sameOrigin vis wellFormed_callOrigin_dom wellFormed_visibleCallsSubsetCalls_h(2))
  qed

  show "c' \<in> ps_vis S"
    by (metis CS_wf UnE \<open>c' \<in> ps_vis S \<union> set (ps_localCalls S)\<close> c_vis local.wf ps_localCalls_no_origin rel rel_callOrigin_vis rel_callOrigin_vis2 sameOrigin vis wellFormed_callOrigin_dom3 wellFormed_visibleCallsSubsetCalls2)

qed


lemma rel_callOrigin_different:
  assumes a0: "callOrigin S x \<noteq> callOrigin S y"
    and wf: "proof_state_wellFormed S"
    and rel: "proof_state_rel S CS"
  shows "callOrigin CS x \<noteq> callOrigin CS y"
  by (smt a0 empty_iff empty_set local.wf map_update_all_get option.exhaust_sel proof_state_rel_callOrigin proof_state_wellFormed_localCalls ps_localCalls_no_origin ps_not_localCalls_not_tx rel)

lemma rel_callOrigin_same:
  assumes "callOrigin S x \<triangleq> xtx"
    and a1: "callOrigin S x = callOrigin S x'"
    and  wf: "proof_state_wellFormed S"
    and rel: "proof_state_rel S CS"
  shows "callOrigin CS x = callOrigin CS x'"
  by (metis (no_types, lifting) \<open>callOrigin S x \<triangleq> xtx\<close> a1 local.wf map_update_all_get option.simps(3) proof_state_rel_callOrigin ps_localCalls_no_origin rel)

lemma rel_noCallOrigin_noHappensBefore:
  assumes "callOrigin S x = None"
    and rel: "proof_state_rel S CS"
    and  wf: "proof_state_wellFormed S"
  shows "(x,y) \<notin> happensBefore S"
  by (metis (no_types, lifting) FieldI1 assms(1) disjoint_iff_not_equal domIff local.wf map_update_all_None proof_state_rel_calls proof_state_rel_facts(4) proof_state_rel_happensBefore_localCalls_disjoint proof_state_rel_wf proof_state_wellFormed_happensBefore_subset_calls rel subsetD wellFormed_callOrigin_dom)

lemma rel_noCallOrigin_noHappensBefore_r:
  assumes "callOrigin S x = None"
    and rel: "proof_state_rel S CS"
    and  wf: "proof_state_wellFormed S"
  shows "(y,x) \<notin> happensBefore S"
  by (metis (no_types, lifting) FieldI2 assms(1) disjoint_iff_not_equal domIff local.wf map_update_all_None proof_state_rel_calls proof_state_rel_facts(4) proof_state_rel_wf proof_state_wellFormed_disjoint_happensBefore_localCalls proof_state_wellFormed_happensBefore_subset_calls rel subsetD wellFormed_callOrigin_dom)


lemma ps_wellFormed_state_transaction_consistent_hb:
  assumes wf: "proof_state_wellFormed S"
    and a0: "callOrigin S x \<noteq> callOrigin S y"
    and a1: "callOrigin S x = callOrigin S x'"
    and a2: "callOrigin S y = callOrigin S y'"
  shows "(x,y) \<in> happensBefore S \<longleftrightarrow> (x', y') \<in> happensBefore S"
proof (rule ps_wellFormed_to_wf[OF wf])
  fix CS
  assume  rel: "proof_state_rel S CS"
    and CS_wf: "state_wellFormed CS"

  {
    fix xtx ytx
    assume "callOrigin S x \<triangleq> xtx" 
      and "callOrigin S y \<triangleq> ytx"


    have "((x, y) \<in> happensBefore CS) = ((x', y') \<in> happensBefore CS)"
      using CS_wf
    proof (rule wellFormed_state_transaction_consistent(3))
      show "callOrigin CS x \<noteq> callOrigin CS y"
        using a0 local.wf rel rel_callOrigin_different by blast
      show "callOrigin CS x = callOrigin CS x'"
        using \<open>callOrigin S x \<triangleq> xtx\<close> a1 local.wf rel rel_callOrigin_same by blast
      show "callOrigin CS y = callOrigin CS y'"
        using \<open>callOrigin S y \<triangleq> ytx\<close> a2 local.wf rel rel_callOrigin_same by blast
    qed


    hence "((x, y) \<in> happensBefore S) \<longleftrightarrow> ((x', y') \<in> happensBefore S)"
      by (metis \<open>callOrigin S y \<triangleq> ytx\<close> a2 local.wf option.simps(3) proof_state_rel_hb ps_localCalls_no_origin rel updateHb_simp2)
  }
  moreover
  {
    assume "callOrigin S x = None" 
    hence "(x,y) \<notin> happensBefore S"
      using local.wf rel rel_noCallOrigin_noHappensBefore by blast
    have "callOrigin S x' = None"
      using \<open>callOrigin S x = None\<close> a1 by auto 
    hence "(x',y') \<notin> happensBefore S"
      using local.wf rel rel_noCallOrigin_noHappensBefore by blast
    hence "((x, y) \<in> happensBefore S) \<longleftrightarrow> ((x', y') \<in> happensBefore S)"
      using \<open>(x, y) \<notin> happensBefore S\<close> by blast
  }
  moreover
  {
    assume "callOrigin S y = None" 
    hence "(x,y) \<notin> happensBefore S"
      using local.wf rel rel_noCallOrigin_noHappensBefore_r by blast
    have "callOrigin S y' = None"
      using \<open>callOrigin S y = None\<close> a2 by auto 
    hence "(x',y') \<notin> happensBefore S"
      using local.wf rel rel_noCallOrigin_noHappensBefore_r by blast
    hence "((x, y) \<in> happensBefore S) \<longleftrightarrow> ((x', y') \<in> happensBefore S)"
      using \<open>(x, y) \<notin> happensBefore S\<close> by blast
  }
  ultimately show ?thesis
    by blast
qed




lemma ps_wellFormed_state_consistent_snapshot:
assumes wf: "proof_state_wellFormed S"
assumes noTx: "\<And>c tx. ps_tx S \<triangleq> tx \<Longrightarrow> callOrigin S c \<noteq> Some tx" 
shows "consistentSnapshotH (calls S) (happensBefore S) (callOrigin S) (\<lambda>x. Some Committed) (ps_vis S)"
  by (simp add: local.wf proof_state_wellFormed_vis_subset_calls ps_wellFormed_state_causality ps_wellFormed_state_transaction_consistent1 show_consistentSnapshot show_transactionConsistent)


lemma ps_wf_happensBefore_irrefl:
assumes wf: "proof_state_wellFormed S"
shows "irrefl (happensBefore S)"
  by (metis (no_types, hide_lams) happensBefore_irrefl  irrefl_def local.wf proof_state_rel_hb ps_wellFormed_to_wf updateHb_simp_distinct2)


lemma ps_wf_happensBefore_acyclic:
assumes wf: "proof_state_wellFormed S"
shows "acyclic (happensBefore S)"
  by (simp add: acyclic_irrefl local.wf ps_wf_happensBefore_irrefl ps_wellFormed_state_hb_trans)




lemma ps_wf_vis_downwards_closed:
  assumes wf: "proof_state_wellFormed S"
    and "(x,y) \<in> happensBefore S"
    and "y\<in>ps_vis S"
  shows "x\<in>ps_vis S"
  by (meson assms(2) assms(3) causallyConsistent_def local.wf ps_wellFormed_state_causality)





lemma ps_wf_happensBefore_txns_left: 
  assumes wf: "proof_state_wellFormed S"
  assumes "(x,y) \<in> happensBefore S"
    and "callOrigin S x = callOrigin S x'"
    and "callOrigin S x \<noteq> callOrigin S y"
  shows "(x',y) \<in> happensBefore S"
  using assms(2) assms(3) assms(4) local.wf ps_wellFormed_state_transaction_consistent_hb by blast




lemma causallyConsistent_downwards_closure:
assumes wf: "proof_state_wellFormed S"
shows "causallyConsistent (happensBefore S) (cs \<down> happensBefore S)"
  by (smt causallyConsistent_def downwardsClosure_in local.wf ps_wellFormed_state_hb_trans transD)




lemma ps_wf_current_tx_not_before_others: 
  assumes wf: "proof_state_wellFormed S"
    and "ps_tx S \<triangleq> tx"
    and "callOrigin S x \<triangleq> tx"
    and "callOrigin S y \<noteq> Some tx"
  shows "(x,y) \<notin> happensBefore S"
  by (meson assms(2) assms(3) domI domIff local.wf ps_localCalls_no_origin ps_not_localCalls_not_tx)



(*
lemma ps_i_callOriginI_notI1:
  assumes "proof_state_wellFormed S_pre" 
    and "invocOp S_pre i = None" 
  shows "i_callOriginI S_pre c \<noteq> Some i"

  by (metis (no_types, lifting) assms(1) assms(2) i_callOriginI_h_def option.case_eq_if option.simps(3) proof_state_rel_invocOp proof_state_rel_txOrigin proof_state_rel_wf proof_state_wellFormed_def wf_no_invocation_no_origin)
*)
(*
lemma ps_i_callOriginI_notI2:
  assumes "proof_state_wellFormed S_pre" 
    and "i_callOriginI S_pre c = Some i" 
  shows "invocOp S_pre i \<noteq> None"
  using assms(1) assms(2) ps_i_callOriginI_notI1 by auto
*)

lemma ps_wellFormed_current_transaction_origin:     
  assumes "proof_state_wellFormed S"
    and "ps_tx S \<triangleq> tx"
  shows "txOrigin S tx = None"
  using assms(1) assms(2) proof_state_rel_txOriginNone proof_state_wellFormed_def by blast


lemma ps_wellFormed_ls_visibleCalls_callOrigin:     
  assumes "proof_state_wellFormed S"
    and "callOrigin S c \<triangleq> tx"
    and "txOrigin S tx \<triangleq> ps_i S"
  shows "c \<in> ps_vis S"
  by (metis assms(1) assms(2) assms(3) i_callOriginI_h_simp proof_state_rel_see_my_updates ps_wellFormed_to_wf)




lemma ps_wf_queryspec:
  assumes wf: "proof_state_wellFormed S"
    and "calls S c \<triangleq> Call op r"
    and "prevCalls = {c'. (c',c)\<in>updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)}"
    and "ctxt = getContextH (calls S |` prevCalls) (updateHb (happensBefore S) (ps_vis S) (ps_localCalls S) |r prevCalls) (Some prevCalls)"
  shows "querySpec (ps_prog S) op ctxt r"
proof (rule ps_wellFormed_to_wf[OF wf])
  fix CS
  assume rel: "proof_state_rel S CS"
    and CS_wf: "state_wellFormed CS"

  have "querySpec (prog CS) op ctxt r"
    using CS_wf
  proof (rule wf_queryspec)
    show "calls CS c \<triangleq> Call op r"
      using assms(2) proof_state_rel_calls rel by fastforce
    show "prevCalls = {c'. (c', c) \<in> happensBefore CS}"
      using assms(3) proof_state_rel_hb rel by force
    show "ctxt = getContextH (calls CS |` prevCalls) (happensBefore CS |r prevCalls) (Some prevCalls)"
      using assms(4) proof_state_rel_calls proof_state_rel_hb rel by fastforce
  qed


  thus "querySpec (ps_prog S) op ctxt r"
    using proof_state_rel_prog rel by force
qed
  
lemma ps_growing_no_localCalls1:
  assumes "ps_growing S S' t"
  shows "ps_localCalls S = []"
  using assms  by (auto simp add: ps_growing_def)

lemma ps_growing_no_localCalls2:
  assumes "ps_growing S S' t"
  shows "ps_localCalls S' = []"
  using assms  by (auto simp add: ps_growing_def)

lemma ps_growing_no_tx1:
  assumes "ps_growing S S' t"
  shows "ps_tx S = None"
  using assms  by (auto simp add: ps_growing_def)

lemma ps_growing_no_tx2:
  assumes "ps_growing S S' t"
  shows "ps_tx S' \<triangleq> t"
  using assms  by (auto simp add: ps_growing_def)


lemma ps_growing_rule:
  assumes "ps_growing S S' t"
    and "\<And>CS CS'.
       \<lbrakk>proof_state_rel S CS; proof_state_rel S' CS';
        state_monotonicGrowth (ps_i S) CS
         (CS'\<lparr>txStatus := (txStatus CS')(t := None),
                txOrigin := (txOrigin CS')(t := None),
                currentTx := (currentTx CS')(ps_i S := None),
                localState := (localState CS')(ps_i S := localState CS (ps_i S)),
                visibleCalls := (visibleCalls CS')(ps_i S := visibleCalls CS (ps_i S))\<rparr>)\<rbrakk>
       \<Longrightarrow> P"
  shows P
  using assms by (auto simp add: ps_growing_def)


lemma ps_monotonicGrowth_txOrigin_i:
  assumes "ps_growing S S' tx"
    and "t \<noteq> tx"
  shows "txOrigin S' t \<triangleq> ps_i S \<longleftrightarrow> txOrigin S t \<triangleq> ps_i S"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S CS"
    and rel2: "proof_state_rel S' CS'"
    and g: "state_monotonicGrowth (ps_i S) CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S := None),                 localState := (localState CS')(ps_i S := localState CS (ps_i S)),                 visibleCalls := (visibleCalls CS')(ps_i S := visibleCalls CS (ps_i S))\<rparr>)"

  from state_monotonicGrowth_txOrigin_i[OF g, where t=t, simplified]
  have "txOrigin CS' t \<triangleq> ps_i S \<longleftrightarrow> txOrigin CS t \<triangleq> ps_i S"
    by (simp add: `t \<noteq> tx`)

  thus "txOrigin S' t \<triangleq> ps_i S = txOrigin S t \<triangleq> ps_i S"
    unfolding proof_state_rel_txOrigin[OF rel1] proof_state_rel_txOrigin[OF rel2]
    by (metis (no_types, lifting) assms(1) assms(2) fun_upd_other option.case_eq_if option.sel ps_growing_no_tx1 ps_growing_no_tx2)
qed


lemma ps_monotonicGrowth_no_new_calls_before_existing1:
  assumes "ps_growing S' S t"
    and "c2\<in>dom (calls S')"
    and "ps_vis S' = ps_vis S"
  shows "(c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(t := None),                 txOrigin := (txOrigin CS')(t := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  from state_monotonicGrowth_no_new_calls_before_existing1[OF g, simplified, of c2 c1]
  have "((c1, c2) \<in> happensBefore CS') \<longleftrightarrow> ((c1, c2) \<in> happensBefore CS)"
    using assms(2) proof_state_rel_calls rel1 by fastforce

  hence "((c1, c2) \<in> updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)) 
    \<longleftrightarrow>  ((c1, c2) \<in> updateHb (happensBefore S') (ps_vis S') (ps_localCalls S'))"
    unfolding proof_state_rel_hb[OF rel1] proof_state_rel_hb[OF rel2] .

  thus "((c1, c2) \<in> happensBefore S) = ((c1, c2) \<in> happensBefore S')"
    by (metis assms(1) ps_growing_no_localCalls1 ps_growing_no_localCalls2 single_invocation_correctness.updateHb_nil)
qed

lemma ps_monotonicGrowth_no_new_calls_before_existing: 
  assumes "ps_growing S' S t"
    and "calls S' c = None"
    and "calls S c \<triangleq> x"
    and "calls S' c' \<triangleq> y"
  shows "(c,c') \<notin> happensBefore S'"
  using assms
  by (meson FieldI1 domIff proof_state_wellFormed_happensBefore_subset_calls ps_growing_rule show_proof_state_wellFormed subset_h1)


lemma ps_monotonicGrowth_txOrigin: 
  assumes "ps_growing S' S tx" 
    and "txOrigin S' t \<triangleq> i'"
    and "tx \<noteq> t"
  shows "txOrigin S t \<triangleq> i'"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "txOrigin CS t \<triangleq> i'"
    using assms(1) assms(2) proof_state_rel_txOrigin ps_growing_no_tx1 rel1 by fastforce


  from state_monotonicGrowth_txOrigin[OF g `txOrigin CS t \<triangleq> i'`]
  have "txOrigin CS' t \<triangleq> i'"
    using assms(3) by auto


  thus "txOrigin S t \<triangleq> i'"
    using assms(1) assms(3) proof_state_rel_txOrigin ps_growing_no_tx2 rel2 by fastforce
qed


lemma ps_monotonicGrowth_calls:
  assumes "ps_growing S' S tx"
    and "calls S' c \<triangleq> info"
  shows "calls S c \<triangleq> info"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "calls CS c \<triangleq> info"
    using assms(2) proof_state_rel_calls rel1 by force


  from state_monotonicGrowth_calls[OF g `calls CS c \<triangleq> info`]
  show "calls S c \<triangleq> info"
    using proof_state_rel_calls rel2 by fastforce
qed

lemma ps_monotonicGrowth_happensBefore:
  assumes "ps_growing S' S tx"
  and "c2\<in>dom (calls S')"
shows "((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S')"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "c2 \<in> dom (calls CS)"
    using assms(2) proof_state_rel_calls rel1 by fastforce

  have "ps_localCalls S' = []"
    using assms(1) ps_growing_no_localCalls1 by blast


  from state_monotonicGrowth_happensBefore[OF g `c2 \<in> dom (calls CS)`, simplified]
  have "((c1, c2) \<in> happensBefore CS') = ((c1, c2) \<in> happensBefore CS)" .

  thus ?thesis
    using \<open>ps_localCalls S' = []\<close> assms(1) proof_state_rel_facts(3) ps_growing_no_localCalls2 rel1 rel2 by fastforce
qed

lemma ps_monotonicGrowth_callOrigin:
  assumes "ps_growing S' S tx"
    and "callOrigin S' c \<triangleq> t"
  shows "callOrigin S c \<triangleq> t"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "callOrigin CS c \<triangleq> t"
    using assms(1) assms(2) proof_state_rel_callOrigin ps_growing_no_localCalls1 rel1 by fastforce


  from state_monotonicGrowth_callOrigin[OF g `callOrigin CS c \<triangleq> t`]
  show "callOrigin S c \<triangleq> t"
    using assms(1) proof_state_rel_callOrigin ps_growing_no_localCalls2 rel2 by fastforce
qed

lemma ps_monotonicGrowth_callOrigin2:
  assumes "ps_growing S' S t"
  shows "callOrigin S c = None \<Longrightarrow> callOrigin S' c = None"
  by (metis assms option.exhaust ps_monotonicGrowth_callOrigin)
  

lemma ps_monotonicGrowth_knownIds:
  assumes "ps_growing S' S tx"
  shows "knownIds S' \<subseteq> knownIds S"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  from state_monotonicGrowth_knownIds[OF g, simplified]
  have "knownIds CS \<subseteq> knownIds CS'" .

  thus "knownIds S' \<subseteq> knownIds S"
    using proof_state_rel_knownIds rel1 rel2 by auto
qed



lemma ps_monotonicGrowth_invocOp:
  assumes "ps_growing S' S tx"
    and "invocOp S' s \<triangleq> info"
  shows "invocOp S s \<triangleq> info"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "invocOp CS s \<triangleq> info"
    using assms(2) proof_state_rel_invocOp rel1 by force


  from state_monotonicGrowth_invocOp[OF g `invocOp CS s \<triangleq> info`, simplified]
  show ?thesis
    using proof_state_rel_invocOp rel2 by fastforce
qed

lemma ps_growing_same_i:
assumes "ps_growing S' S tx"
shows "ps_i S = ps_i S'"
  using assms ps_growing_def by blast



lemma ps_monotonicGrowth_invocOp_i:
  assumes "ps_growing S' S tx"
  shows "invocOp S (ps_i S) = invocOp S' (ps_i S)"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  from state_monotonicGrowth_invocOp_i[OF g]
  have "invocOp CS' (ps_i S') = invocOp CS (ps_i S')" by simp
  thus ?thesis
    by (metis (no_types, lifting) assms proof_state_rel_invocOp ps_growing_same_i rel1 rel2)
qed

lemma ps_monotonicGrowth_invocRes:
  assumes "ps_growing S' S tx"
    and "invocRes S' s \<triangleq> info"
  shows "invocRes S s \<triangleq> info"
  using assms(1) proof (rule ps_growing_rule)
  fix CS CS'
  assume rel1: "proof_state_rel S' CS"
    and rel2: "proof_state_rel S CS'"
    and g: "state_monotonicGrowth (ps_i S') CS          (CS'\<lparr>txStatus := (txStatus CS')(tx := None),                 txOrigin := (txOrigin CS')(tx := None),                 currentTx := (currentTx CS')(ps_i S' := None),                 localState := (localState CS')(ps_i S' := localState CS (ps_i S')),                 visibleCalls := (visibleCalls CS')(ps_i S' := visibleCalls CS (ps_i S'))\<rparr>)"

  have "invocRes CS s \<triangleq> info"
    using assms(2) proof_state_rel_invocRes rel1 by fastforce


  from state_monotonicGrowth_invocRes[OF g `invocRes CS s \<triangleq> info`, simplified]
  have "invocRes CS' s \<triangleq> info" .
  thus ?thesis
    using proof_state_rel_invocRes rel2 by force
qed



lemma ps_monotonicGrowth_invocRes_i:
  assumes "ps_growing S' S t"
  shows "invocRes S' (ps_i S') = invocRes S (ps_i S')"
  by (smt assms proof_state_rel_invocRes proof_state_rel_ls proof_state_rel_wf ps_growing_rule ps_growing_same_i wf_localState_noReturn)



lemma ps_monotonicGrowth_prog:
  assumes "ps_growing S' S t"
  shows "ps_prog S = ps_prog S'"
  using assms ps_growing_def by blast

lemma ps_monotonicGrowth_invocOp2:
  assumes "ps_growing S' S t"
  shows "(invocOp S' \<subseteq>\<^sub>m invocOp S) "
  using assms map_le_def ps_monotonicGrowth_invocOp by fastforce

  


lemma ps_monotonicGrowth_current_transactions_fixed:
  assumes "ps_growing S S' t"
    and "ps_tx S \<triangleq> tx"
  shows "callOrigin S c \<triangleq> tx \<longleftrightarrow> callOrigin S' c \<triangleq> tx"
  using assms(1) assms(2) ps_growing_no_tx1 by force



end