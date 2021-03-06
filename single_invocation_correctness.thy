section \<open>Single-Invocation Corrrectness\<close>

theory single_invocation_correctness
  imports execution_invariants_s fixedpoints execution_invariants invContext_simps
    state_monotonicGrowth_invariants
begin


text \<open>This theory includes techniques to prove that a program is correct in the single-invocId semantics.\<close>

text \<open>
  Start with initial state,
  
  then steps
  
  finally return and last check
  
  somehow automated

\<close>


fun updateHb where
  updateHb_nil: "updateHb hb vis [] = hb"
| updateHb_cons[simp del]: "updateHb hb vis (c#cs) = updateHb (hb \<union> vis \<times> {c}) (insert c vis) cs"

lemma updateHb_single: "updateHb hb vis [c] = hb \<union> vis \<times> {c}"
  by (simp add: updateHb_cons)

lemma updateHb_chain: 
  assumes "vis' = set cs \<union> vis"
  shows "updateHb (updateHb hb vis cs) vis' [c] = updateHb hb vis (cs@[c])"
using assms apply (induct cs arbitrary: hb vis vis' c )
  by (fastforce simp add:  updateHb_cons)+

lemma updateHb_simp1:
  assumes "x \<notin> set cs"
  shows "(x,y) \<in> updateHb hb vis cs \<longleftrightarrow> ((x,y) \<in> hb \<or> x\<in>vis \<and> y \<in> set cs)"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    by (auto simp add: updateHb_cons)
qed


lemma updateHb_simp2:
  assumes "y \<notin> set cs"
  shows "(x,y) \<in> updateHb hb vis cs \<longleftrightarrow> (x,y) \<in> hb"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    by (auto simp add: updateHb_cons)
qed

lemma updateHb_in_vis:
  assumes 
    "x\<in>vis"
    and "y\<in>set cs"
   shows "(x,y) \<in> updateHb hb vis cs"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    apply (auto simp add: updateHb_cons  )
    by (metis UnI2 insert_is_Un mem_Sigma_iff singletonI updateHb_simp2)
qed

lemma updateHb_simp3:
  assumes 
    "cs!i = x"
    and "cs!j = y"
    and "i<j"
    and "j<length cs"
   shows "(x,y) \<in> updateHb hb vis cs"
  using assms proof (induct cs arbitrary: hb vis i j)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    apply (auto simp add: updateHb_cons in_set_conv_nth nth_Cons' )
    by (simp add: updateHb_in_vis)
qed

lemma updateHb_simp_distinct:
  assumes 
    "distinct cs"
  shows "(x,y) \<in> updateHb hb vis cs 
  \<longleftrightarrow> ((x, y)\<in>hb \<or> x\<in>vis \<and> y\<in>set cs \<or> (\<exists>i j. cs!i=x \<and> cs!j=y \<and> i < j \<and> j < length cs))"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)

  have IH:
    "(x,y) \<in> updateHb (hb \<union> vis \<times> {a}) (insert a vis) cs
\<longleftrightarrow> ((x, y)\<in>(hb \<union> vis \<times> {a}) \<or> x\<in>(insert a vis) \<and> y\<in>set cs \<or> (\<exists>i j. cs!i=x \<and> cs!j=y \<and> i < j \<and> j < length cs))"
    apply (rule Cons) using Cons.prems by auto

  show ?case 
    apply (auto simp add: updateHb_cons IH )
    apply (metis One_nat_def in_set_conv_nth list.sel(3) not_less_eq nth_Cons_0 nth_Cons_pos nth_tl zero_less_Suc)
    apply (metis One_nat_def Suc_mono diff_Suc_1 nth_Cons_Suc)
    apply (metis One_nat_def Suc_less_eq Suc_pred nat_neq_iff not_less_zero nth_Cons')
    by (metis One_nat_def diff_Suc_1 gr_implies_not0 less_Suc_eq_0_disj nth_Cons')
qed


lemma updateHb_simp_distinct2:
  shows "(x,y) \<in> updateHb hb vis cs 
  \<longleftrightarrow> ((x, y)\<in>hb 
      \<or> x\<in>vis \<and> y\<in>set cs 
      \<or> before_in_list cs x y)"
proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by auto
next
case (Cons a cs)
  show ?case 
    by (auto simp add: updateHb_cons before_in_list_cons updateHb_simp2 Cons.hyps before_in_list_contains_r)
qed


lemma updateHb_simp_split:
"updateHb hb vis cs = hb \<union> updateHb {} vis cs"
proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a cs)

  have "updateHb hb vis (a # cs) 
      = updateHb (hb \<union> vis \<times> {a}) (insert a vis) cs"
    by (simp add: updateHb_cons)
  also have "... = (hb \<union> vis \<times> {a}) \<union> updateHb {} (insert a vis) cs"
    by (meson Cons.hyps)
  also have "... = hb \<union> updateHb (vis \<times> {a}) (insert a vis) cs"
    using Cons.hyps by blast
  also have "... = hb \<union> updateHb {} vis (a # cs) "
    by (simp add: updateHb_cons)
  finally show ?case .
qed

lemma snd_updateHb:
"snd ` updateHb hb vis cs \<subseteq> snd ` hb \<union> set cs"
  by (smt UnI1 UnI2 image_eqI image_subset_iff prod.collapse updateHb_simp2)

lemma snd_updateHb2:
"snd ` updateHb {} vis cs \<subseteq> set cs"
  using snd_updateHb by fastforce

  


abbreviation invariant_all' :: "('proc, 'ls, 'op, 'any) state \<Rightarrow> bool" where
"invariant_all' state \<equiv>  invariant (prog state) (invContext' state)"



lemma use_map_le:
  assumes "m x \<triangleq> y" and "m  \<subseteq>\<^sub>m m'"
  shows "m' x \<triangleq> y"
  using assms
  by (metis domI map_le_def) 

lemma has_invocOp_forever:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and "invocOp S i \<triangleq> info"
  shows "invocOp S' i \<triangleq> info"

  using assms proof (induct rule: step_s_induct)
  case initial
  then show ?case by auto
next
  case (step tr S' a S'')
  then have i1: "invocOp S i \<triangleq> info" and  i2: "invocOp S' i \<triangleq> info"
    by auto

  from \<open>S' ~~ (i, a) \<leadsto>\<^sub>S S''\<close>
  show ?case
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )

  next
    case (newId C s ls f ls' uid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (beginAtomic C s ls f ls' t C' C'' vis vis' )
    then show ?case using i2 state_monotonicGrowth_invocOp[OF \<open>state_monotonicGrowth s C C'\<close>]
      by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (endAtomic C s ls f ls' t C' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (dbop C s ls f Op  ls' t c res vis)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (invocation C s procName  initState impl C' C'' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (return C s ls f res C' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  qed

qed


lemma has_invocOp_afterOneStep:
  assumes step: "S ~~ (i, a) \<leadsto>\<^sub>S S'"
    and wf: "state_wellFormed_s S i"
  shows "invocOp S' i \<noteq> None"   
  using step wf by (auto simp add: step_s.simps wf_s_localState_to_invocOp2,
    meson state_monotonicGrowth_invocOp wf_s_localState_to_invocOp2)



lemma has_invocOp_afterStart:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and notEmpty: "trace \<noteq> []"
    and wf: "state_wellFormed_s S i"
  shows "invocOp S' i \<noteq> None"   
  using steps notEmpty wf proof (induct rule: step_s_induct)
  case initial
  then show ?case
    by simp  
next
  case (step tr S a S')
  have "state_wellFormed_s S i"
    using local.wf state_wellFormed_s_def step.step steps_s_append by blast 

  from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> and \<open>state_wellFormed_s S i\<close>
  show ?case 
    by (rule has_invocOp_afterOneStep)
qed


lemma invocations_only_in_beginning:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and wf: "state_wellFormed_s S i"
    and notStarted: "invocOp S i = None"
    and traceLen: "j < length trace"
  shows "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
proof -

  from steps
  obtain S_mid where "S ~~ (i, take j trace) \<leadsto>\<^sub>S* S_mid" and "S_mid ~~ (i, drop j trace) \<leadsto>\<^sub>S* S'"
    using steps_s_append_simp by force


  obtain Sa where firstStep: "S ~~ (i, hd trace) \<leadsto>\<^sub>S Sa" and afterFirstStep: "Sa ~~ (i, tl trace) \<leadsto>\<^sub>S* S'"
    by (metis Cons_nth_drop_Suc append.assoc append_take_drop_id hd_Cons_tl snoc_eq_iff_butlast steps steps_s_cons_simp traceLen)

  with notStarted
  have startsWithInvoc: "isAInvoc (fst (hd trace))"
    by (auto simp add: step_s.simps isAInvoc_def local.wf wf_s_localState_to_invocOp)


  {
    assume "j = 0"
    then have "isAInvoc (fst (trace ! j))" 
      using startsWithInvoc hd_drop_conv_nth traceLen by force 
  }
  moreover
  {
    assume "j \<noteq> 0"

    from afterFirstStep
    obtain Sc where steps_until_after_j: "Sa ~~ (i, take j (tl trace)) \<leadsto>\<^sub>S* Sc"
      by (metis append_take_drop_id steps_s_append_simp)


\<comment> \<open>get Sb so that S Sa Sb S\<close>
    from steps_until_after_j
    have "Sa ~~ (i, (take (j-1) (tl trace))@[trace!j]) \<leadsto>\<^sub>S* Sc"
      by (metis \<open>j \<noteq> 0\<close> drop_Nil drop_eq_Nil hd_drop_conv_nth leD take_eq_Nil take_hd_drop take_tl tl_append2 tl_take traceLen)
    from this    
    obtain Sb 
      where steps1: "Sa ~~ (i, take (j-1) (tl trace)) \<leadsto>\<^sub>S* Sb"
        and step_j: "Sb ~~ (i, trace ! j) \<leadsto>\<^sub>S Sc"
      by (auto simp add: steps_s_append_simp steps_s_single)

    have "invocOp Sa i \<noteq> None"
      using firstStep has_invocOp_afterOneStep local.wf by blast  

    then have "invocOp Sb i \<noteq> None"
      using has_invocOp_forever steps1 by blast

    with step_j 
    have "\<not>isAInvoc (fst (trace ! j))" 
      by (auto simp add: step_s.simps isAInvoc_def)
  }
  ultimately
  show "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
    by blast
qed    

lemma initialState_noTxns1:
  assumes initS: "S \<in> initialStates program i"
  shows "txStatus S tx \<noteq> Some Uncommitted"
  using initS by (auto simp add: initialStates_def)

lemma initialState_noTxns2:
  assumes initS: "S \<in> initialStates program i"
  shows "currentTx S i' = None"
  using initS by (auto simp add: initialStates_def,
      meson option.exhaust wellFormed_currentTx_unique_h(2))


lemma steps_s_noOtherTx:
  assumes steps: "initS ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and initS: "initS \<in> initialStates program i"
    and "i' \<noteq> i"
  shows "currentTx S_fin i' = None"
  using steps proof (induct rule: step_s_induct)
  case initial
  from initS
  show "currentTx initS i' = None"
    using initialState_noTxns2 by auto

next
  case (step tr S a S')


  from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> 
  show ?case 
    using \<open>i' \<noteq> i\<close> by (auto simp add: step_s.simps \<open>currentTx S i' = None\<close>,
        (meson option.exhaust wellFormed_currentTx_unique_h(2))+)
qed

lemma state_wellFormed_combine1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto> S'"
  and "a\<noteq>ACrash"
shows "state_wellFormed S'"
  using \<open>state_wellFormed S\<close> proof (rule state_wellFormed_combine)
  from \<open>S ~~ (i, a) \<leadsto> S'\<close>
  show "S ~~ [(i,a)] \<leadsto>* S'"
    by (simp add: steps_single)
  show "\<And>ia. (ia, ACrash) \<notin> set [(i, a)]"
    using \<open>a\<noteq>ACrash\<close> by simp
qed

lemma state_wellFormed_combine_s1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto>\<^sub>S S'"
shows "state_wellFormed S'"
proof -

from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> 
  show "state_wellFormed S'"
  proof (induct rule: step_s.cases)
    case (local C s ls f ok ls')
    then have "S ~~ (i, ALocal ok) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (newId C s ls f ls' uid uidv ls'')
    then have "S ~~ (i, ANewId uidv) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (beginAtomic C s ls f ls' t C' vis vis' newTxns )
    then show ?case 
      by blast
  next
    case (endAtomic C s ls f ls' t C' valid)
    then have "S ~~ (i, AEndAtomic) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (dbop C s ls f Op ls' t c res vis)
    then have "S ~~ (i, ADbOp c Op res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (invocation C s proc initState impl C' C'' valid)
    then have "C' ~~ (i, AInvoc proc) \<leadsto> C''"
      by (auto simp add: step.simps,
        insert wf_localState_to_invocOp, blast+)

    then show ?case
      using \<open>state_wellFormed C'\<close> \<open>S' = C''\<close> state_wellFormed_combine1 by blast
  next
    case (return C s ls f res C' valid)
    then have "S ~~ (i, AReturn res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  qed
qed

lemma committedCalls_allCommitted:
  assumes wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. txStatus S t \<noteq> Some Uncommitted"
  shows "committedCalls S = dom (calls S)"
proof (auto simp add: committedCallsH_def isCommittedH_def )

  

  show "\<exists>y. calls S x \<triangleq> y"
    if c0: "callOrigin S x \<triangleq> tx"
      and c1: "txStatus S tx \<triangleq> Committed"
    for  x tx
    using that  by (simp add: domD domIff local.wf wellFormed_callOrigin_dom3)

  

  show "\<exists>tx. callOrigin S x \<triangleq> tx \<and> txStatus S tx \<triangleq> Committed"
    if c0: "calls S x \<triangleq> y"
    for  x y
  proof - 
    obtain tx where "callOrigin S x \<triangleq> tx"
      using c0 local.wf wellFormed_callOrigin_dom3 by force

    moreover have "txStatus S tx \<triangleq> Committed"
      by (metis (full_types) \<open>callOrigin S x \<triangleq> tx\<close> domD domIff local.wf noUncommitted txStatus.exhaust wf_no_txStatus_origin_for_nothing)


    ultimately show "\<exists>tx. callOrigin S x \<triangleq> tx \<and> txStatus S tx \<triangleq> Committed"
      by blast
  qed
qed

lemma invContextH_same_allCommitted:
  assumes  wf1: "\<And>c. (state_calls c = None) \<longleftrightarrow> (state_callOrigin c = None)"
    and wf2: "\<And>c tx. state_callOrigin c \<triangleq> tx \<Longrightarrow> state_txStatus tx \<noteq> None"
    and wf3: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls a \<noteq> None"
    and wf4: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls b \<noteq> None"
    and wf5: "\<And>c. (state_txOrigin c = None) \<longleftrightarrow> (state_txStatus c = None)"
    and noUncommitted: "\<And>t. state_txStatus t \<noteq> Some Uncommitted"
  shows "invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore state_calls state_knownIds state_invocOp state_invocRes
       = invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore state_calls state_knownIds state_invocOp state_invocRes"
proof (auto simp add: invContextH_def invContextH2_def
  committedCallsH_def isCommittedH_def restrict_map_def restrict_relation_def
   intro!: ext)
  show "\<And>x. \<forall>tx. state_callOrigin x \<triangleq> tx \<longrightarrow> state_txStatus tx \<noteq> Some Committed \<Longrightarrow> None = state_calls x"
    by (metis (full_types) noUncommitted option.exhaust_sel txStatus.exhaust wf1 wf2)
  show "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> \<exists>tx. state_callOrigin a \<triangleq> tx \<and> state_txStatus tx \<triangleq> Committed"
    by (metis (full_types) noUncommitted option.exhaust txStatus.exhaust wf1 wf2 wf3)
  show "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> \<exists>tx. state_callOrigin b \<triangleq> tx \<and> state_txStatus tx \<triangleq> Committed"
    by (metis (full_types) noUncommitted option.exhaust txStatus.exhaust wf1 wf2 wf4)
  show "\<And>x. \<forall>tx. state_callOrigin x \<triangleq> tx \<longrightarrow> state_txStatus tx \<noteq> Some Committed \<Longrightarrow> None = state_callOrigin x"
    by (metis (full_types) noUncommitted option.exhaust_sel txStatus.exhaust wf2)
  show "\<And>x. state_txStatus x \<noteq> Some Committed \<Longrightarrow> None = state_txOrigin x"
    by (metis noUncommitted option.exhaust_sel txStatus.exhaust wf5)
qed

lemmas invContextH_same_allCommitted' = invContextH_same_allCommitted[simplified invContextH2_def]



lemma invContext_same_allCommitted:
  assumes  wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. txStatus S t \<noteq> Some Uncommitted"
  shows "invContext S
       = invContext' S"
proof (rule invContextH_same_allCommitted)
  show "\<And>c. (calls S c = None) = (callOrigin S c = None)"
  using local.wf wellFormed_callOrigin_dom3 by blast
    show "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> txStatus S tx \<noteq> None"
      by (simp add: local.wf wellFormed_state_callOrigin_txStatus)
   show "\<And>a b. (a, b) \<in> happensBefore S \<Longrightarrow> calls S a \<noteq> None"
     by (simp add: local.wf wellFormed_happensBefore_calls_l)
   show "\<And>a b. (a, b) \<in> happensBefore S \<Longrightarrow> calls S b \<noteq> None"
     by (simp add: local.wf wellFormed_happensBefore_calls_r)
   show "\<And>c. (txOrigin S c = None) = (txStatus S c = None)"
     by (simp add: local.wf wf_transaction_status_iff_origin)
   show "\<And>t. txStatus S t \<noteq> Some Uncommitted"
     using noUncommitted by blast
 qed

lemmas invContext_same_allCommitted' = invContext_same_allCommitted[simplified invContextH2_def]


lemma wf_localState_currentProc_m:
  assumes "S ~~ tr \<leadsto>* S'"
    and "(localState S i = None \<longleftrightarrow> currentProc S i = None)"
  shows "(localState S' i = None \<longleftrightarrow> currentProc S' i = None)"
  using assms proof (induct rule: steps_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step S' tr a S'')
  then show ?case  by (auto simp add: step.simps split: if_splits)
qed


lemma wf_localState_currentProc:
  assumes "state_wellFormed S"
  shows "localState S i = None \<longleftrightarrow> currentProc S i = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  then show ?case 
    by (auto simp add: step.simps split: if_splits)
qed






lemma show_exists_state:
  fixes P :: "('proc, 'ls, 'op, 'any)state \<Rightarrow> bool"
  assumes "\<exists>calls happensBefore prog callOrigin txOrigin
   generatedIds knownIds invocOp invocRes txStatus
localState currentProc visibleCalls currentTx. P \<lparr>
  calls = calls,
  happensBefore = happensBefore,
  callOrigin  = callOrigin,
  txOrigin  = txOrigin,
  knownIds  = knownIds,
  invocOp  =invocOp,
  invocRes =invocRes,
  prog = prog,
  txStatus  =txStatus,
  generatedIds  = generatedIds,
  localState  =localState,
  currentProc  =currentProc,
  visibleCalls  =visibleCalls,
  currentTx  = currentTx
 \<rparr>"
  shows "\<exists>S. P S"
  using assms by auto

lemma exists_narrowL1: "(\<exists>x. P x \<and> Q) \<longleftrightarrow> (\<exists>x. P x) \<and> Q" 
  by auto

lemma exists_narrowL2: "(\<exists>x y. P x y \<and> Q y) \<longleftrightarrow> (\<exists>y. (\<exists>x. P x y) \<and> Q y)" 
  by auto

lemma exists_narrowL3: "(\<exists>x y1 y2. P x y1 y2 \<and> Q y1 y2) \<longleftrightarrow> (\<exists>y1 y2. (\<exists>x. P x y1 y2) \<and> Q y1 y2)" 
  by auto

lemma exists_narrowL4: "(\<exists>x y1 y2 y3. P x y1 y2 y3 \<and> Q y1 y2 y3) \<longleftrightarrow> (\<exists>y1 y2 y3. (\<exists>x. P x y1 y2 y3) \<and> Q y1 y2 y3)" 
  by auto

lemma exists_narrowR1: "(\<exists>x. P \<and> Q x) \<longleftrightarrow> P \<and> (\<exists>x. Q x)" 
  by auto

lemma exists_narrowR2: "(\<exists>x y. P y \<and> Q x y) \<longleftrightarrow> (\<exists>y. P  y \<and> (\<exists>x. Q x y))" 
  by auto

lemma exists_narrowR3: "(\<exists>x y1 y2. P y1 y2 \<and> Q x y1 y2) \<longleftrightarrow> (\<exists>y1 y2. P y1 y2 \<and> (\<exists>x. Q x y1 y2))" 
  by auto

lemma exists_narrowR4: "(\<exists>x y1 y2 y3. P y1 y2 y3 \<and> Q x y1 y2 y3) \<longleftrightarrow> (\<exists>y1 y2 y3. P y1 y2 y3 \<and> (\<exists>x. Q x y1 y2 y3))" 
  by auto

lemmas exists_narrow = 
exists_narrowL1 
exists_narrowL2
exists_narrowL3
exists_narrowL4
exists_narrowR1
exists_narrowR2
exists_narrowR3
exists_narrowR4

lemma prog_initial: "prog (initialState program) = program"
  by (auto simp add: initialState_def)








lemma consistentSnapshot_empty: "consistentSnapshot S {}"
  by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def  transactionConsistent_committed_def transactionConsistent_atomic_def)



lemma exists_optionI: "x \<noteq> None \<Longrightarrow> \<exists>y. x \<triangleq> y"
  by auto



lemma txStatus_initial: "txStatus (initialState progr) t = None"
  by (simp add: initialState_def)




definition initialStates' :: "('proc::valueType, 'ls, 'op::valueType, 'any::valueType) prog \<Rightarrow> invocId \<Rightarrow> ('proc, 'ls, 'op, 'any) state set"  where
  "initialStates' progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocOp := (invocOp S)(i \<mapsto> proc)\<rparr>) 
 | S proc initState impl.
    prog S = progr
  \<and> procedure progr proc = (initState, impl)  
  \<and> uniqueIds proc \<subseteq> knownIds S
  \<and> invariant_all' S
  \<and> state_wellFormed S
  \<and> invocOp S i = None
  \<and> (\<forall>tx. txStatus S tx \<noteq> Some Uncommitted)
  \<and> (\<forall>tx. txOrigin S tx \<noteq> Some i)
}"

lemma initialStates'_same:
  shows "initialStates progr i = initialStates' progr i"
proof(auto simp add: initialStates_def initialStates'_def, fuzzy_goal_cases A B)
  case (A S proc initState impl)
  then show ?case 
    by (auto simp add: invContext_same_allCommitted)
next
  case (B S proc initState impl)
  then show ?case
    by (auto simp add: invContext_same_allCommitted intro!: exI)
qed

       

end