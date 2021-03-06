section "Consistency"

theory consistency
  imports repliss_sem 
    execution_invariants
    "fuzzyrule.fuzzy_goal_cases"
begin


text "In this section, we show that the semantics maintains certain consistency invariants."

definition
"causallyConsistent hb vis \<equiv>
  (\<forall>c1 c2. c1\<in>vis \<and> (c2,c1)\<in> hb \<longrightarrow> c2\<in>vis)"

definition
"transactionConsistent_committed origin txSt vis \<equiv>
    (\<forall>c tx. c\<in>vis \<and> origin c \<triangleq> tx \<longrightarrow> txSt tx \<triangleq> Committed)"

definition
"transactionConsistent_atomic origin vis \<equiv>
     (\<forall>c1 c2. c1\<in>vis \<and> origin c1 = origin c2 \<longrightarrow> c2\<in>vis)"

definition
"transactionConsistent origin txSt vis \<equiv>
    transactionConsistent_committed origin txSt vis
  \<and> transactionConsistent_atomic origin vis"

lemma transactionConsistent_Committed:
shows "\<lbrakk>transactionConsistent origin txSt vis; c\<in>vis; origin c \<triangleq> tx; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txSt tx \<triangleq> Committed"
by (auto simp add:  transactionConsistent_def transactionConsistent_committed_def) 

lemma transactionConsistent_all_from_same:
shows "\<lbrakk>transactionConsistent origin txSt vis; c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
by (auto simp add:  transactionConsistent_def transactionConsistent_atomic_def) 

definition consistentSnapshotH where
"consistentSnapshotH s_calls s_happensBefore s_callOrigin s_txStatus vis \<equiv>
  vis \<subseteq> dom s_calls
 \<comment> \<open>  causally consistent  \<close> 
 \<and> (causallyConsistent s_happensBefore vis)
 \<comment> \<open> transaction consistent  \<close>
 \<and> (transactionConsistent s_callOrigin s_txStatus vis)
"

abbreviation consistentSnapshot where
"consistentSnapshot state vis \<equiv>
consistentSnapshotH (calls state) (happensBefore state) (callOrigin state) (txStatus state) vis"

abbreviation consistentSnapshotI where
"consistentSnapshotI state vis \<equiv>
consistentSnapshotH (calls state) (happensBefore state) (callOrigin state) (\<lambda>t. Some Committed) vis"


 text \<open>
 \DefineSnippet{causallyConsistent}{
    @{thm [display] causallyConsistent_def}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{transactionConsistent_committed}{
    @{thm [display] transactionConsistent_committed_def}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{transactionConsistent_atomic}{
    @{thm [display] transactionConsistent_atomic_def}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{transactionConsistent}{
    @{thm [display] transactionConsistent_def}
 }%EndSnippet
 \<close>


 text \<open>
 \DefineSnippet{transactionConsistent_unfolded}{
    @{thm [display] transactionConsistent_def[unfolded transactionConsistent_committed_def transactionConsistent_atomic_def]}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{consistentSnapshotH}{
    @{thm [display] consistentSnapshotH_def}
 }%EndSnippet
 \<close>

schematic_goal consistentSnapshot_def:
"consistentSnapshot S vis \<longleftrightarrow> ?x"
  by (subst consistentSnapshotH_def, rule refl)


 text \<open>
 \DefineSnippet{consistentSnapshot}{
    @{thm [display] consistentSnapshot_def}
 }%EndSnippet
 \<close>

text \<open>
 \DefineSnippet{consistentSnapshot_unfolded}{
    @{thm [display] consistentSnapshot_def[unfolded causallyConsistent_def transactionConsistent_def transactionConsistent_committed_def transactionConsistent_atomic_def]}
 }%EndSnippet
 \<close>

text \<open>
 \DefineSnippet{consistentSnapshot_unfolded2}{
    @{thm [display] consistentSnapshot_def[unfolded  transactionConsistent_def]}
 }%EndSnippet
 \<close>

lemma show_consistentSnapshot:
  assumes "vis \<subseteq> dom s_calls"
and "causallyConsistent s_happensBefore vis"
and "transactionConsistent s_callOrigin s_txStatus vis"
  shows "consistentSnapshotH s_calls s_happensBefore s_callOrigin s_txStatus vis"
  using assms by (auto simp add: consistentSnapshotH_def)



lemma chooseSnapshot_causallyConsistent_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2': "trans (happensBefore S)"
    and a3: "causallyConsistent (happensBefore S) vis"
  shows "causallyConsistent (happensBefore S) snapshot"
  using a1 a3 proof (auto simp add: chooseSnapshot_def downwardsClosure_def causallyConsistent_def, intro exI conjI, fuzzy_goal_cases A)
  case (A newTxns c1 c2 y)
  show "(c2, y) \<in> happensBefore S"
    using `(c2, c1) \<in> happensBefore S`
      `(c1, y) \<in> happensBefore S`
    by (meson  a2' transE)
  show "y \<in> callsInTransaction S newTxns"
    using ` y \<in> callsInTransaction S newTxns` .
qed



text_raw \<open>\DefineSnippet{wellFormed_state_causality}{\<close>
lemma wellFormed_state_causality:
  assumes wf: "state_wellFormed S"
  shows "\<And>s vis. visibleCalls S s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore S) vis"
    and "trans (happensBefore S)"
text_raw \<open>}%EndSnippet\<close>
  using assms  proof (induct rule: wellFormed_induct)
  case initial
  show "visibleCalls (initialState (prog S)) s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore (initialState (prog S))) vis" for s vis
    by (auto simp add: initialState_def)
  show "trans (happensBefore (initialState (prog S)))"
    by (auto simp add: initialState_def)
next
  case (step C a C')

  have causal: "causallyConsistent (happensBefore C) vis" if "visibleCalls C s \<triangleq> vis" for s vis
    using step.hyps(2) that by auto

  have "trans (happensBefore C)"
    by (simp add: step.hyps(3))

  show "trans (happensBefore C')"
  proof
    show "\<And>x y z. \<lbrakk>(x, y) \<in> happensBefore C'; (y, z) \<in> happensBefore C'\<rbrakk> \<Longrightarrow> (x, z) \<in> happensBefore C'"
      using \<open>trans (happensBefore C)\<close> \<open>C ~~ a \<leadsto> C'\<close> causal by (auto simp add: causallyConsistent_def step_simps_all elim: transE dest: wellFormed_happensBefore_calls_l[OF `state_wellFormed C`])
  qed

  show "visibleCalls C' s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore C') vis" for s vis
    using \<open>C ~~ a \<leadsto> C'\<close> causal 
  proof (induct rule: step.cases)
    case (beginAtomic S i ls f ls' t vis snapshot)

    have h1: "trans (happensBefore S)"
      using beginAtomic.hyps(1) step.hyps(3) by blast

    have h2: "causallyConsistent (happensBefore S) vis"
      using beginAtomic.hyps(1) beginAtomic.hyps(9) step.hyps(2) by blast


    from beginAtomic show ?case 
      using chooseSnapshot_causallyConsistent_preserve[OF `chooseSnapshot snapshot vis S` h1 h2]
      by (auto simp add: step_simps_all causallyConsistent_def split: if_splits)

  next
    case (dbop S i ls f Op ls' t c res vis)
    have "state_wellFormed S"
      using dbop.hyps(1) step.hyps(1) by blast

    from dbop show ?case 
      using wellFormed_visibleCallsSubsetCalls2[OF \<open>state_wellFormed S\<close>]
      by (auto simp add: step_simps_all causallyConsistent_def dest: wellFormed_happensBefore_calls_r[OF `state_wellFormed S`] split: if_splits)
  qed (auto simp add: step_simps_all causallyConsistent_def split: if_splits)

qed

text_raw \<open>\DefineSnippet{happensBefore_irrefl}{\<close>
lemma happensBefore_irrefl:
assumes wf: "state_wellFormed S"
shows "irrefl (happensBefore S)"
  text_raw \<open>}%EndSnippet\<close>
using assms  proof (induct rule: wellFormed_induct)
  case initial
  then show ?case
    by  (auto simp add: initialState_def step_simps_all irreflI)
next
  case (step t a s)
  then show ?case 
    by (auto simp add: initialState_def step_simps_all irreflI)
     (metis SigmaE2 Un_iff irrefl_def singletonD wellFormed_visibleCallsSubsetCalls2)
qed 


text_raw \<open>\DefineSnippet{wellFormed_state_transaction_consistent}{\<close>
lemma wellFormed_state_transaction_consistent:
assumes wf: "state_wellFormed S"
\<comment> \<open>contains only committed calls and calls from current transaction:\<close>
shows "\<And>s vis c tx. \<lbrakk>visibleCalls S s \<triangleq> vis; c\<in>vis; callOrigin S c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus S tx \<triangleq> Committed \<or> currentTx S s \<triangleq> tx"
\<comment> \<open>contains all calls from a transaction\<close>
  and "\<And>s vis c c'. \<lbrakk>visibleCalls S s \<triangleq> vis; c\<in>vis; callOrigin S c = callOrigin S c'\<rbrakk> \<Longrightarrow> c'\<in>vis"
\<comment> \<open>happens-before consistent with transactions\<close>
  and "\<And>x y x' y'. \<lbrakk>callOrigin S x \<noteq> callOrigin S y; callOrigin S x = callOrigin S x'; callOrigin S y = callOrigin S y' \<rbrakk> \<Longrightarrow>  (x,y) \<in> happensBefore S \<longleftrightarrow> (x', y') \<in> happensBefore S"
\<comment> \<open>happens-before only towards committed transactions or to the same transaction\<close>  
  and "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore S; callOrigin S y \<triangleq> tx; callOrigin S x \<triangleq> tx'\<rbrakk> \<Longrightarrow> txStatus S tx' \<triangleq> Committed \<or> tx' = tx"
text_raw \<open>}%EndSnippet\<close>
  using assms  proof (induct  rule: wellFormed_induct)
  case initial
  
  define init where [simp]: "init = (initialState (prog S))"
  
  show "\<And>s vis c tx. \<lbrakk>visibleCalls init s \<triangleq> vis; c\<in>vis; callOrigin init c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus init tx \<triangleq> Committed \<or> currentTx init s \<triangleq> tx"
    by (auto simp add: initialState_def )
  show "\<And>s vis c1 c2. \<lbrakk>visibleCalls init s \<triangleq> vis; c1\<in>vis; callOrigin init c1 = callOrigin init c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
    by (auto simp add: initialState_def )
  show "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin init x1 \<noteq> callOrigin init y1; callOrigin init x1 = callOrigin init x2;
                    callOrigin init y1 = callOrigin init y2\<rbrakk>
                   \<Longrightarrow> ((x1, y1) \<in> happensBefore init) = ((x2, y2) \<in> happensBefore init)"
    by (auto simp add: initialState_def )                   
  show "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore init; callOrigin init y \<triangleq> tx; callOrigin init x \<triangleq> tx'\<rbrakk> \<Longrightarrow> txStatus init tx' \<triangleq> Committed \<or> tx' = tx"
    by (auto simp add: initialState_def )
next
  case (step C a C')
  
  \<comment> \<open>contains only committed calls and calls from current transaction:\<close>
  from step 
  have IH1: "\<And>s vis c tx. \<lbrakk>visibleCalls C s \<triangleq> vis; c\<in>vis; callOrigin C c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus C tx \<triangleq> Committed \<or> currentTx C s \<triangleq> tx"
    by auto
\<comment> \<open>contains all calls from a transaction\<close>
  from step 
  have IH2: "\<And>s vis c1 c2. \<lbrakk>visibleCalls C s \<triangleq> vis; c1\<in>vis; callOrigin C c1 = callOrigin C c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
    by auto
\<comment> \<open>happens-before consistent with transactions\<close>
  from step 
  have IH3: "\<And>x y x' y'. \<lbrakk>callOrigin C x \<noteq> callOrigin C y; callOrigin C x = callOrigin C x'; callOrigin C y = callOrigin C y' \<rbrakk> \<Longrightarrow>  (x,y) \<in> happensBefore C \<longleftrightarrow> (x', y') \<in> happensBefore C"
    by blast
  then have IH3_to: "\<And>x1 y1 x2 y2. \<lbrakk>(x1,y1) \<in> happensBefore C; callOrigin C x1 = callOrigin C x2; callOrigin C y1 = callOrigin C y2; callOrigin C x1 \<noteq> callOrigin C y1 \<rbrakk> \<Longrightarrow> (x2, y2) \<in> happensBefore C"   
    by blast
\<comment> \<open>happens-before only towards committed transactions or to the same transaction\<close>  
  from step 
  have IH4: "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore C; callOrigin C y \<triangleq> tx; callOrigin C x \<triangleq> tx'\<rbrakk> \<Longrightarrow> txStatus C tx' \<triangleq> Committed \<or> tx' = tx"
    by auto
  
  have new_snapshot_cases: "(c \<in> callsInTransactionH orig txns \<down> hb) 
  \<longleftrightarrow> ((\<exists>c2 txn. (c,c2)\<in>hb \<and> orig c2 \<triangleq> txn \<and> txn\<in>txns) 
       \<or> (\<exists>txn. orig c \<triangleq> txn \<and> txn\<in>txns ))" 
    for c orig txns hb
    by (auto simp add: callsInTransactionH_def downwardsClosure_def)  
    
    
  show IH1': "txStatus C' tx \<triangleq> Committed \<or> currentTx C' s \<triangleq> tx"
    if g1: "visibleCalls C' s \<triangleq> vis" 
    and g2: "c\<in>vis" 
    and g3: "callOrigin C' c \<triangleq> tx"
    for s vis c tx
  using \<open>C ~~ a \<leadsto> C'\<close>
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using IH1 g1 g2 g3 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis using IH1 g1 g2 g3 by auto
  next
    case (beginAtomic s' ls f ls' t vis' snapshot)
    show ?thesis 
      using g1 g2 g3 proof (auto simp add: beginAtomic)

      show "currentTx C s \<triangleq> t"
        if c0: "visibleCalls C s \<triangleq> vis"
          and c1: "c \<in> vis"
          and c2: "callOrigin C c \<triangleq> t"
          and c3: "tx = t"
          and c4: "s \<noteq> s'"
        using c2 local.beginAtomic(7) step.hyps(1) wf_no_txStatus_origin_for_nothing by blast


      show "txStatus C tx \<triangleq> Committed"
        if c0: "visibleCalls C s \<triangleq> vis"
          and c1: "c \<in> vis"
          and c2: "callOrigin C c \<triangleq> tx"
          and c3: "tx \<noteq> t"
          and c4: "s \<noteq> s'"
          and c5: "currentTx C s \<noteq> Some tx"
        using IH1 c0 c2 c5 g2 by auto

      show "txStatus C tx \<triangleq> Committed"
        if a0: "snapshot = vis"
          and a1: "c \<in> vis"
          and a2: "callOrigin C c \<triangleq> tx"
          and a3: "tx \<noteq> t"
          and a4: "s = s'"
      proof (cases "c \<in> vis'")
        case True
        then show "txStatus C tx \<triangleq> Committed"
          using IH1 a2 \<open>currentTx C s' = None\<close> \<open>visibleCalls C s' \<triangleq> vis'\<close> by fastforce
      next
        case False
        from \<open>chooseSnapshot snapshot vis' C\<close>
        show "txStatus C tx \<triangleq> Committed"
        proof (rule chooseSnapshot_committed2)
          show "c \<in> snapshot"
            by (simp add: a0 g2)
          show " callOrigin C c \<triangleq> tx"
            by (simp add: a2)
          show "c \<notin> vis'" using False  .
          show "\<And>c c' tx tx'. \<lbrakk>(c', c) \<in> happensBefore C; callOrigin C c \<triangleq> tx; callOrigin C c' \<triangleq> tx'; txStatus C tx \<triangleq> Committed\<rbrakk> \<Longrightarrow> txStatus C tx' \<triangleq> Committed"
            using IH4 by blast
        qed
      qed
    qed
  next
    case (endAtomic s' ls f ls' t)
    show ?thesis 
      using g1 g2 g3 
      by (auto simp add: endAtomic) (use IH1 local.endAtomic(6) in \<open>fastforce\<close>)+
      
  next
    case (dbop s' ls f Op ls' t c' res vis')
    show ?thesis 
      using g1 g2 g3 
    proof (auto simp add: dbop split: if_splits)

      show "txStatus C tx \<triangleq> Committed"
        if c0: "s = s'"
          and c1: "c \<noteq> c'"
          and c2: "callOrigin C c \<triangleq> tx"
          and c3: "vis = insert c' vis'"
          and c4: "t \<noteq> tx"
          and c5: "c \<in> vis'"
        using IH1 c2 c4 c5 local.dbop(6) local.dbop(9) by fastforce

      show "txStatus C tx \<triangleq> Committed"
        if c0: "s \<noteq> s'"
          and c1: "visibleCalls C s \<triangleq> vis"
          and c2: "c' \<in> vis"
          and c3: "c = c'"
          and c4: "t = tx"
          and c5: "currentTx C s \<noteq> Some tx"
        using c1 c2 local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast


      show "txStatus C tx \<triangleq> Committed"
        if c0: "s \<noteq> s'"
          and c1: "visibleCalls C s \<triangleq> vis"
          and c2: "c \<in> vis"
          and c3: "c \<noteq> c'"
          and c4: "callOrigin C c \<triangleq> tx"
          and c5: "currentTx C s \<noteq> Some tx"
        using IH1 c1 c4 c5 g2 by blast
    qed
      
  next
    case (invocation s' procName initialState impl)
    show ?thesis 
      using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (crash s ls)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (invCheck res s)
    then show ?thesis using IH1 g1 g2 g3 by auto
  qed
    
  
  show IH2': "c2\<in>vis"
    if g1: "visibleCalls C' s \<triangleq> vis"
    and g2: "c1\<in>vis"
    and g3: "callOrigin C' c1 = callOrigin C' c2"
    for s vis c1 c2
  using \<open>C ~~ a \<leadsto> C'\<close>
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using IH2 g1 g2 g3 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  next
    case (beginAtomic s' ls f ls' t vis' snapshot)
    then show ?thesis  
      using g1 g2 g3 
    proof (auto split: if_splits)

      assume c0: "c1 \<in> vis"
          and c1: "callOrigin C c1 = callOrigin C c2"
          and c2: "a = (s', ABeginAtomic t vis)"
          and c3: "C' = C \<lparr>localState := localState C(s' \<mapsto> ls'), currentTx := currentTx C(s' \<mapsto> t), txStatus := txStatus C(t \<mapsto> Uncommitted), txOrigin := txOrigin C(t \<mapsto> s'), visibleCalls := visibleCalls C(s' \<mapsto> vis)\<rparr>"
          and c4: "localState C s' \<triangleq> ls"
          and c5: "currentProc C s' \<triangleq> f"
          and c6: "f ls = BeginAtomic ls'"
          and c7: "currentTx C s' = None"
          and c8: "txStatus C t = None"
          and c9: "visibleCalls C s' \<triangleq> vis'"
          and c10: "chooseSnapshot vis vis' C"
          and c11: "s = s'"
          and c12: "snapshot = vis"

      show "c2 \<in> vis"
      proof (cases "callOrigin C c1")
        case None
        then show "c2 \<in> vis"
          by (smt IH1' action.distinct(31) c2 callOrigin_same_committed domD domIff g1 g2 g3 snd_conv state_wellFormed_combine_step step.hyps(1) step.hyps(6) step.hyps(7) subsetCE txStatus_mono2 wellFormed_callOrigin_dom wellFormed_state_calls_from_current_transaction_in_vis wellFormed_visibleCallsSubsetCalls_h(2))
      next
        case (Some c1tx)
        show "c2 \<in> vis"
          using \<open>chooseSnapshot vis vis' C\<close> \<open>c1 \<in> vis\<close> 
        proof (rule chooseSnapshot_transactionConsistent)
          show "callOrigin C c1 \<triangleq> c1tx"
            by (simp add: Some)
          show "callOrigin C c2 \<triangleq> c1tx"
            using Some c1 by auto
          show "\<And>c c'. \<lbrakk>c \<in> vis'; callOrigin C c \<triangleq> c1tx; callOrigin C c' \<triangleq> c1tx\<rbrakk> \<Longrightarrow> c' \<in> vis'"
            using c9 step.hyps(3) by auto
          show "\<lbrakk>(ca, c) \<in> happensBefore C; callOrigin C c \<triangleq> tx; callOrigin C ca \<triangleq> tx'; callOrigin C cb \<triangleq> tx'; tx \<noteq> tx'\<rbrakk> \<Longrightarrow> (cb, c) \<in> happensBefore C" for  c ca cb tx tx'
            using  IH3[where x=cb and y=c and x'=ca and y'=c] by auto
        qed
      qed
    next

      show "c2 \<in> vis"
        if c0: "c1 \<in> vis"
          and c1: "callOrigin C c1 = callOrigin C c2"
          and c2: "a = (s', ABeginAtomic t snapshot)"
          and c3: "C' = C \<lparr>localState := localState C(s' \<mapsto> ls'), currentTx := currentTx C(s' \<mapsto> t), txStatus := txStatus C(t \<mapsto> Uncommitted), txOrigin := txOrigin C(t \<mapsto> s'), visibleCalls := visibleCalls C(s' \<mapsto> snapshot)\<rparr>"
          and c4: "localState C s' \<triangleq> ls"
          and c5: "currentProc C s' \<triangleq> f"
          and c6: "f ls = BeginAtomic ls'"
          and c7: "currentTx C s' = None"
          and c8: "txStatus C t = None"
          and c9: "visibleCalls C s' \<triangleq> vis'"
          and c10: "chooseSnapshot snapshot vis' C"
          and c11: "s \<noteq> s'"
          and c12: "visibleCalls C s \<triangleq> vis"
        using IH2 c1 c12 g2 by blast

    qed
      
  next
    case (endAtomic s ls f ls' t)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  next
    case (dbop s' ls f Op ls' t c res vis')
    show ?thesis  
    proof (cases "s' = s")
      case True
      then show ?thesis 
        using g1 g2 g3 
      proof (auto simp add: dbop split: if_splits, fuzzy_goal_cases A B C)
        case A
        show ?case
          by (metis A.Some_eq A.not_member local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_state_calls_from_current_transaction_in_vis)
      next case B
        show ?case
          using B.member local.dbop(7) local.dbop(9) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast
      next case C
        show ?case
          using C.callOrigin_eq C.member C.not_member IH2 local.dbop(9) by blast
      qed

      
    next
      case False

      have not_committed_h: "txStatus C t \<noteq> Some Committed" if "c1 \<in> vis"
        using local.dbop(6) not_uncommitted_cases step.hyps(1) wellFormed_currentTxUncommitted by blast
      
      show ?thesis 
        using False g1 g2 g3 
      proof (auto simp add: dbop split: if_splits, fuzzy_goal_cases A B C)
       case A
       show ?case
         using A.callOrigin_eq A.visibleCalls_eq False IH1 g2 local.dbop(6) not_committed_h step.hyps(1) wellFormed_currentTx_unique by blast
      next case B
        show ?case
          using B.member B.visibleCalls_eq local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast
      next case C
        show ?case
          using C.callOrigin_eq C.visibleCalls_eq IH2 g2 by blast
      qed
    qed
  next
    case (invocation s procName initialState impl)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (crash s ls)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (invCheck res s)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  qed
  
  show IH4': "txStatus C' tx' \<triangleq> Committed \<or> tx' = tx"
      if g1: "(x,y)\<in>happensBefore C'"
      and g2: "callOrigin C' y \<triangleq> tx"
      and g3: "callOrigin C' x \<triangleq> tx'"
      for x y tx tx'
  using \<open>C ~~ a \<leadsto> C'\<close>
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (beginAtomic s ls f ls' t vis snapshot)
    show ?thesis 
      using g1 g2 g3 
    proof (auto simp add: beginAtomic split: if_splits, fuzzy_goal_cases A B)
      case A show ?case
        using A.callOrigin_eq2 local.beginAtomic(7) step.hyps(1) wf_no_txStatus_origin_for_nothing by blast
    next case B show ?case
        using B.callOrigin_eq B.callOrigin_eq2 B.member B.not_tx'___def2 IH4 by auto
    qed
      
  next
    case (endAtomic s ls f ls' t)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (dbop s ls f Op ls' t c res vis)
    show ?thesis 
      using g1 g2 g3 
    proof (auto simp add: dbop split: if_splits, fuzzy_goal_cases A B C D)
      case A show ?case
        using A.member local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_r by blast
    next case B show ?case
        using B.callOrigin_eq B.member B.not_tx'___def B.t___def IH1 local.dbop(6) local.dbop(9) by fastforce
    next case C show ?case
        using C.member local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
    next case D show ?case
        using D.callOrigin_eq D.callOrigin_eq2 D.member D.not_tx'___def IH4 by blast
    qed
      
  next
    case (invocation s procName initialState impl)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (return s ls f res)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (crash s ls)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (invCheck res s)
    then show ?thesis using g1 g2 g3 IH4 by auto
  qed    
      
  show IH3': "(x1,y1) \<in> happensBefore C' \<longleftrightarrow> (x2, y2) \<in> happensBefore C'"
    if  g1: "callOrigin C' x1 \<noteq> callOrigin C' y1"
    and g2: "callOrigin C' x1 = callOrigin C' x2"
    and g3: "callOrigin C' y1 = callOrigin C' y2 "
    for x1 y1 x2 y2 
  proof -  
    have whenUnchanged: "(x1,y1) \<in> happensBefore C' \<longleftrightarrow> (x2, y2) \<in> happensBefore C'"  
      if "happensBefore C' = happensBefore C" and "callOrigin C' = callOrigin C"
      using that
      by (metis IH3 g1 g2 g3) 
  
    show "(x1,y1) \<in> happensBefore C' \<longleftrightarrow> (x2, y2) \<in> happensBefore C'"
    using \<open>C ~~ a \<leadsto> C'\<close>
    proof (cases rule: step.cases)
      case (local s ls f ls')
      then show ?thesis using whenUnchanged by auto
    next
      case (newId s ls f ls' uid)
      then show ?thesis using whenUnchanged by auto
    next
      case (beginAtomic s ls f ls' t vis snapshot)
      then show ?thesis using whenUnchanged by auto
    next
      case (endAtomic s ls f ls' t)
      then show ?thesis using whenUnchanged by auto
    next
      case (dbop s ls f Op ls' t c res vis)
      
      from \<open>calls C c = None\<close>
      have c_no_hb1[simp]: "(x, c) \<notin> happensBefore C" for x
        using wellFormed_visibleCallsSubsetCalls_h(1)[OF \<open>state_wellFormed C\<close>] by auto
        
      have [simp]: "callOrigin C c = None"
        by (simp add: local.dbop(7) step.hyps(1) wf_callOrigin_and_calls)
        
      have t_uncomited[simp]:  "txStatus C t \<triangleq> Uncommitted"
          using local.dbop(6) step.hyps(1) wellFormed_currentTxUncommitted by blast
      
      have origin_t: "callOrigin C y2 \<triangleq> t" 
            if "callOrigin C y1 = callOrigin C y2"
            and "callOrigin C x1 \<triangleq> t"
            and "(x1, y1) \<in> happensBefore C"
            for x1 y1 y2
            by (metis IH3_to \<open>callOrigin C c = None\<close> \<open>txStatus C t \<triangleq> Uncommitted\<close> that c_no_hb1 not_None_eq option.inject step.hyps(5) txStatus.distinct(1))      
          
      show ?thesis 
        using g1 g2 g3  proof (auto simp add: dbop split: if_splits)
        show "\<lbrakk>y1 = c; y2 = c; callOrigin C x2 \<noteq> Some t; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; x1 \<in> vis\<rbrakk> \<Longrightarrow> x2 \<in> vis"
          using IH2 local.dbop(9) by blast
        show "\<lbrakk>y1 = c; y2 = c; callOrigin C x2 \<noteq> Some t; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; x2 \<in> vis\<rbrakk> \<Longrightarrow> x1 \<in> vis"
          using IH2 local.dbop(9) by auto
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 \<triangleq> t; y2 = c; callOrigin C x2 \<noteq> Some t; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; (x1, y1) \<in> happensBefore C\<rbrakk> \<Longrightarrow> x2 \<in> vis"
          by (smt IH3_to causallyConsistent_def local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_state_calls_from_current_transaction_in_vis wellFormed_state_causality(1))
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 \<triangleq> t; y2 = c; callOrigin C x2 \<noteq> Some t; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; x2 \<in> vis\<rbrakk> \<Longrightarrow> (x1, y1) \<in> happensBefore C"
          using IH2 local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_happensBefore_vis by fastforce
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; Some t \<noteq> callOrigin C y2; x2 = c; x1 = c; (c, y1) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (c, y2) \<in> happensBefore C"
          using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; Some t \<noteq> callOrigin C y2; x2 = c; x1 = c; (c, y2) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (c, y1) \<in> happensBefore C"
          using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; Some t \<noteq> callOrigin C y2; x2 = c; x1 \<noteq> c; callOrigin C x1 \<triangleq> t; (x1, y1) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (c, y2) \<in> happensBefore C"
          by (metis origin_t)
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; Some t \<noteq> callOrigin C y2; x2 = c; x1 \<noteq> c; callOrigin C x1 \<triangleq> t; (c, y2) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (x1, y1) \<in> happensBefore C"
          using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
        show "\<lbrakk>y1 = c; Some t = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; x1 \<in> vis\<rbrakk> \<Longrightarrow> (x2, y2) \<in> happensBefore C"
          by (metis IH2 local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_happensBefore_vis)
        show "\<lbrakk>y1 = c; Some t = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; (x2, y2) \<in> happensBefore C\<rbrakk> \<Longrightarrow> x1 \<in> vis"
          by (metis IH2 causallyConsistent_def local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_state_calls_from_current_transaction_in_vis wellFormed_state_causality(1))
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 = c; Some t = callOrigin C x2; (c, y1) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (x2, y2) \<in> happensBefore C"
          using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 = c; Some t = callOrigin C x2; (x2, y2) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (c, y1) \<in> happensBefore C"
          using origin_t by fastforce
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; (x1, y1) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (x2, y2) \<in> happensBefore C"
          by (metis IH3)
        show "\<lbrakk>y1 \<noteq> c; callOrigin C y1 = callOrigin C y2; y2 \<noteq> c; callOrigin C x2 \<noteq> callOrigin C y2; x2 \<noteq> c; x1 \<noteq> c; callOrigin C x1 = callOrigin C x2; (x2, y2) \<in> happensBefore C\<rbrakk> \<Longrightarrow> (x1, y1) \<in> happensBefore C"
          by (simp add: IH3_to)
      qed
    next
      case (invocation s procName initialState impl)
      then show ?thesis using whenUnchanged by auto
    next
      case (return s ls f res)
      then show ?thesis using whenUnchanged by auto
    next
      case (crash s ls)
      then show ?thesis using whenUnchanged by auto
    next
      case (invCheck res s)
      then show ?thesis using whenUnchanged by auto
    qed
  qed
qed  


lemma show_transactionConsistent[case_names only_committed[in_vis origin_tx] all_from_same[in_vis origin_same]]:
assumes "\<And>c tx. \<lbrakk>c\<in>vis; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txSt tx \<triangleq> Committed"
    and "\<And>c1 c2. \<lbrakk>c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
shows "transactionConsistent origin txSt vis"
  using assms by (auto simp add: transactionConsistent_def transactionConsistent_atomic_def transactionConsistent_committed_def)


text_raw \<open>\DefineSnippet{wellFormed_state_consistent_snapshot}{\<close>
lemma wellFormed_state_consistent_snapshot:
assumes wf: "state_wellFormed S"
assumes vis: "visibleCalls S s \<triangleq> vis"
assumes noTx: "\<And>c tx. currentTx S s \<triangleq> tx \<Longrightarrow> callOrigin S c \<noteq> Some tx" 
shows "consistentSnapshot S vis"
  text_raw \<open>}%EndSnippet\<close>
unfolding consistentSnapshotH_def proof (intro conjI)
  show "vis \<subseteq> dom (calls S)"
    using wf vis
    using wellFormed_visibleCallsSubsetCalls_h(2) by fastforce 
    
  show "causallyConsistent (happensBefore S) vis"
    using local.wf vis wellFormed_state_causality(1) by auto
    
  show "transactionConsistent (callOrigin S) (txStatus S) vis"
    unfolding transactionConsistent_def transactionConsistent_atomic_def transactionConsistent_committed_def
    using wellFormed_state_transaction_consistent[OF wf] noTx vis
    by meson
qed



text_raw \<open>\DefineSnippet{happensBefore_transitive}{\<close>
lemma happensBefore_transitive:
assumes wf: "state_wellFormed S"
shows "trans (happensBefore S)"
  text_raw \<open>}%EndSnippet\<close>
  using local.wf wellFormed_state_causality(2) by blast




text_raw \<open>\DefineSnippet{happensBefore_acyclic}{\<close>
lemma happensBefore_acyclic:
assumes wf: "state_wellFormed S"
shows "acyclic (happensBefore S)"
  text_raw \<open>}%EndSnippet\<close>
  by (auto simp add: acyclic_irrefl trancl_id[OF happensBefore_transitive[OF wf]] happensBefore_irrefl[OF wf])



text_raw \<open>\DefineSnippet{causallyConsistent_downwards}{\<close>
lemma causallyConsistent_downwards:
  assumes  cs: "causallyConsistent hb vis"
    and trans: "trans hb"
shows "causallyConsistent hb (vis \<union> S \<down> hb)"
text_raw \<open>}%EndSnippet\<close>
proof -
  show ?thesis
    using cs 
    by (auto simp add: causallyConsistent_def downwardsClosure_def)
      (meson local.trans transE)
qed

lemma wf_vis_downwards_closed:
  assumes wf: "state_wellFormed S"
    and "trans (happensBefore S)"
    and "visibleCalls S i \<triangleq> Vis"
    and "(X,Y) \<in> happensBefore S"
    and "Y\<in>Vis"
  shows "X\<in>Vis"
  by (meson assms causallyConsistent_def local.wf wellFormed_state_causality(1))


text_raw \<open>\DefineSnippet{wf_causallyConsistent1}{\<close>
lemma wf_causallyConsistent1:
  assumes wf: "state_wellFormed S"
    and "visibleCalls S i \<triangleq> vis"
  shows "causallyConsistent (happensBefore S) vis"
text_raw \<open>}%EndSnippet\<close>
  using assms(2) local.wf wellFormed_state_causality(1) by blast


lemma wf_vis_downwards_closed2:
  assumes wf: "state_wellFormed S"
    and "visibleCalls S i \<triangleq> Vis"
    and "(X,Y) \<in> happensBefore S"
    and "Y\<in>Vis"
  shows "X\<in>Vis"
  using assms(2) assms(3) assms(4) happensBefore_transitive local.wf wf_vis_downwards_closed by blast






lemma wf_happensBefore_txns_left: 
  assumes wf: "state_wellFormed S"
  assumes "(x,y) \<in> happensBefore S"
    and "callOrigin S x = callOrigin S x'"
    and "callOrigin S x \<noteq> callOrigin S y"
  shows "(x',y) \<in> happensBefore S"
  using assms(2) assms(3) assms(4) local.wf wellFormed_state_transaction_consistent(3) by blast

lemma wf_transactionConsistent1:
  assumes wf: "state_wellFormed S"
    and "visibleCalls S i \<triangleq> vis"
    and "c\<in>vis"
    and "callOrigin S c \<triangleq> tx"
    and "currentTx S i \<noteq> Some tx"
  shows "txStatus S tx \<triangleq> Committed"
  using assms(2) assms(3) assms(4) assms(5) local.wf wellFormed_state_transaction_consistent(1) by blast



lemma happensBefore_not_refl:
  assumes "state_wellFormed S"
  shows "(c,c) \<notin> happensBefore S"
  by (meson assms happensBefore_irrefl irrefl_def)


lemma happensBefore_finite:
  assumes "state_wellFormed S"
  shows "finite (happensBefore S)"
proof (rule finite_subset)
  show "happensBefore S \<subseteq> dom (calls S) \<times> dom (calls S) "
    by (simp add: assms wellFormed_visibleCallsSubsetCalls_h(1))

  show "finite (dom (calls S) \<times> dom (calls S))"
    by (simp add: assms wf_finite_calls)
qed




lemma happensBefore_wf:
  assumes "state_wellFormed S"
  shows "wf ((happensBefore S)\<inverse>)"
proof (rule finite_acyclic_wf)
  show "finite ((happensBefore S)\<inverse>)"
    by (simp add: assms happensBefore_finite)

  show "acyclic ((happensBefore S)\<inverse>)"
  proof
    show "acyclic (happensBefore S)"
      by (simp add: assms happensBefore_acyclic)
  qed
qed

end


