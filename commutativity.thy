section \<open>Commutativity in Executions\<close>
theory commutativity
  imports repliss_sem prefix
    "HOL-Eisbach.Eisbach"
    execution_invariants
    invContext_simps
begin


text \<open>This theory proves commutativity between certain actions in executions.\<close>



definition commutativeS :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> invocId \<times> ('proc, 'operation, 'any) action \<Rightarrow> invocId \<times> ('proc, 'operation, 'any) action \<Rightarrow> bool" where
  "commutativeS s a b \<equiv> (\<forall>t. ((s ~~ [a,b] \<leadsto>*  t) \<longleftrightarrow> (s ~~ [b,a] \<leadsto>* t)))"


lemma useCommutativeS:
  assumes "commutativeS s a b"
  shows "(s ~~ [a,b] \<leadsto>*  t) \<longleftrightarrow> (s ~~ [b,a] \<leadsto>* t)"
  using assms by (simp add: commutativeS_def)


definition "precondition a C \<equiv> \<exists>C'. C ~~ a \<leadsto> C'"

lemma usePrecondition: "precondition a C \<Longrightarrow> \<exists>C'. C ~~ a \<leadsto> C'"
  by (simp add: precondition_def)

lemma usePrecondition2: "precondition a C \<Longrightarrow> (\<And>C'. C ~~ a \<leadsto> C' \<Longrightarrow> P C') \<Longrightarrow> \<exists>C'. (C ~~ a \<leadsto> C') \<and> P C'"
  using usePrecondition by blast

lemma commutativeS_switchArgs: 
  "commutativeS s a b \<longleftrightarrow> commutativeS s b a"
  by (auto simp add: commutativeS_def)


lemma preconditionI: "\<lbrakk>s ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> precondition a s"
  by (auto simp add: precondition_def)

lemma show_commutativeS[case_names preAB preBA commute ]: 
  assumes a1:  "\<And>s1 s2. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ b \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ a \<leadsto> s2)" 
    and a2:  "\<And>s1 s2. \<lbrakk>s ~~ b \<leadsto> s1; s1 ~~ a \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ a \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ b \<leadsto> s2)" 
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
  shows "commutativeS s a b"
  by (auto simp add: commutativeS_def  steps_appendFront,
      insert a1 a4, blast,
      insert a2 a4, blast)

lemma show_commutativeS_pres[case_names preBfront preAfront preAback preBback commute ]: 
  assumes a1:  "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s1\<rbrakk> \<Longrightarrow> precondition b s"
    and a1': "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s1\<rbrakk> \<Longrightarrow> precondition a s"
    and a2:  "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s\<rbrakk> \<Longrightarrow> precondition a s1"
    and a2': "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s\<rbrakk> \<Longrightarrow> precondition b s1"
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
  shows "commutativeS s a b"
proof (auto simp add: commutativeS_def precondition_def steps_appendFront steps_empty; rule usePrecondition2)
  show "precondition b s"
    if c0: "s ~~ a \<leadsto> B"
      and c1: "B ~~ b \<leadsto> t"
    for  t B
    using a1 c0 c1 preconditionI by blast

  show "Ba ~~ a \<leadsto> t"
    if c0: "s ~~ a \<leadsto> B"
      and c1: "B ~~ b \<leadsto> t"
      and c2: "s ~~ b \<leadsto> Ba"
    for  t B Ba
    by (metis a2 a4 c0 c1 c2 preconditionI usePrecondition)

  show "precondition a s"
    if c0: "s ~~ b \<leadsto> B"
      and c1: "B ~~ a \<leadsto> t"
    for  t B
    using a1' c0 c1 preconditionI by blast

  show "Ba ~~ b \<leadsto> t"
    if c0: "s ~~ b \<leadsto> B"
      and c1: "B ~~ a \<leadsto> t"
      and c2: "s ~~ a \<leadsto> Ba"
    for  t B Ba
    by (metis a2' a4 c0 c1 c2 preconditionI usePrecondition)
qed


definition differentIds :: "(invocId \<times> ('proc, 'operation, 'any) action) \<Rightarrow> (invocId \<times> ('proc, 'operation, 'any) action) \<Rightarrow> bool" where
  "differentIds a b \<equiv> case (a,b) of
   ((s1, ANewId u1), (s2, ANewId u2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ABeginAtomic u1 nt1), (s2, ABeginAtomic u2 nt2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ADbOp u1 o1 r1), (s2, ADbOp u2 o2 r2)) \<Rightarrow> (u1 \<noteq> u2)
 | _ \<Rightarrow> True"

lemma differentIds_newId:
  "differentIds (s1, ANewId u1) (s2, ANewId u2) \<longleftrightarrow> (u1 \<noteq> u2)"
  by (simp add: differentIds_def)

lemma differentIds_beginAtomic:
  "differentIds (s1, ABeginAtomic u1 nt1) (s2, ABeginAtomic u2 nt2) \<longleftrightarrow> (u1 \<noteq> u2)"
  by (simp add: differentIds_def)

lemma differentIds_dbop:
  "differentIds (s1, ADbOp u1 o1 r1) (s2, ADbOp u2 o2 r2) \<longleftrightarrow> (u1 \<noteq> u2)"
  by (simp add: differentIds_def)

lemma steps_to_differentIds: 
  assumes step1: "s ~~ (sa,a) \<leadsto> B" and step2: "B ~~ (sb,b) \<leadsto> t"
  shows "differentIds (sa,a) (sb,b)"
  by (cases a; cases b;
      insert step1 step2,
      auto simp add: differentIds_def step_simps split: if_splits)

lemma steps_to_differentIds2: 
  assumes step1: "s ~~ a \<leadsto> B" and step2: "B ~~ b \<leadsto> t"
  shows "differentIds a b"
  by (metis prod.swap_def step1 step2 steps_to_differentIds swap_swap)

lemma differentIds_commute: 
  shows "differentIds a b = differentIds b a"
  by (auto simp add: differentIds_def split: action.splits)


lemma show_commutativeS_pres2[case_names preBfront preAfront preAback preBback commute ]: 
  assumes a1:  "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s1; differentIds a b\<rbrakk> \<Longrightarrow> precondition b s"
    and a1': "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s1; differentIds a b\<rbrakk> \<Longrightarrow> precondition a s"
    and a2:  "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s; differentIds a b\<rbrakk> \<Longrightarrow> precondition a s1"
    and a2': "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s; differentIds a b\<rbrakk> \<Longrightarrow> precondition b s1"
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
  shows "commutativeS s a b"
proof (auto simp add: commutativeS_def precondition_def steps_appendFront steps_empty)
  fix t B
  assume step1: "s ~~ a \<leadsto> B" and step2: "B ~~ b \<leadsto> t"

  then have dIds: "differentIds a b"
    using steps_to_differentIds2 by blast

  show "\<exists>B. (s ~~ b \<leadsto> B) \<and> (B ~~ a \<leadsto> t)"
    by (metis a1 a2 a4 dIds preconditionI step1 step2 usePrecondition)
next   
  fix t B
  assume step1: "s ~~ b \<leadsto> B" and step2: "B ~~ a \<leadsto> t"

  then have dIds: "differentIds a b"
    using steps_to_differentIds2
    using differentIds_commute by blast 

  show "\<exists>B. (s ~~ a \<leadsto> B) \<and> (B ~~ b \<leadsto> t)"
    by (metis a1' a2' a4 dIds preconditionI step1 step2 usePrecondition)
qed  


lemma precondition_alocal:
  "precondition (s, ALocal) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = LocalStep ls')"
  by (auto simp add: precondition_def intro: step.intros elim: step_elims)


lemma precondition_newid:
  "precondition (s, ANewId uid) C = (\<exists>ls f ls' ls''.
     localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = NewId ls' 
   \<and>  generatedIds C (to_nat uid) = None \<and> uniqueIds uid = {to_nat uid} 
   \<and>  ls' uid \<triangleq> ls'')"
  by (auto simp add: precondition_def intro: step.intros elim!: step_elims)


lemma precondition_beginAtomic:
  "precondition (s, ABeginAtomic tx snapshot) C = 
    (\<exists>ls f ls' vis. 
        localState C s \<triangleq> ls 
      \<and> currentProc C s \<triangleq> f 
      \<and> f ls = BeginAtomic ls' 
      \<and> currentTransaction C s = None 
      \<and> transactionStatus C tx = None
      \<and> visibleCalls C s \<triangleq> vis
      \<and> chooseSnapshot snapshot vis C)"
  by (auto simp add: precondition_def step_simps )

lemma precondition_endAtomic:
  "precondition (s, AEndAtomic) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = EndAtomic ls' \<and> currentTransaction C s \<noteq> None)"
  by (auto simp add: precondition_def intro: step.intros elim!: step_elims)

lemma precondition_invoc:
  "precondition (s, AInvoc proc) C = (localState C s = None \<and> uniqueIds proc \<subseteq> knownIds C \<and> invocationOp C s = None)"
  by (auto simp add: precondition_def step.simps)


lemma precondition_dbop:
  "precondition (s, ADbOp c operation  res) C = (\<exists>ls f ls' t vis. calls C c = None \<and> localState C s \<triangleq> ls 
    \<and> currentProc C s \<triangleq> f \<and> f ls = DbOperation operation  ls' \<and> currentTransaction C s \<triangleq> t \<and> querySpec (prog C) operation  (getContext C s) res \<and> visibleCalls C s \<triangleq> vis)"
  by (auto simp add: precondition_def intro: step.intros elim!: step_elims)



lemma precondition_return:
  "precondition (s, AReturn res) C = (\<exists>ls f. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = Return res \<and> currentTransaction C s = None)"
  by (auto simp add: precondition_def intro: step.intros elim!: step_elims)

lemma precondition_fail:
  "precondition (s, AFail) C = (\<exists>ls. localState C s \<triangleq> ls)" \<comment> \<open>failures occur wherever something is running ;)\<close>
  by (auto simp add: precondition_def intro: step.intros elim!: step_elims)

lemma precondition_invcheck:
  "precondition (s, AInvcheck res) C \<longleftrightarrow> (res = invariant (prog C) (invContext C))"
  by (auto simp add: precondition_def step_simps intro: step.intros elim!: step_elims)



lemma commutativePreservesPrecondition:
  assumes preconditionHolds: "precondition (sb,b) B"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommitted: "transactionStatus A tx \<triangleq> Uncommitted"
    and aIsInLocal: "localState A sa \<triangleq> lsa"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
  shows "precondition (sb,b) A"
proof -

  have origin_inv: "dom (callOrigin A) = dom (calls A)"
    by (simp add: wellFormed wellFormed_callOrigin_dom)

  have visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    by (simp add: wellFormed wellFormed_visibleCallsSubsetCalls_h(2))

  from exec
  have committed_same: "transactionStatus A t \<triangleq> Committed \<longleftrightarrow> transactionStatus B t \<triangleq> Committed" for t
    using aIsNotCommit committed_same by blast

  from exec
  have callOrigin_same_committed: "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx" if "transactionStatus A tx \<triangleq> Committed " for c tx
    using callOrigin_same_committed that wellFormed by blast    

  from exec
  have happensBefore_same_committed2: "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
    if "transactionStatus A tx \<triangleq> Committed " 
      and "callOrigin A y \<triangleq> tx"
    for tx x y
    using that happensBefore_same_committed2 wellFormed by blast 

  show ?thesis
  proof (cases b)
    case ALocal
    show ?thesis using precondition_alocal unchangedInTransaction
      by (metis ALocal differentSessions exec preconditionHolds) 

  next
    case (ANewId x2)
    with preconditionHolds
    obtain ls f ls' ls''
      where 1: "localState B sb \<triangleq> ls" 
        and 2: "currentProc B sb \<triangleq> f" 
        and 3: "generatedIds B (to_nat x2) = None" 
        and 4: "f ls = NewId ls'"
        and 6: "uniqueIds x2 = {to_nat x2}"
        and 7: "ls' x2 \<triangleq> ls''"
      by (auto simp add: precondition_newid)
    have 5: "generatedIds A (to_nat x2) = None"
      using generatedIds_mono2_rev[OF 3 exec] by blast
    then show ?thesis
      by (metis "1" "2" 4 6 7 ANewId differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
  next
    case (ABeginAtomic tx snapshot)
    with preconditionHolds obtain ls f ls' vis
      where 1: "localState B sb \<triangleq> ls"
        and 2: "currentProc B sb \<triangleq> f"
        and 3: "f ls = BeginAtomic ls'"
        and 4: "currentTransaction B sb = None"
        and 5: "transactionStatus B tx = None"
        and 6: "chooseSnapshot snapshot vis B"
        and 7: "visibleCalls B sb \<triangleq> vis"
      by (auto simp add: precondition_beginAtomic)
    have tx_none: "transactionStatus A tx = None" using transactionStatus_mono' 5 exec by blast 
    show ?thesis 
      using exec differentSessions differentSessions[symmetric] 1 2 3 4 5 6 7 tx_none txIsUncommitted wellFormed 
      by (auto simp add: wellFormed_callOrigin_dom2 aIsInTransaction aIsNotCommit step.simps \<open>b = ABeginAtomic tx snapshot\<close> precondition_beginAtomic elim!: chooseSnapshot_unchanged_precise split: if_splits)

  next
    case AEndAtomic
    then show ?thesis
      by (metis differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3))
  next
    case (ADbOp callId operation res)
    with preconditionHolds obtain ls f ls' vis t 
      where 1: "calls B callId = None"
        and 2: "localState B sb \<triangleq> ls"
        and 3: "currentProc B sb \<triangleq> f"
        and 4: "f ls = DbOperation operation  ls'"
        and 5: "currentTransaction B sb \<triangleq> t"
        and 6: "querySpec (prog B) operation  (getContext B sb) res"
        and 7: "visibleCalls B sb \<triangleq> vis"
      by (auto simp add: precondition_dbop)
    moreover have "calls A callId = None"
      using "1" calls_mono' exec by blast   
    moreover have "prog B = prog A"
      using exec prog_inv by auto  
    moreover have "getContext B sb = getContext A sb"
      by (metis aIsInTransaction differentSessions exec unchangedInTransaction_getContext visibleCalls_inv) 
    ultimately show ?thesis  using unchangedInTransaction
      by (smt ADbOp aIsInTransaction differentSessions exec precondition_dbop)

  next
    case (AInvoc proc)
    with preconditionHolds 
      have "invocationOp B sb = None"
        and "localState B sb = None"
        and "uniqueIds proc \<subseteq> knownIds B"
      by (auto simp add: precondition_invoc)
    moreover have "invocationOp A sb = None"
      using aIsInTransaction calculation(1) differentSessions exec unchangedInTransaction(5) by fastforce

    ultimately show ?thesis using unchangedInTransaction
      by (smt AInvoc aIsInTransaction differentSessions exec precondition_invoc prog_inv)
  next
    case (AReturn x8)
    then show ?thesis
      by (metis differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
  next
    case AFail
    then show ?thesis
      by (metis differentSessions exec preconditionHolds precondition_fail unchangedInTransaction(1))
  next
    case (AInvcheck res)
    with preconditionHolds 
    have 2: "res = invariant (prog B) (invContext B)"
      by (auto simp add: precondition_invcheck)

    have invContextSame: "(invContext A) = (invContext B)"
      using aIsInTransaction aIsNotCommit exec invContextSnapshot_same txIsUncommitted wellFormed by blast

    have "precondition (sb, AInvcheck res) A"  
      using prog_inv[OF exec] by (auto simp add: precondition_invcheck  committed_same 2 invContextSame)

    then show ?thesis
      using AInvcheck by blast  

  qed
qed


lemma commutative_ALocal_other:
  assumes a1: "sa \<noteq> sb"
  shows "commutativeS S (sa, ALocal) (sb, a)"
  by (cases a, auto simp add: commutativeS_def steps_simps steps_empty a1 a1[symmetric] fun_upd_twist elim!: chooseSnapshot_unchanged_precise)


lemma commutative_other_ALocal:
  assumes a1: "sa \<noteq> sb"
  shows "commutativeS S (sa, a) (sb, ALocal)"
  using assms commutativeS_switchArgs  by (metis commutative_ALocal_other)



lemma step_existsH:
  "\<lbrakk>precondition a A; \<And>B. A ~~ a \<leadsto> B \<Longrightarrow> P B \<rbrakk> \<Longrightarrow> \<exists>B. (A ~~ a \<leadsto> B) \<and> P B"
  using usePrecondition by blast


lemma commutative_Dbop_other:
  assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
  shows "commutativeS S (sa, ADbOp c operation res) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis  by (simp add: commutative_other_ALocal)
next
  case (ANewId x2)
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)


next
  case AEndAtomic
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case AFail
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront  a1[symmetric]  step_simps fun_upd_twist)
next
  case (AInvoc p)
  show ?thesis 
  proof (induct rule: show_commutativeS_pres)
    case (preBfront s1)
    then show ?case 
      by (auto simp add: AInvoc precondition_invoc step_simps split: if_splits)
  next
    case (preAfront s1)
    then show ?case 
      by (auto simp add: AInvoc precondition_dbop step_simps)
  next
    case (preAback s1)
    then show ?case 
      by (auto simp add: AInvoc precondition_dbop step_simps)
  next
    case (preBback s1)
    then show ?case 
      by (auto simp add: AInvoc precondition_invoc step_simps)
  next
    case (commute s1 s2 s1' s2')
    then show ?case 
      by (auto simp add: AInvoc commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
  qed

next
  case (AReturn x8)
  show ?thesis 
    by (rule show_commutativeS_pres,
        auto simp add: AReturn precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)

next
  case (AInvcheck res)
  show ?thesis 
    by (rule show_commutativeS_pres, auto simp add: a2 AInvcheck precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist subset_eq invContextH_simps  wellFormed_currentTransactionUncommitted   invContext_unchanged_happensBefore     invContext_unchanged_happensBefore2 
 wellFormed_callOrigin_dom3 wellFormed_currentTransaction_unique_h(2))


next
  case (ADbOp c' operation'  res')
  show ?thesis 
    by (rule show_commutativeS_pres2; insert ADbOp a2,
        auto simp add: precondition_dbop a1[symmetric] step_simps 
        wellFormed_visibleCallsSubsetCalls2 state_ext differentIds_dbop 
        getContextH_visUpdate getContextH_callsUpdate
        split: if_splits)
next
next
  case (ABeginAtomic tx txns)
  then have a_def[simp]: "a = ABeginAtomic tx txns" .
      \<comment> \<open>case (APull txns)\<close>
  show ?thesis
  proof (induct rule: show_commutativeS_pres2)
    case (preBfront s1)
    then show "precondition (sb, a) S" 
      using a2 by (auto simp add: wellFormed_callOrigin_dom2 wellFormed_currentTransactionUncommitted precondition_dbop precondition_beginAtomic step_simps split: if_splits elim!: chooseSnapshot_unchanged_precise)

  next
    case (preAfront s1)
    then show "precondition (sa, ADbOp c operation res) S" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps)
  next
    case (preAback s1)
    then show "precondition (sa, ADbOp c operation res) s1" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps)
  next
    case (preBback s1)
    then show "precondition (sb, a) s1" 
      using a2 by (auto simp add: wellFormed_currentTransaction_unique_h(2) wellFormed_callOrigin_dom2 precondition_dbop precondition_beginAtomic step_simps split: if_splits elim!: chooseSnapshot_unchanged_precise)
      

  next
    case (commute s1 s2 s1' s2')
    then have step1: "S ~~ (sa, ADbOp c operation res) \<leadsto> s1"
      and step2: "s1 ~~ (sb, ABeginAtomic tx txns) \<leadsto> s2"
      and step3: "S ~~ (sb, ABeginAtomic tx txns) \<leadsto> s1'"
      and step4: "s1' ~~ (sa, ADbOp c operation  res) \<leadsto> s2'"
      by auto
    show "s2 = s2'" 
      by (insert step1, auto simp add: step_simps,
          insert step3, auto simp add: step_simps,
          insert step2, auto simp add: step_simps,
          insert step4, auto simp add: step_simps,
          auto simp add: step_simps a1[symmetric] state_updates_normalize  intro!: show_state_calls_eq)
  qed
qed

lemma commutative_newId_other:
  assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
  shows "commutativeS S (sa, ANewId uid) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis by (simp add: commutative_other_ALocal)
next
  case (ANewId x2)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (ABeginAtomic x3)
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute elim!: chooseSnapshot_unchanged_precise)

next
  case AEndAtomic
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (ADbOp )
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_Dbop_other by metis
next
  case (AInvoc )
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (AReturn x8)
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case AFail
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (AInvcheck x10)
  then show ?thesis by (auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
qed

lemma commutative_fail_other:
  assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
  shows "commutativeS S (sa, AFail) (sb, a)"
  by (cases a, auto simp add: steps_empty commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute elim!: chooseSnapshot_unchanged_precise)



lemma commutative_beginAtomic_other:
  assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
    and no_end_atomic: "a \<noteq> AEndAtomic" 
  shows "commutativeS S (sa, ABeginAtomic t newTxns) (sb, a)"
proof -
  have a1'[simp]: "sb \<noteq> sa" using a1 ..
  show "?thesis"
  proof (cases a)
    case ALocal
    then show ?thesis
      by (simp add: commutative_other_ALocal)
  next
    case (ANewId x2)
    then show ?thesis
      using a1 a2 commutativeS_switchArgs commutative_newId_other
      by metis 
  next
    case (ABeginAtomic t txns)
    show ?thesis 
      by (rule show_commutativeS, 
        auto simp add: ABeginAtomic step_simps contra_subsetD split: if_splits elim!: chooseSnapshot_unchanged_precise, 
        subst state_ext;
        auto simp add: ABeginAtomic step_simps contra_subsetD split: if_splits elim!: chooseSnapshot_unchanged_precise)


  next
    case AEndAtomic \<comment> \<open>this is not commutative, since the transaction committed could be included in ht next snapshot\<close>
    then show ?thesis
      using no_end_atomic by auto 
  next
    case (ADbOp )
    then show ?thesis
      using a1 a2 commutativeS_switchArgs commutative_Dbop_other by metis 
        (**next
  case (APull x6)
  then show ?thesis 
  by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute,
    auto, smt mem_Collect_eq option.inject subsetCE transactionStatus.distinct(1))*)
  next
    case (AInvoc)
    then show ?thesis by (auto simp add: steps_empty a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits elim!: chooseSnapshot_unchanged_precise)
  next
    case (AReturn x8)
    then show ?thesis by (auto simp add: steps_empty a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits elim!: chooseSnapshot_unchanged_precise)
  next
    case AFail
    then show ?thesis
      using a1 a2 commutativeS_switchArgs commutative_fail_other by metis 
  next
    case (AInvcheck x10)
    then show ?thesis 
      by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute invContextH_simps split: if_splits, auto simp add: invContextH_def )
  qed
qed


lemma commutativeInTransaction:
  assumes a_is_in_transaction: "currentTransaction S sa \<triangleq> t"
    and b_is_a_different_session[simp]: "sa \<noteq> sb"
    and not_endAtomic: "a \<noteq> AEndAtomic"
    and not_invCheck: "\<not>is_AInvcheck a"
    and wf[simp]: "state_wellFormed S"
  shows "commutativeS S (sa, a) (sb, b)"
proof (cases a)
  case ALocal
  then show ?thesis 
    by (simp add: commutative_ALocal_other)
next
  case (ANewId x2)
  then show ?thesis
    by (simp add: commutative_newId_other) 
next
  case (ABeginAtomic x3)
  then show ?thesis  
    by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction,
        metis a_is_in_transaction b_is_a_different_session option.simps(3) unchangedInTransaction(3))
next
  case AEndAtomic
  then show ?thesis using not_endAtomic by simp
next
  case (ADbOp)
  then show ?thesis
    by (simp add: commutative_Dbop_other)  
next
  case (AInvoc)
  then show ?thesis 
    by (auto simp add: commutativeS_def steps_appendFront,
        metis a_is_in_transaction local.wf option.distinct(1) preconditionI precondition_invoc wellFormed_invoc_notStarted(1),
        metis a_is_in_transaction b_is_a_different_session local.wf option.distinct(1) preconditionI precondition_invoc unchangedInTransaction(5) wellFormed_invoc_notStarted(1))
next
  case (AReturn x8)
  then show ?thesis   
    by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction,
        metis a_is_in_transaction b_is_a_different_session option.distinct(1) unchangedInTransaction(3))

next
  case AFail
  then show ?thesis
    by (simp add: commutative_fail_other)  
next
  case (AInvcheck res)
  then show ?thesis
    using is_AInvcheck_def not_invCheck by auto   
qed



lemma move_transaction:
  assumes a_is_in_transaction: "currentTransaction S sa \<triangleq> t"
    and b_is_a_different_session[simp]: "sa \<noteq> sb"
    and not_endAtomic: "a \<noteq> AEndAtomic"
    and not_invCheck: "\<not>is_AInvcheck a"
    and wf[simp]: "state_wellFormed S"
  shows "(S ~~ [(sa,a),(sb,b)] \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,a)] \<leadsto>* T)"
proof (rule useCommutativeS)   
  show "commutativeS S (sa, a) (sb, b)"
    by (simp add: a_is_in_transaction commutativeInTransaction not_endAtomic not_invCheck)
qed

lemma move_transaction2:
  assumes a_is_in_transaction: "currentTransaction S (get_invoc a) \<triangleq> t"
    and b_is_a_different_session[simp]: "get_invoc a \<noteq> get_invoc b"
    and not_endAtomic: "get_action a \<noteq> AEndAtomic"
    and not_invCheck: "\<not>is_AInvcheck (get_action a)"
    and wf[simp]: "state_wellFormed S"
  shows "(S ~~ a#b#xs \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)"
proof -
  have "(S ~~ a#b#xs \<leadsto>* T) \<longleftrightarrow> (\<exists>S'. (S ~~ [a,b] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    by (auto simp add: steps_appendFront steps_empty)
  moreover have "... \<longleftrightarrow> (\<exists>S'. (S ~~ [b,a] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    by (metis a_is_in_transaction b_is_a_different_session local.wf move_transaction not_endAtomic prod.collapse not_invCheck)
  moreover have "... \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)" 
    by (auto simp add: steps_appendFront steps_empty)
  ultimately show ?thesis
    by blast 
qed   






lemma one_compaction_step:
  assumes splitTrace: "tr = (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "get_invoc x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endAtomic: "get_action x \<noteq> AEndAtomic"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
  using splitTrace txaInTx xOutside no_endAtomic  proof (induct txa arbitrary: tr x rest rule: rev_induct)
  case Nil

  have "(s_init ~~ tr \<leadsto>* C) 
      = (s_init ~~ (s, ABeginAtomic tx ntxns) # x # rest \<leadsto>* C)" 
    using Nil by simp
  moreover have "... = (\<exists>S'. (s_init ~~ [(s, ABeginAtomic tx ntxns), x] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    by (auto simp add: steps_appendFront steps_empty)
  moreover have "... = (\<exists>S'. (s_init ~~ [x, (s, ABeginAtomic tx ntxns)] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    using useCommutativeS[OF commutative_beginAtomic_other[OF \<open>get_invoc x \<noteq> s\<close>[symmetric] wf \<open>get_action x \<noteq> AEndAtomic\<close>]]
    by simp
  moreover have "... = ( s_init ~~ x # (s, ABeginAtomic tx ntxns) # [] @ rest \<leadsto>* C)"
    by (auto simp add: steps_appendFront steps_empty)

  ultimately show ?case by auto
next
  case (snoc a as)

  have "(s_init ~~ x # (s, ABeginAtomic tx ntxns) # (as @ [a]) @ rest \<leadsto>* C)
      = (s_init ~~ x # (s, ABeginAtomic tx ntxns) # as @ ([a] @ rest) \<leadsto>* C)"
    by simp
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ [x] @ ([a] @ rest) \<leadsto>* C)"
    using snoc.hyps by (metis append_Cons append_Nil butlast_snoc in_set_butlastD snoc.prems) 
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ x # a # rest \<leadsto>* C)"
    by simp
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S') \<and> (S' ~~  x # a # rest \<leadsto>* C))"
    by (auto simp add:  steps_append steps_appendFront)
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S') \<and> (S' ~~  a # x # rest \<leadsto>* C))" (is ?eq1)
  proof -
    have "(S' ~~ x # a # rest \<leadsto>* C)
          \<longleftrightarrow> (S' ~~ a # x # rest \<leadsto>* C)" 
      if "(s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S')"
      for S'
    proof (rule move_transaction2[symmetric])
      have [simp]: "get_invoc a = s" using snoc
        by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 
      show "currentTransaction S' (get_invoc a) \<triangleq> tx" 
        using currentTransaction_unchangedInternalSteps3
        by (metis \<open>get_invoc a = s\<close> butlast_snoc in_set_butlastD local.wf snoc.prems(2) that) 
      show "get_invoc a \<noteq> get_invoc x"
        using snoc
        by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing) 
      show "get_action a \<noteq> AEndAtomic"
        using snoc 
        by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing)  
      show "state_wellFormed S'"
        using wf that by (rule state_wellFormed_combine, 
            insert snoc.prems(2), fastforce)
      show " \<not> is_AInvcheck (get_action a)"
        by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1 snoc.prems(2))
    qed
    then show ?eq1 by blast
  qed
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ a # x # rest \<leadsto>* C)"  
    by (auto simp add: steps_append steps_appendFront)
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # (as @ [a]) @ x # rest \<leadsto>* C)"  
    by auto
  ultimately show ?case
    using snoc.prems(1) by blast 
qed    


lemma one_compaction_step2:
  assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "get_invoc x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "get_action x \<noteq> AEndAtomic"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
proof 
  assume "s_init ~~ tr \<leadsto>* C"
  with steps_append 
  obtain S_mid where "s_init ~~ trStart \<leadsto>* S_mid" and "S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C"
    using splitTrace by blast

  have "state_wellFormed S_mid"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> local.wf noFail splitTrace state_wellFormed_combine by fastforce


  from \<open>S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C\<close>
  have "S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    using \<open>state_wellFormed S_mid\<close> no_endatomic one_compaction_step txaInTx xOutside by blast

  then show "s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> steps_append2 by blast
next \<comment> \<open>Other direction is very similar:\<close>
  assume "s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
  with steps_append 
  obtain S_mid where "s_init ~~ trStart \<leadsto>* S_mid" and "S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    by blast

  have "state_wellFormed S_mid"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> local.wf noFail splitTrace state_wellFormed_combine by fastforce

  from \<open>S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C\<close>
  have "S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C"
    using \<open>state_wellFormed S_mid\<close> no_endatomic one_compaction_step txaInTx xOutside by blast

  then show "s_init ~~ tr \<leadsto>* C"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> splitTrace steps_append2 by blast
qed


lemma one_compaction_step3:
  assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and splitTrace': "tr' = trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest"
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "get_invoc x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "get_action x \<noteq> AEndAtomic"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr' \<leadsto>* C)"
  using local.wf one_compaction_step2 splitTrace splitTrace' txaInTx xOutside no_endatomic noFail by blast 




definition canSwap :: "'ls itself \<Rightarrow> ('proc::valueType, 'operation, 'any::valueType)  action \<Rightarrow> ('proc, 'operation, 'any) action \<Rightarrow> bool" where
  "canSwap t a b \<equiv> (\<forall>(C1::('proc, 'ls, 'operation, 'any) state) C2 s1 s2. 
      s1\<noteq>s2 \<and> (C1 ~~ [(s1,a),(s2,b)] \<leadsto>* C2) \<and> state_wellFormed C1 \<longrightarrow> (C1 ~~ [(s2,b),(s1,a)] \<leadsto>* C2))"

lemma show_canSwap:
  assumes "\<And>(C1::('proc::valueType, 'ls, 'operation, 'any::valueType) state) C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
  shows "canSwap (t::'ls itself) a b"
proof (auto simp add: canSwap_def)
  fix C1 C3 :: "('proc, 'ls, 'operation, 'any) state"
  fix s1 s2
  assume a0: "s1 \<noteq> s2"
    and a1: "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C3"
    and a2: "state_wellFormed C1"

  from a1 obtain C2
    where a1': "C1 ~~ (s1,a) \<leadsto> C2" and a1'': "C2 ~~ (s2,b) \<leadsto> C3"
    using steps_appendFront steps_single by blast


  show "C1 ~~ [(s2, b), (s1, a)] \<leadsto>* C3"
  proof (subst steps.simps, clarsimp simp add: steps_empty steps_single, rule assms)
    show "s1 \<noteq> s2" using a0.
    show "C1 ~~ (s1, a) \<leadsto> C2" using a1'.
    show "C2 ~~ (s2,b) \<leadsto> C3" using a1''.
    show "state_wellFormed C1" using a2.
  qed
qed
       
lemma show_canSwap':
  assumes "x = a" 
    and"\<And>(C1::('proc::valueType, 'ls, 'operation, 'any::valueType) state) C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
  shows "canSwap (t::'ls itself) x b"
  by (simp add: assms show_canSwap)

method prove_canSwap = (
    rule show_canSwap, 
    auto simp add: step_simps state_updates_normalize fun_upd_twist intro!: show_state_calls_eq elim!: chooseSnapshot_unchanged_precise)

method prove_canSwap' = (
    rule show_canSwap', 
    auto simp add: step_simps state_updates_normalize fun_upd_twist intro!: show_state_calls_eq elim!: chooseSnapshot_unchanged_precise)
method prove_canSwap'' = (
    rule show_canSwap', 
    auto del: ext  simp add: wellFormed_callOrigin_dom2 step_simps wellFormed_currentTransactionUncommitted state_updates_normalize fun_upd_twist intro!: show_state_calls_eq ext split: if_splits elim!: chooseSnapshot_unchanged_precise)

lemma commutativeS_canSwap:
  assumes comm: "\<And>(C::('proc::valueType, 'ls, 'operation, 'any::valueType) state) s1 s2. \<lbrakk>s1\<noteq>s2;  state_wellFormed C\<rbrakk> \<Longrightarrow> commutativeS C (s1,a) (s2,b)"
  shows "canSwap (t::'ls itself) a b"
proof (auto simp add: canSwap_def)
  fix C1 C2 :: "('proc, 'ls, 'operation, 'any) state"
  fix s1 s2
  assume a0: "s1 \<noteq> s2"
    and a1: "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2"
and a2: "state_wellFormed C1"

  show "C1 ~~ [(s2, b), (s1, a)] \<leadsto>* C2"
  proof (subst useCommutativeS)
    show "commutativeS C1 (s2, b) (s1, a)" 
      using comm a0  a2 by (simp add: commutativeS_switchArgs)
    show "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2" using a1.
  qed
qed

lemma commutativeS_canSwap_sym:
  assumes comm: "\<And>(C::('proc::valueType, 'ls, 'operation, 'any::valueType) state) s1 s2. \<lbrakk>s1\<noteq>s2;  state_wellFormed C\<rbrakk> \<Longrightarrow> commutativeS C (s1,b) (s2,a)"
  shows "canSwap (t::'ls itself) a b"
  by (metis comm commutativeS_canSwap commutativeS_switchArgs)





text \<open>We can swap one action over a list of actions with canSwap\<close>
lemma swapMany:
  assumes steps: "(C1::('proc::valueType, 'ls, 'operation, 'any::valueType) state) ~~ tr @ [(s,a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> get_invoc x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (get_action x) a"
    and wf: "state_wellFormed C1"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "C1 ~~ [(s,a)] @ tr \<leadsto>* C2"
  using steps tr_different_session tr_canSwap noFail
proof (induct tr arbitrary: C2 rule: rev_induct)
  case Nil
  then show ?case
    by simp 
next
  case (snoc a' tr')
  then have IH: "\<And>C2. \<lbrakk>C1 ~~ tr' @ [(s, a)] \<leadsto>* C2; \<And>x. x \<in> set tr' \<Longrightarrow> get_invoc x \<noteq> s; \<And>x. x \<in> set tr' \<Longrightarrow> canSwap t (get_action x) a\<rbrakk> \<Longrightarrow> C1 ~~ [(s, a)] @ tr' \<leadsto>* C2" 
    and steps: "C1 ~~ (tr' @ [a']) @ [(s, a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> get_invoc x \<noteq> s"
    and tr_canSwap: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> canSwap t (get_action x) a"
    and noFail2a: "\<And>i. (i, AFail) \<notin> set (tr' @ [a'])"
    by auto

  from steps
  obtain C'
    where steps1: "C1 ~~ tr' \<leadsto>* C'" 
      and steps2: "C' ~~ [a', (s, a)] \<leadsto>* C2"
    by (auto simp add: steps_append)

  have wf': "state_wellFormed C'"
    using local.wf state_wellFormed_combine steps1 noFail2a by auto 

  from steps2
  have steps2': "C' ~~ [(s, a), a'] \<leadsto>* C2"
    using tr_canSwap by (metis canSwap_def list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1 tr_different_session wf') 

  from steps1 steps2'
  have "C1 ~~ tr' @  [(s, a), a'] \<leadsto>* C2"
    using steps_append2 by blast

  from this 
  obtain C''
    where steps1': "C1 ~~ tr' @  [(s, a)] \<leadsto>* C''" and steps2'': "C'' ~~ [a'] \<leadsto>* C2"
    by (metis (no_types, hide_lams) append.assoc append_Cons append_Nil steps_append)

  from steps1' IH
  have steps1'': "C1 ~~ [(s, a)] @ tr' \<leadsto>* C''"
    by (simp add: snoc.prems(2) snoc.prems(3))


  with steps2''  
  show ?case
    using steps_append2 by fastforce 
qed


lemma swapMany_middle:
  fixes C1 :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state"
  assumes steps: "C1 ~~ tr_start @ tr @ [(s,a)] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> get_invoc x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (get_action x) a"
    and wf: "state_wellFormed C1"
    and nofail1: "\<And>i. (i,AFail)\<notin> set tr_start"
    and nofail2: "\<And>i. (i,AFail)\<notin> set tr"
  shows "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
proof -
  from steps
  obtain C1' C2'
    where "C1 ~~ tr_start \<leadsto>* C1'" and "C1' ~~ tr @ [(s,a)] \<leadsto>* C2'" and "C2' ~~ tr_end \<leadsto>* C2"
    by (meson steps_append)

  then have "C1' ~~ [(s,a)] @ tr  \<leadsto>* C2'"
    using local.wf state_wellFormed_combine swapMany tr_canSwap tr_different_session nofail1 nofail2  by blast 

  then show "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
    using \<open>C1 ~~ tr_start \<leadsto>* C1'\<close> \<open>C2' ~~ tr_end \<leadsto>* C2\<close>
    using steps_append by blast  
qed    

lemma swapMany_middle':
  fixes C1 :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state"
  assumes steps: "C1 ~~ tr_start @ tr @ [a] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> get_invoc x \<noteq> (get_invoc a)"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (get_action x) (get_action a)"
    and wf: "state_wellFormed C1"
    and nofail1: "\<And>i. (i,AFail)\<notin> set tr_start"
    and nofail2: "\<And>i. (i,AFail)\<notin> set tr"
  shows "C1 ~~ tr_start @ [a] @ tr @ tr_end \<leadsto>* C2"
  by (insert assms, cases a, rule ssubst, assumption, rule swapMany_middle, auto)




lemma canSwap_cases:
  assumes no_begin_atomic: "\<And>txId txns. b \<noteq> ABeginAtomic txId txns"
    and no_invoc: "\<And>p. b \<noteq> AInvoc p"
    and no_invcheck_a: "\<not>is_AInvcheck a"
    and no_invcheck_b: "\<not>is_AInvcheck b"  
    and no_fail_a: "a \<noteq> AFail"
    and no_fail_b: "b \<noteq> AFail"    
  shows "canSwap t a b"
proof (cases b)
  case ALocal
  then show ?thesis
    by (simp add: commutativeS_canSwap commutative_other_ALocal)
next
  case (ANewId bid)
  then have [simp]: "b = ANewId bid" .

  show ?thesis
    by (simp add: commutativeS_canSwap_sym commutative_newId_other)
next
  case (ABeginAtomic x31 x32)
  then show ?thesis
    using no_begin_atomic by blast
next
  case AEndAtomic
  then have [simp]: "b = AEndAtomic" .
  then show ?thesis 
  proof (cases a; prove_canSwap?)
    case ALocal
    then show ?thesis
      by (simp add: commutativeS_canSwap commutative_ALocal_other)
  next
    case (ANewId x2)
    then show ?thesis
      by (simp add: commutativeS_canSwap commutative_newId_other) 
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis 
      by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis 
      by prove_canSwap''
  next
    case (ADbOp )
    then show ?thesis
      by (simp add: commutativeS_canSwap commutative_Dbop_other)
  next
    case (AInvoc )
    then show ?thesis
      by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis by prove_canSwap''
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case (ADbOp c op r)
  then have [simp]: "b = ADbOp c op r" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis  by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp )
    then show ?thesis
      by (meson canSwap_def commutative_Dbop_other useCommutativeS)  
  next
    case (AInvoc )
    then show ?thesis by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis
      using no_fail_a by blast 
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by blast 
  qed
next
  case (AInvoc )
  then show ?thesis
    using no_invoc by auto
next
  case (AReturn res)
  then have [simp]: "b = AReturn res" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp)
    then show ?thesis by prove_canSwap''
  next
    case (AInvoc)
    then show ?thesis by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis by prove_canSwap''
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case AFail
  then show ?thesis
    using no_fail_b by blast 
next
  case (AInvcheck r)
  then show ?thesis
    using is_AInvcheck_def no_invcheck_b by auto 
qed




end

