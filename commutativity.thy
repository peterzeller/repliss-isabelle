section \<open>Commutativity in Executions\<close>
theory commutativity
  imports repliss_sem prefix
    "HOL-Eisbach.Eisbach"
    execution_invariants
    invContext_simps
begin


text \<open>This theory proves commutativity between certain actions in executions.\<close>


definition canSwap :: "'ls itself \<Rightarrow> ('proc::valueType, 'operation, 'any::valueType)  action \<Rightarrow> ('proc, 'operation, 'any) action \<Rightarrow> bool" where
  "canSwap t a b \<equiv> (\<forall>(C1::('proc, 'ls, 'operation, 'any) state) C2 i1 i2. 
      i1\<noteq>i2 \<and> (C1 ~~ [(i1,a),(i2,b)] \<leadsto>* C2) \<and> state_wellFormed C1 \<longrightarrow> (C1 ~~ [(i2,b),(i1,a)] \<leadsto>* C2))"


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

method prove_canSwap'' uses simp  = (
    rule show_canSwap', 
    auto del: ext  simp add: simp step_simps fun_upd_twist intro!: show_state_calls_eq ext split: if_splits elim!: chooseSnapshot_unchanged_precise)




text "The following are all the relevant cases where canSwap is true:"
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
  hence [simp]: " b = ALocal" .

  show ?thesis
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis  by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis  by prove_canSwap''
  next
    case (ADbOp x51 x52 x53)
    then show ?thesis  by prove_canSwap''
  next
    case (AInvoc x6)
    then show ?thesis  by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis  by prove_canSwap''
  next
    case AFail
    then show ?thesis  by prove_canSwap''
  next
    case (AInvcheck x9)
    then show ?thesis  by prove_canSwap''
  qed
next
  case (ANewId bid)
  then have [simp]: "b = ANewId bid" .

  show ?thesis
  proof (cases a)
    case ALocal
    then show ?thesis  by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis  by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis  by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis  by prove_canSwap''
  next
    case (ADbOp x51 x52 x53)
    then show ?thesis  by prove_canSwap''
  next
    case (AInvoc x6)
    then show ?thesis  by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis  by prove_canSwap''
  next
    case AFail
    then show ?thesis  by prove_canSwap''
  next
    case (AInvcheck x9)
    then show ?thesis  by prove_canSwap''
  qed

next
  case (ABeginAtomic x31 x32)
  then show ?thesis
    using no_begin_atomic by blast
next
  case AEndAtomic
  then have [simp]: "b = AEndAtomic" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis  by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis  by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis 
      by (prove_canSwap'' simp:   wellFormed_currentTransactionUncommitted  )
  next
    case AEndAtomic
    then show ?thesis 
      by prove_canSwap''
  next
    case (ADbOp )
    then show ?thesis 
      by prove_canSwap''
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
    then show ?thesis by (prove_canSwap'' simp: wellFormed_callOrigin_dom2  wellFormed_currentTransactionUncommitted  )
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp )
    then show ?thesis
      by (prove_canSwap'' simp:  getContextH_callsUpdate getContextH_visUpdate wellFormed_visibleCallsSubsetCalls2)  
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

