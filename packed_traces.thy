theory packed_traces
imports commutativity
begin



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
qed

lemma move_transaction2:
  assumes a_is_in_transaction: "currentTransaction S (fst a) \<triangleq> t"
    and b_is_a_different_session[simp]: "fst a \<noteq> fst b"
    and not_endAtomic: "snd a \<noteq> AEndAtomic"
    and not_invCheck: "\<not>is_AInvcheck (snd a)"
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
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endAtomic: "snd x \<noteq> AEndAtomic"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
  using splitTrace txaInTx xOutside no_endAtomic  proof (induct txa arbitrary: tr x rest rule: rev_induct)
  case Nil

  have "(s_init ~~ tr \<leadsto>* C) 
      = (s_init ~~ (s, ABeginAtomic tx ntxns) # x # rest \<leadsto>* C)" 
    using Nil by simp
  moreover have "... = (\<exists>S'. (s_init ~~ [(s, ABeginAtomic tx ntxns), x] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    by (auto simp add: steps_appendFront steps_empty)
  moreover have "... = (\<exists>S'. (s_init ~~ [x, (s, ABeginAtomic tx ntxns)] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    using useCommutativeS[OF commutative_beginAtomic_other[OF \<open>fst x \<noteq> s\<close>[symmetric] wf \<open>snd x \<noteq> AEndAtomic\<close>]]
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
      have [simp]: "fst a = s" using snoc
        by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 
      show "currentTransaction S' (fst a) \<triangleq> tx" 
        using currentTransaction_unchangedInternalSteps3
        by (metis \<open>fst a = s\<close> butlast_snoc in_set_butlastD local.wf snoc.prems(2) that) 
      show "fst a \<noteq> fst x"
        using snoc
        by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing) 
      show "snd a \<noteq> AEndAtomic"
        using snoc 
        by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing)  
      show "state_wellFormed S'"
        using wf that by (rule state_wellFormed_combine, 
            insert snoc.prems(2), fastforce)
      show " \<not> is_AInvcheck (snd a)"
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
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "snd x \<noteq> AEndAtomic"
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
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "snd x \<noteq> AEndAtomic"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr' \<leadsto>* C)"
  using local.wf one_compaction_step2 splitTrace splitTrace' txaInTx xOutside no_endatomic noFail by blast 

definition indexInOtherTransaction :: "('proc, 'operation, 'any) trace \<Rightarrow> txid \<Rightarrow> nat \<Rightarrow> bool" where
  "indexInOtherTransaction tr tx k \<equiv> 
  \<exists>i s ntxns. 
      k<length tr 
    \<and> i<k 
    \<and> tr!i = (s, ABeginAtomic tx ntxns)  
    \<and> fst (tr!k) \<noteq> s
    \<and> \<not>(\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

definition transactionIsPacked :: "('proc, 'operation, 'any) trace \<Rightarrow> txid \<Rightarrow> bool" where
  "transactionIsPacked tr tx \<equiv> 
  \<forall>k. \<not>indexInOtherTransaction tr tx k"  




\<comment> \<open>this is an alternative definition, which might be easier to work with in some cases\<close>
definition transactionIsPackedAlt :: "('proc, 'operation, 'any) trace \<Rightarrow> txid \<Rightarrow> bool" where
  "transactionIsPackedAlt tr tx \<equiv> 
  if \<exists>i s ntxns. i < length tr \<and> tr!i = (s, ABeginAtomic tx ntxns) then
    \<exists>i s end ntxns. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx ntxns)
        \<and> end > i  
        \<and> (end < length tr \<and> tr!end = (s, AEndAtomic) \<or> end = length tr)  
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> fst (tr!j) = s) 
  else
    True
  "  

lemma transactionIsPackedAlt_case_tx_exists:
  assumes "(s, ABeginAtomic tx ntxns) \<in> set tr"
  shows "transactionIsPackedAlt tr tx \<equiv> 
    \<exists>i s end ntxns. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx ntxns)
        \<and> end > i  
        \<and> (end < length tr \<and> tr!end = (s, AEndAtomic) \<or> end = length tr)  
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> fst (tr!j) = s) 
  "  
  by (subst transactionIsPackedAlt_def,
  subst if_P,
  insert assms,
  meson in_set_conv_nth, simp)


lemma transactionIsPackedAlt_eq:
  assumes uniqueTxs: "\<And>i j s s' tnxns tnxns'. \<lbrakk>i<length tr; j<length tr; tr!i = (s, ABeginAtomic tx tnxns); tr!j = (s', ABeginAtomic tx tnxns')\<rbrakk> \<Longrightarrow> i = j"
  shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
proof (auto simp add: transactionIsPackedAlt_def )
  fix i s ntxns ia sa ntxns'
  assume a0: "i < length tr"
    and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
    and a2: "ia < length tr"
    and a3: "tr ! ia = (sa, ABeginAtomic tx ntxns')"
    and a4: "\<forall>j. ia \<le> j \<and> j < length tr \<longrightarrow> fst (tr ! j) = sa"

  have [simp]: "ia = i"
    using a2 a0 a3 a1 by (rule uniqueTxs)



  then have [simp]: "sa = s"
    using a1 a3 by auto  
  then have a4': "\<And>j. i \<le> j \<Longrightarrow> j < length tr \<Longrightarrow> fst (tr ! j) = s"  
    using a4 by auto

  show "transactionIsPacked tr tx"
    by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s',
     smt \<open>ia = i\<close> \<open>sa = s\<close> a2 a3 a4' le_eq_less_or_eq le_less_trans prod.inject uniqueTxs)
next
  fix i s ntxns
  assume a0: "i < length tr"
    and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
    and a2: "transactionIsPacked tr tx"

  from a2
  have a2': "fst (tr ! k) = s \<or> (\<exists>j<k. i < j \<and> tr ! j = (s, AEndAtomic))" 
    if "k<length tr" "i<k"
    for k
    using a1 that by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)

  show "\<exists>i<length tr. \<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"  
  proof (rule_tac x=i in exI, (auto simp add: a0))
    show "\<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"
    proof (rule_tac x=s in exI, safe)
      show "\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)"
        by (simp add: a1) 
      define endPos where "endPos = (if \<exists>j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) then LEAST j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) else length tr)"
      show "\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s) "
      proof (rule_tac x="endPos" in exI, (auto simp add: endPos_def))
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) < length tr"
          by (smt less_trans neqE not_less_Least)
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> tr ! (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) = (s, AEndAtomic)"
          by (smt LeastI)
        show "\<And>j ja. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); i \<le> ja; ja < (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic))\<rbrakk> \<Longrightarrow> fst (tr ! ja) = s"
          by (smt a1 a2' dual_order.strict_trans fst_conv neqE not_le not_less_Least)
        show "\<And>j. \<lbrakk>\<forall>j<length tr. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic); i \<le> j; j < length tr\<rbrakk> \<Longrightarrow> fst (tr ! j) = s"
          by (metis a1 a2' dual_order.strict_trans fst_conv le_eq_less_or_eq)
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic)\<rbrakk> \<Longrightarrow> i < (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic))"
          by (metis (mono_tags, lifting) LeastI_ex)
        show "\<forall>j<length tr. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic) \<Longrightarrow> i < length tr"
          using a0 by blast  
      qed
    qed
  qed  
next
  show "\<forall>i<length tr. \<forall>s ntxns. tr ! i \<noteq> (s, ABeginAtomic tx ntxns) \<Longrightarrow> transactionIsPacked tr tx"
    by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
next
  fix i s ntxns ia sa ntxns' ende
  assume a0: "i < length tr"
    and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
    and a3: "tr ! ia = (sa, ABeginAtomic tx ntxns')"
    and a7: "ia < ende"
    and a4: "\<forall>j. ia \<le> j \<and> j < ende \<longrightarrow> fst (tr ! j) = sa"
    and a5: "ende < length tr"
    and a6: "tr ! ende = (sa, AEndAtomic)"

  have a2: "ia < length tr"
    using a5 a7 less_trans by blast


  with uniqueTxs have [simp]: "ia = i"
    using a0 a1 a3 by blast

  then have [simp]: "sa = s"
    using a1 a3 by auto     

  have a4': "fst (tr ! j) = s" if "i \<le> j" and "j < ende" for j
    by (auto simp add: that a4)  


  show "transactionIsPacked tr tx"
  proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s' ntxns)
    fix k i' s' ntxns
    assume b0: "k < length tr"
      and b1: "i' < k"
      and b2: "tr ! i' = (s', ABeginAtomic tx ntxns)"
      and b3: "\<forall>j>i'. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
      and b4: "fst (tr ! k) \<noteq> s'"

    have " i' < length tr"
      using b0 b1 order.strict_trans by blast 


    then have [simp]: "i' = i"
      using uniqueTxs b2 a1 a0 by blast 

    then have [simp]: "s' = s"
      using a1 b2 by auto

    have b3': "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic)"
      using b3 by simp      
    have "fst (tr ! k) = s"
    proof (cases "k < ende")
      case True
      show ?thesis
      proof (rule a4')
        show "i \<le> k"
          using \<open>i' = i\<close> b1 dual_order.strict_implies_order by blast 
        show "k < ende" using True .
      qed
    next case False
      then have "k \<ge> ende" by simp
      show ?thesis
      proof (cases "k = ende")
        case True
        then show ?thesis
          by (simp add: a6) 
      next
        case False
        then have "k > ende"
          by (simp add: \<open>ende \<le> k\<close> dual_order.strict_iff_order) 
        from b3' have "ende>i \<and> ende < k \<longrightarrow> tr ! ende \<noteq> (s, AEndAtomic)"
          by blast
        with \<open>k > ende\<close> have "tr ! ende \<noteq> (s, AEndAtomic)"
          using \<open>ia = i\<close> a7 by blast

        then show ?thesis
          by (simp add: a6) 
      qed
    qed 
    with b4 show False  by simp
  qed
qed

lemma transactionIsPackedAlt_eq2:
  assumes steps: "initialState p ~~ tr \<leadsto>* S"
  shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
  by (auto simp add: transactionIdsUnique[OF steps] transactionIsPackedAlt_eq)






lemma transactionIsPacked_show:
  assumes steps: "initialState p ~~ tr \<leadsto>* S"
    and beginAtomic1: "beginAtomic < endAtomic"
    and beginAtomic2: "tr!beginAtomic = (s, ABeginAtomic tx ntxns)"
    and endAtomic1: "endAtomic < length tr"    
    and endAtomic2: "tr!endAtomic = (s, AEndAtomic)"
    and a1: "\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> fst (tr ! i) = s"
  shows "transactionIsPacked tr tx"
proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
  fix k i s' ntxns
  assume b0: "k < length tr"
    and b1: "i < k"
    and b2: "tr ! i = (s', ABeginAtomic tx ntxns)"
    and b3: "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
    and b4: "fst (tr ! k) \<noteq> s'"

  from b2
  have "i = beginAtomic"
    using b0 b1 beginAtomic1 beginAtomic2 endAtomic1 transactionIdsUnique[OF steps] by auto
  then have "s' = s"
    using b2 beginAtomic2 by auto

  from b3
  have "k \<le> endAtomic"
    using \<open>i = beginAtomic\<close> \<open>s' = s\<close> beginAtomic1 endAtomic2 leI by blast

  with b4 show False
    using \<open>i = beginAtomic\<close> \<open>k \<le> endAtomic\<close> a1 b1 b2 by auto
qed    



\<comment> \<open>the set of transactions occurring in the trace\<close>    
definition traceTransactions :: "('proc, 'operation, 'any) trace \<Rightarrow> txid set" where
  "traceTransactions tr \<equiv> {tx | s tx txns. (s, ABeginAtomic tx txns) \<in> set tr}"

text \<open>between begin and end of a transaction there are no actions from other sessions\<close>
definition transactionsArePacked :: "('proc, 'operation, 'any) trace \<Rightarrow> bool" where
  "transactionsArePacked tr \<equiv>
  \<forall>i k s t txns. 
      i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t txns)  
    \<and> fst (tr!k) \<noteq> s
    \<longrightarrow>  (\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

text \<open>
For termination proofs, we want to measure how far a trace is from being packed.
For this we take the sum over all actions in the trace and count in how many transactions
it appears.
\<close>


\<comment> \<open>checks if sessions s is in a transaction at position i in trace tr\<close>
definition inTransaction :: "('proc, 'operation, 'any) trace \<Rightarrow> nat \<Rightarrow> invocId \<Rightarrow> bool"  where 
  "inTransaction tr i s \<equiv>
  \<exists>j. j\<le>i \<and> i<length tr \<and> (\<exists>t txns. tr!j = (s, ABeginAtomic t txns))
     \<and> (\<forall>k. j<k \<and> k < length tr \<and> k\<le>i \<longrightarrow> tr!k \<noteq> (s, AEndAtomic))
"

\<comment> \<open>returns the set of all transactions, which are in a transaction at point i in the trace\<close>
definition sessionsInTransaction :: "('proc, 'operation, 'any) trace \<Rightarrow> nat \<Rightarrow> invocId set"  where 
  "sessionsInTransaction tr i \<equiv> {s. inTransaction tr i s}"






lemma sessionsInTransaction_h1: " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1 txns), (s\<^sub>1, AEndAtomic)] 3 = {}" 
  by (auto simp add: sessionsInTransaction_def  inTransaction_def nth_Cons' split: if_splits)


lemma sessionsInTransaction_h2: " sessionsInTransaction [(s1, ABeginAtomic t\<^sub>1 txns)] 0= {s1}" 
  by (auto simp add: sessionsInTransaction_def inTransaction_def nth_Cons' split: if_splits)

lemma sessionsInTransaction_h3: " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1 txns), (s\<^sub>1, AEndAtomic)] 1 = {}" 
  by (auto simp add: sessionsInTransaction_def inTransaction_def nth_Cons' split: if_splits )



lemma sessionsInTransaction_append:
  "i<length xs \<Longrightarrow> sessionsInTransaction (xs@ys) i = sessionsInTransaction xs i"
  by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def)



lemma not_packed_example:
  assumes notPacked: "\<not>transactionsArePacked tr"
  shows "\<exists>i k s t ts a s'. 
      tr ! k = (s', a)
    \<and> i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t ts)  
    \<and> s' \<noteq> s
    \<and>  (\<forall>j. i < j \<and> j < k \<longrightarrow> tr!j \<noteq> (s, AEndAtomic))"
  using assms by (auto simp add: transactionsArePacked_def, metis prod.collapse)





lemma show_traceCorrect_same:
  assumes sameTraceContent: "set tr = set tr'"
  shows "traceCorrect tr' = traceCorrect tr"
  using assms by (auto simp add: traceCorrect_def)


definition allowed_context_switch where 
  "allowed_context_switch action \<equiv> 
            (\<exists>txId txns. action = ABeginAtomic txId txns) 
          \<or> (\<exists>p. action = AInvoc p)"


lemma allowed_context_switch_simps:
  shows "\<not>allowed_context_switch ALocal" 
    and "\<not>allowed_context_switch (ANewId uid)"
    and "allowed_context_switch (ABeginAtomic t ats)"
    and "\<not>allowed_context_switch AEndAtomic" 
    and "\<not>allowed_context_switch (ADbOp c x ar)" 
    and "allowed_context_switch (AInvoc p)"
    and "\<not>allowed_context_switch (AReturn ir)" 
    and "\<not>allowed_context_switch AFail" 
    and "\<not>allowed_context_switch (AInvcheck invr)" by (auto simp add: allowed_context_switch_def)


definition packed_trace :: "('proc, 'operation, 'any) trace \<Rightarrow> bool" where
  "packed_trace tr \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> fst (tr!(i-1)) \<noteq> fst (tr!i)
    \<longrightarrow> (allowed_context_switch (snd (tr!i)))" 


lemmas use_packed_trace = iffD1[OF packed_trace_def[THEN meta_eq_to_obj_eq], rule_format]



lemma prefixes_are_packed:
  assumes "packed_trace tr'" 
    and "isPrefix tr tr'"
  shows "packed_trace tr"
  using \<open>packed_trace tr'\<close> by (auto simp add: packed_trace_def,
      metis (no_types, lifting) Suc_leI assms(2) diff_less_Suc isPrefix_len isPrefix_same less_le_trans)



lemma context_switches_in_packed: 
  assumes packed: "packed_trace tr"
    and split_tr: "tr = tr1@[(s,a),(s',a')]@tr2"
    and differentSession: "s \<noteq> s'"
  shows "allowed_context_switch a'"
proof -
  have "a' = snd(tr!(1+length tr1))"
    using split_tr by (auto simp add: nth_append)

  moreover
  have "allowed_context_switch (snd(tr!(1+length tr1)))"
    using packed proof (rule use_packed_trace)
    show "0 < 1 + length tr1" by simp
    show "1 + length tr1 < length tr" using split_tr by auto
    show "fst (tr ! (1 + length tr1 - 1)) \<noteq> fst (tr ! (1 + length tr1))" using split_tr \<open>s \<noteq> s'\<close> by (auto simp add: nth_append)
  qed
  ultimately
  show ?thesis by simp
qed  



definition canSwap :: "'ls itself \<Rightarrow> ('proc::valueType, 'operation, 'any::valueType)  action \<Rightarrow> ('proc, 'operation, 'any) action \<Rightarrow> bool" where
  "canSwap t a b \<equiv> (\<forall>(C1::('proc, 'ls, 'operation, 'any) state) C2 s1 s2. s1\<noteq>s2 \<and> (C1 ~~ [(s1,a),(s2,b)] \<leadsto>* C2) \<and> state_wellFormed C1 \<longrightarrow> (C1 ~~ [(s2,b),(s1,a)] \<leadsto>* C2))"

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
  assumes comm: "\<And>(C::('proc::valueType, 'ls, 'operation, 'any::valueType) state) s1 s2. s1\<noteq>s2 \<Longrightarrow> commutativeS C (s1,a) (s2,b)"
  shows "canSwap (t::'ls itself) a b"
proof (auto simp add: canSwap_def)
  fix C1 C2 :: "('proc, 'ls, 'operation, 'any) state"
  fix s1 s2
  assume a0: "s1 \<noteq> s2"
    and a1: "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2"

  show "C1 ~~ [(s2, b), (s1, a)] \<leadsto>* C2"
  proof (subst useCommutativeS)
    show "commutativeS C1 (s2, b) (s1, a)" 
      using comm a0 by (simp add: commutativeS_switchArgs) 
    show "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2" using a1.
  qed
qed


lemma canSwap_when_allowed:
  assumes no_ctxt_switch: "\<not>allowed_context_switch b"
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
  proof (cases a)
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by blast 
  qed (simp, prove_canSwap+)
next
  case (ABeginAtomic x31 x32)
  then show ?thesis
    using allowed_context_switch_def no_ctxt_switch by auto 
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
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp )
    then show ?thesis by prove_canSwap''
  next
    case (AInvoc )
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
  case (ADbOp c op r)
  then have [simp]: "b = ADbOp c op r" .
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
    using allowed_context_switch_def[where action = b] no_ctxt_switch by auto 

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


text \<open>We can swap one action over a list of actions with canSwap\<close>
lemma swapMany:
  assumes steps: "(C1::('proc::valueType, 'ls, 'operation, 'any::valueType) state) ~~ tr @ [(s,a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) a"
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
  then have IH: "\<And>C2. \<lbrakk>C1 ~~ tr' @ [(s, a)] \<leadsto>* C2; \<And>x. x \<in> set tr' \<Longrightarrow> fst x \<noteq> s; \<And>x. x \<in> set tr' \<Longrightarrow> canSwap t (snd x) a\<rbrakk> \<Longrightarrow> C1 ~~ [(s, a)] @ tr' \<leadsto>* C2" 
    and steps: "C1 ~~ (tr' @ [a']) @ [(s, a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> canSwap t (snd x) a"
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
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) a"
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
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> (fst a)"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) (snd a)"
    and wf: "state_wellFormed C1"
    and nofail1: "\<And>i. (i,AFail)\<notin> set tr_start"
    and nofail2: "\<And>i. (i,AFail)\<notin> set tr"
  shows "C1 ~~ tr_start @ [a] @ tr @ tr_end \<leadsto>* C2"
  by (insert assms, cases a, rule ssubst, assumption, rule swapMany_middle, auto)


definition packed_trace_s :: "('proc, 'operation, 'any) trace \<Rightarrow> invocId \<Rightarrow> bool" where
  "packed_trace_s tr s \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> fst (tr!i) = s
    \<longrightarrow> fst (tr!(i-1)) \<noteq> s
    \<longrightarrow> (allowed_context_switch (snd (tr!i)))" 





lemma pack_trace_for_one_session:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr \<Longrightarrow> \<not>is_AInvcheck a "
  shows "\<exists>tr'. packed_trace_s tr' s
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s)
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
  text \<open>By induction over the minimal index that is not packed.\<close>
    \<comment> \<open>I could not figure out how to write this down as an induction over the minimum, so I reversed it and made it an induction over the maximum inversed index.\<close>
  using steps noFail noInvcheck        
proof (induct "max_natset {length tr - i  | i.
        0<i 
      \<and> i<length tr 
      \<and> fst (tr!(i-1)) \<noteq> s
      \<and> fst (tr!i) = s
      \<and> \<not>(allowed_context_switch (snd(tr!i)))}"
    arbitrary: tr C
    rule: less_induct)
  case less
  then have IH: "\<And>tra C. \<lbrakk>max_natset {length tra - i |i. 0 < i \<and> i < length tra \<and> fst (tra ! (i - 1)) \<noteq> s \<and> fst (tra ! i) = s \<and> \<not> allowed_context_switch (snd (tra ! i))}
                      < max_natset {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))};
                      initialState program ~~ tra \<leadsto>* C; \<And>s. (s, AFail) \<notin> set tra; \<And>s a. (s, a) \<in> set tra \<Longrightarrow> \<not> is_AInvcheck a\<rbrakk>
                     \<Longrightarrow> \<exists>tr'. packed_trace_s tr' s \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tra s \<longrightarrow> packed_trace_s tr' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a) \<in> set tr \<Longrightarrow> \<not> is_AInvcheck a"
    by auto

  show ?case 
  proof (cases "max_natset {length tr - i  | i. 0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))}")
    case 0
    then have "{i. 0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))} = {}"
      by (simp add: max_natset_empty)
    then have already_packed: "packed_trace_s tr s"
      by (auto simp add: packed_trace_s_def)

    show ?thesis 
      by (rule exI[where x=tr], auto simp add: less already_packed)

  next
    case (Suc n)

    text \<open>There is one problematic position\<close>
    from Suc
    obtain i_example
      where i_example: "0 < i_example \<and> i_example < length tr \<and> fst (tr ! (i_example - 1)) \<noteq> s \<and> fst (tr ! i_example) = s \<and> \<not> allowed_context_switch (snd (tr ! i_example))"
      using max_natset_Collect_Suc(1) by fastforce

    text \<open>Let i be the smallest problematic position\<close>
    obtain i
      where i_def: "0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))"
        and i_min: "\<And>j. 0<j \<and> j<length tr \<and> fst (tr!(j-1)) \<noteq> s \<and> fst (tr!j) = s \<and> \<not>(allowed_context_switch (snd(tr!j))) \<Longrightarrow> j\<ge>i"
      using i_example by (atomize_elim, rule ex_has_least_nat)
    then have i1[simp]: "0<i"
      and i2[simp]: "i<length tr"
      and i3: "fst (tr!(i-1)) \<noteq> s"
      and i4: "fst (tr!i) = s"
      and i5: "\<not>(allowed_context_switch (snd(tr!i)))"
      by auto

    text \<open>There must be a previous action on the same invocId (at least the invocId should be there, since i is no invocId).\<close>
    obtain prev
      where prev1: "fst(tr!prev) = s"
        and prev2: "prev < i"
        and prev3: "\<And>j. \<lbrakk>prev < j; j < i\<rbrakk> \<Longrightarrow> fst(tr!j) \<noteq> s"
    proof (atomize_elim)
      from \<open>initialState program ~~ tr \<leadsto>* C\<close> \<open>i<length tr\<close> \<open>fst (tr!i) = s\<close>
      have "\<exists>j<i. fst (tr ! j) = s \<and> (\<exists>p. snd (tr ! j) = AInvoc p)"
      proof (rule exists_invoc)
        show "\<And>p. snd (tr ! i) \<noteq> AInvoc p"
          using allowed_context_switch_def[where action="snd (tr ! i)"] i5 by auto 
        show "\<not> is_AInvcheck (snd (tr ! i))"
          by (metis i2 less.prems(3) nth_mem snd_conv surj_pair)
      qed
      then have "\<exists>j<i. fst (tr ! j) = s"
        by auto
      then have "\<exists>j. (j<i \<and> fst (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> fst (tr ! j') = s \<longrightarrow> j'\<le>j)"
      proof (rule exists_greatest')
        show "\<exists>bound. \<forall>j. j < i \<and> fst (tr ! j) = s \<longrightarrow> j \<le> bound"
          using less_or_eq_imp_le by blast
      qed
      from this obtain j where "(j<i \<and> fst (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> fst (tr ! j') = s \<longrightarrow> j'\<le>j)"
        by blast
      then have "fst (tr ! j) = s \<and> j < i \<and> (\<forall>j'>j. j' < i \<longrightarrow> fst (tr ! j') \<noteq> s)"
        by auto

      then show "\<exists>prev. fst (tr ! prev) = s \<and> prev < i \<and> (\<forall>j>prev. j < i \<longrightarrow> fst (tr ! j) \<noteq> s)"  ..
    qed

    have [simp]: "prev < length tr"
      using i2 order.strict_trans prev2 by blast
    have [simp]: "min (length tr) prev = prev"
      using i2 prev2 by linarith  
    have [simp]: "min (length tr) i = i"
      using i2  by linarith    

    text \<open>Then we can split the trace, so that we have (one action from s) -- (many other actions) -- (action i form s)\<close>
    have tr_split: "tr = take prev tr @ [tr!prev] @ drop (Suc prev) (take i tr) @ [tr!i] @ drop (Suc i) tr"
    proof (rule nth_equalityI)
      show "length tr = length (take prev tr @ [tr ! prev] @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr)"
        using i2 prev2 by (auto, linarith)
      show "tr ! ia = (take prev tr @ [tr ! prev] @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr) ! ia" if "ia<length tr"for ia
        using that by (auto simp add: nth_append nth_Cons'  Suc_leI less_diff_conv prev2)
    qed    


    text \<open>Because of the swap lemma we can change this to (one action from s) -- (action i form s) -- (many other actions)\<close>
    define tr' where "tr' = take prev tr @ [tr!prev, tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr"

    have tr'sameLength: "length tr' = length tr"
      using i2 prev2  by (auto simp add: tr'_def, linarith)


    have tr'_sameSet: "set tr' = set tr" 
      by (subst tr_split, subst  tr'_def, auto)


    have tr'1: "tr'!x = tr!x" if "x \<le> prev" for x
      using that by (auto simp add: tr'_def nth_append)
    moreover have tr'2: "tr'!x = tr!i" if "x=Suc prev" for x
      using that by (auto simp add: tr'_def nth_append)
    moreover have tr'3: "tr'!x = tr!(x-1)" if "x>Suc prev"  and "x<i" for x
      using that by (auto simp add: tr'_def nth_append nth_Cons',
       metis Suc_diff_Suc diff_Suc_less dual_order.strict_trans less_2_cases not_less_eq numeral_2_eq_2)
    moreover have tr'4: "tr'!x = tr!(x-1)" if  "x = i" for x
      using that prev2 antisym i_def prev1 by (auto simp add: tr'_def nth_append nth_Cons' Suc_diff_Suc numeral_2_eq_2, fastforce)
    moreover have tr'5: "tr'!x = tr!x" if "x > i" and "x < length tr" for x
      using that prev2 by (auto simp add: tr'_def nth_append nth_Cons')
    ultimately have tr'i_def: "tr'!x = (if x\<le>prev then tr!x else if x=Suc prev then tr!i else if x\<le>i then tr!(x-1) else tr!x)" if "x<length tr" for x
      by (metis antisym_conv2 not_le not_less_eq_eq that)  


    have "initialState program ~~ (take prev tr @ [tr!prev]) @ [tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr \<leadsto>* C"
    proof (rule swapMany_middle')
      show "initialState program ~~ (take prev tr @ [tr ! prev]) @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr \<leadsto>* C"
        using tr_split less.prems(1) by auto

      show "\<And>x. x \<in> set (drop (Suc prev) (take i tr)) \<Longrightarrow> fst x \<noteq> fst (tr ! i)"
        using prev3 by (auto simp add: in_set_conv_nth,
            metis add.commute add_Suc_right fst_conv i4 less_add_Suc1 less_diff_conv) 

      from i5
      show "canSwap t (snd x) (snd (tr ! i))" if "x \<in> set (drop (Suc prev) (take i tr))" for x t
      proof (rule canSwap_when_allowed)
        from that obtain k 
          where k1: "x = tr!k" 
            and k2: "k<i" 
            and k3: "k>prev"
          by (auto simp add: in_set_conv_nth)

        then have k4: "x\<in>set tr"
          using dual_order.strict_trans i2 nth_mem by blast


        show "\<not> is_AInvcheck (snd x)"
          by (metis k4 less.prems(3) prod.collapse)
        show "\<not> is_AInvcheck (snd (tr ! i))"
          by (metis i2 less.prems(3) nth_mem snd_conv surj_pair)
        show "snd x \<noteq> AFail"
          by (metis k4 less.prems(2) prod.collapse)
        show "snd (tr ! i) \<noteq> AFail"
          by (metis i2 less.prems(2) nth_mem old.prod.exhaust snd_conv)
      qed  

      show "state_wellFormed (initialState program)"
        by (simp add: state_wellFormed_init)

      from noFail
      show "\<And>i. (i, AFail) \<notin> set (take prev tr @ [tr ! prev])"
        by (metis \<open>prev < length tr\<close> hd_drop_conv_nth in_set_takeD take_hd_drop)
      from noFail
      show "\<And>ia. (ia, AFail) \<notin> set (drop (Suc prev) (take i tr))"
        by (meson in_set_dropD in_set_takeD)
    qed    


    then have "initialState program ~~ tr' \<leadsto>* C"
      by (simp add: tr'_def)

    have tr'packed: "packed_trace_s tr' s" if "packed_trace_s tr s" for s
      using that Suc_leI prev2 
      by (auto simp add: packed_trace_s_def tr'i_def tr'sameLength i4 prev1,
         metis One_nat_def Suc_diff_eq_diff_pred  i4 nat_less_le not_less_eq_eq zero_less_Suc zero_less_diff,
         metis One_nat_def Suc_eq_plus1 diff_Suc_1 i_def le_SucE le_diff_conv zero_less_Suc)



    text \<open>Now the problem at i is fixed, so we can use IH to fix the rest of the trace.\<close>
    have "\<exists>tr''. packed_trace_s tr'' s \<and> (initialState program ~~ tr'' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tr' s \<longrightarrow> packed_trace_s tr'' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr'') \<and> (\<forall>s a. (s, a) \<in> set tr'' \<longrightarrow> \<not> is_AInvcheck a)"
    proof (rule IH)
      show "initialState program ~~ tr' \<leadsto>* C"
        by (simp add: \<open>initialState program ~~ tr' \<leadsto>* C\<close>)
      show "\<And>s. (s, AFail) \<notin> set tr'"
        using noFail tr'_sameSet by blast 
      show "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
        using noInvcheck tr'_sameSet by blast



      show "max_natset {length tr' - i |i. 0 < i \<and> i < length tr' \<and> fst (tr' ! (i - 1)) \<noteq> s \<and> fst (tr' ! i) = s \<and> \<not> allowed_context_switch (snd (tr' ! i))}
          < max_natset {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))}"
      proof (rule show_max_natset_smaller_Collect, intro exI)
        show "length tr - i = length tr - i \<and> 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))"
          using One_nat_def i3 i4 i5 by auto
        show "finite {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))}" by force
        show "\<exists>i. j = length tr' - i \<and> 0 < i \<and> i < length tr' \<and> fst (tr' ! (i - 1)) \<noteq> s \<and> fst (tr' ! i) = s \<and> \<not> allowed_context_switch (snd (tr' ! i)) \<Longrightarrow> j < length tr - i" for j
        proof (auto simp add: tr'sameLength intro!: diff_less_mono2)
          fix i'
          assume a0: "j = length tr - i'"
            and a1: "0 < i'"
            and a2: "i' < length tr"
            and a3: "fst (tr' ! (i' - Suc 0)) \<noteq> fst (tr' ! i')"
            and a4: "\<not> allowed_context_switch (snd (tr' ! i'))"
            and a5: "s = fst (tr' ! i')"

          show "i < i'"
            using a2 a3 a4
            by (auto simp add: tr'i_def split: if_splits,
                metis One_nat_def a1 a5 dual_order.strict_iff_order i_min leD prev2 tr'1,
                insert \<open>0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))\<close> prev1,
                blast,
                insert a3 a5 i_def tr'2, (auto)[1],
                metis One_nat_def a5 antisym diff_le_self i3 le_less_linear prev3 tr'i_def)
        qed
      qed
    qed

    from this obtain tr'' 
      where tr''1: "packed_trace_s tr'' s" 
        and tr''2: "initialState program ~~ tr'' \<leadsto>* C" 
        and tr''3: "\<forall>s. packed_trace_s tr' s \<longrightarrow> packed_trace_s tr'' s"
        and tr''4: "(\<forall>s. (s, AFail) \<notin> set tr'')"
        and tr''5: "(\<forall>s a. (s, a) \<in> set tr'' \<longrightarrow> \<not> is_AInvcheck a)" 
      by blast

    from tr''3
    have tr''packed: "\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr'' s"
      using tr'packed by blast


    show ?thesis
      using tr''1 tr''2 tr''4 tr''5 tr''packed by blast 


  qed
qed

lemma packed_trace_iff_all_sessions_packed:
  "packed_trace tr \<longleftrightarrow> (\<forall>s. packed_trace_s tr s)"
  by (auto simp add: packed_trace_def packed_trace_s_def)

text \<open>Now we can just repeat fixing invocId by invocId, until all sessions are packed.\<close>
lemma pack_trace:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr \<Longrightarrow> \<not>is_AInvcheck a "
  shows "\<exists>tr'. packed_trace tr'
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
proof -
  have "{s. \<not>packed_trace_s tr s } \<subseteq> set (map fst tr)"
    by (auto simp add: packed_trace_s_def)

  then have "finite {s. \<not>packed_trace_s tr s }"
    using infinite_super by blast

  from this and assms
  show ?thesis
  proof (induct "{s. \<not>packed_trace_s tr s }" arbitrary: tr rule: finite_psubset_induct)
    case psubset

    show ?case 
    proof (cases "{s. \<not>packed_trace_s tr s } = {}")
      case True
      then have "packed_trace tr"
        by (auto simp add: packed_trace_iff_all_sessions_packed)
      then show ?thesis
        using psubset.prems by blast 
    next
      case False
      from this obtain s where "\<not> packed_trace_s tr s"
        by blast


      from \<open>initialState program ~~ tr \<leadsto>* C\<close> \<open>\<And>s. (s, AFail) \<notin> set tr\<close> \<open>\<And>s a. (s, a) \<in> set tr \<Longrightarrow> \<not> is_AInvcheck a\<close>
      have "\<exists>tr'. packed_trace_s tr' s \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"  
        by (rule pack_trace_for_one_session; force)

      from this
      obtain tr' 
        where tr'1: "packed_trace_s tr' s"
          and tr'2: "initialState program ~~ tr' \<leadsto>* C"
          and tr'3: "\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s"
          and tr'4: "\<And>s. (s, AFail) \<notin> set tr'"
          and tr'5: "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
        by blast

      from tr'1 tr'3 \<open>\<not> packed_trace_s tr s\<close>
      have subset: "{s. \<not>packed_trace_s tr' s } \<subset> {s. \<not>packed_trace_s tr s }"
        by auto

      from subset tr'2 tr'4 tr'5
      show ?thesis 
        by (rule psubset; force)
    qed
  qed
qed




lemma pack_incorrect_trace:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and notCorrect: "\<not>traceCorrect tr"
  shows "\<exists>tr' C'. packed_trace tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* C')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> \<not>traceCorrect tr'"
proof -
  text \<open>As the trace is not correct, there must be a failing invariant:\<close> 

  from notCorrect
  obtain failPos1 
    where failPos1_props: "failPos1 < length tr \<and> (\<exists>s. tr ! failPos1 = (s, AInvcheck False))"
    by (meson in_set_conv_nth traceCorrect_def)

  text \<open>Now take the minimal failing position.\<close>  
  then have "\<exists>failPos1. (failPos1 < length tr \<and> (\<exists>s. tr ! failPos1 = (s, AInvcheck False)))
           \<and> (\<forall>i. (i < length tr \<and> (\<exists>s. tr ! i = (s, AInvcheck False))) \<longrightarrow> i \<ge> failPos1)"
    by (rule ex_has_least_nat)
  from this
  obtain failPos failPos_s 
    where failPos_len: "failPos < length tr" 
      and failPos_fail: "tr ! failPos = (failPos_s, AInvcheck False)"
      and failPos_min: "\<And> i. \<lbrakk>i < length tr; \<exists>s txns. tr ! i = (s, AInvcheck False)\<rbrakk> \<Longrightarrow> i\<ge>failPos"
    by auto



  text \<open>Only the part leading to the invariant violation is relevant ...\<close>  

  define tr' where "tr' = take failPos tr"

  from steps
  obtain C' where tr'_steps: "initialState program ~~ tr' \<leadsto>* C'"
    by (metis append_take_drop_id steps_append tr'_def)

  from steps
  have "initialState program ~~ (tr'@[tr!failPos]@drop (Suc failPos) tr) \<leadsto>* C"
    by (metis \<open>failPos < length tr\<close> append.assoc append_take_drop_id take_Suc_conv_app_nth tr'_def)
  then have "\<exists>C''. C' ~~ tr ! failPos  \<leadsto>  C''"
    using  tr'_steps by (auto simp add: steps_append2 steps_appendFront)

  then have C'_fails: "\<And>s. C' ~~ (s, AInvcheck False) \<leadsto> C'"  
    by (auto simp add: failPos_fail step_simps)


  text \<open>Now remove all other invariant checks\<close>
  define tr'' where "tr'' = filter (\<lambda>(s,a). \<not>is_AInvcheck a) tr'"

  from tr'_steps
  have tr''_steps:  "initialState program ~~ tr'' \<leadsto>* C'"
    by (auto simp add: tr''_def,
     induct rule: steps_induct,
     auto simp add: is_AInvcheck_def step_simps steps_step steps_empty)


  from tr''_steps
  have "\<exists>tr'''. packed_trace tr''' \<and> (initialState program ~~ tr''' \<leadsto>* C') \<and> (\<forall>s. (s, AFail) \<notin> set tr''') \<and> (\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a)"
  proof (rule pack_trace)
    show "\<And>s. (s, AFail) \<notin> set tr''"
      using noFail by (auto simp add: tr'_def tr''_def dest: in_set_takeD)
    show "\<And>s a. (s, a) \<in> set tr'' \<Longrightarrow> \<not> is_AInvcheck a"
      by (auto simp add: tr''_def)
  qed    

  from this
  obtain tr'''
    where tr'''1: "packed_trace tr'''"
      and tr'''2: "initialState program ~~ tr''' \<leadsto>* C'"
      and tr'''3: "\<forall>s. (s, AFail) \<notin> set tr'''"
      and tr'''4: "\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a"
    by blast

  define tr4 where "tr4 = tr''' @ [(fst (last tr'''), AInvcheck False)]"

  from \<open>packed_trace tr'''\<close>
  have "packed_trace tr4"
    by (auto simp add: packed_trace_def tr4_def nth_append,
     metis One_nat_def gr_implies_not_zero last_conv_nth length_0_conv less_SucE)


  moreover have "initialState program ~~ tr4 \<leadsto>* C'"
    using C'_fails steps_append2 steps_single tr'''2 tr4_def by blast
  moreover have "\<forall>s. (s, AFail) \<notin> set tr4"
    by (simp add: tr4_def tr'''3)
  moreover have "\<not> traceCorrect tr4"
    by (auto simp add: traceCorrect_def tr4_def)

  ultimately show ?thesis by blast
qed    





end