theory approach
  imports Main commutativity
    repliss_sem_single_invocation
    consistency
begin

section \<open>Proof approach\<close>

text \<open>This theory includes the soundness proof of our proof approach.\<close>

(*
TODO:

1. single invocId semantics

2. show that multi-invocId trace with fixed invocId can be reduced to multiple single invocId traces by chopping

3. other things

*)


declare length_dropWhile_le[simp]  


lemma state_wellFormed_ls_visibleCalls:     
  assumes "state_wellFormed S"
  shows "localState S s = None \<longleftrightarrow> visibleCalls S s = None"
  using assms apply (induct rule: wellFormed_induct)
   apply (simp add: initialState_def)
  apply (erule step.cases)
          apply (auto split: if_splits)
  done

lemma state_wellFormed_ls_to_visibleCalls:     
  assumes "state_wellFormed S"
    and "currentTransaction S s \<triangleq> tx"
  shows "localState S s \<noteq> None"
  using assms apply (induct rule: wellFormed_induct)
   apply (simp add: initialState_def)
  apply (erule step.cases)
          apply (auto split: if_splits)
  done  

lemma state_wellFormed_tx_to_visibleCalls:     
  assumes wf: "state_wellFormed S"
    and "currentTransaction S s \<triangleq> tx"
  shows "visibleCalls S s \<noteq> None"
  using assms state_wellFormed_ls_to_visibleCalls[OF wf] state_wellFormed_ls_visibleCalls[OF wf] by auto

lemma state_wellFormed_invocation_before_result:
  assumes "state_wellFormed C"
    and "invocationOp C s = None"
  shows "invocationRes C s = None"    
  using assms apply (induct arbitrary:  rule: wellFormed_induct)
  by (auto simp add: initialState_def step_simps_all wellFormed_invoc_notStarted(2) split: if_splits)


lemma state_wellFormed_no_result_when_running:     
  assumes "state_wellFormed C"
    and "localState C s \<triangleq> ls" 
  shows "invocationRes C s = None"   
  using assms apply (induct arbitrary: ls rule: wellFormed_induct)
  by (auto simp add: initialState_def step_simps_all state_wellFormed_invocation_before_result split: if_splits)



text \<open>Coupling invariant: S is state from distributed execution and S is state from single-invocId execution.\<close>
definition state_coupling :: "('ls,'any::valueType) state \<Rightarrow> ('ls,'any) state \<Rightarrow> invocId \<Rightarrow> bool \<Rightarrow> bool" where
  "state_coupling S S' i sameSession \<equiv> 
   if sameSession then
      \<comment> \<open>  did a step in the same invocId  \<close>
      S' = S
\<comment> \<open>
      if currentTransaction S i = None 
      then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S i orElse {} \<and> S' = S\<lparr>visibleCalls := (visibleCalls S)(i := vis') \<rparr> \<comment> \<open>  TODO maybe can get equality here \<close>
      else S' = S \<close>
   else 
      \<comment> \<open>  did step in a different invocId  \<close>
        state_monotonicGrowth i S' S
      \<comment> \<open>  local state on s unchanged  \<close>
      \<and> localState S i = localState S' i
      \<and> currentProc S i = currentProc S' i
      \<and> currentTransaction S i = currentTransaction S' i
      \<and> visibleCalls S i = visibleCalls S' i
      \<and> (\<forall>t. transactionOrigin S' t \<triangleq> i \<longleftrightarrow> transactionOrigin S t \<triangleq> i)
      "


(*

record operationContext = 
  calls :: "callId \<rightharpoonup> call"
  happensBefore :: "callId rel"

record distributed_state = operationContext +
  prog :: prog
  callOrigin :: "callId \<rightharpoonup> txid"
  generatedIds :: "'any set"
  knownIds :: "'any set"
  invocationOp :: "invocId \<rightharpoonup> (procedureName \<times> 'any list)"
  invocationRes :: "invocId \<rightharpoonup> 'any"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

record state = distributed_state + 
  localState :: "invocId \<rightharpoonup> localState"
  currentProc :: "invocId \<rightharpoonup> procedureImpl"
  visibleCalls :: "invocId \<rightharpoonup> callId set"
  currentTransaction :: "invocId \<rightharpoonup> txid"
*)


lemma state_coupling_same_inv:
  assumes "state_coupling S S' s True"
  shows "invariant_all S' \<longleftrightarrow> invariant_all S"
proof -
  have [simp]: "prog S' = prog S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "callOrigin S' = callOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "transactionOrigin S' = transactionOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "transactionStatus S' = transactionStatus S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "happensBefore S' = happensBefore S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "calls S' = calls S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "knownIds S' = knownIds S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationOp S' = invocationOp S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationRes S' = invocationRes S" using assms by (auto simp add: state_coupling_def split: if_splits)

  ultimately 
  show "invariant_all S' \<longleftrightarrow> invariant_all S"
    by  (auto simp add:  consistentSnapshotH_def)
qed    


(*
When all transactions are committed in S 
and we execute some packed trace tr and get to state S'
where tx is uncommitted in S'
then the last executed transaction must be tx
TODO something missing ?????
*)
lemma only_one_commmitted_transaction_h:
  assumes  steps: "S ~~ tr \<leadsto>* S'"
    and wf: "state_wellFormed S"
    and packed: "packed_trace tr"
    and status: "transactionStatus S' tx \<triangleq> Uncommitted"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    \<comment> \<open>and tr_len: "length tr > 0"\<close>
    \<comment> \<open>and allEnd: "allTransactionsEnd tr"\<close>
    and noSwitch: "noContextSwitchesInTransaction tr"
    and initial: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "(currentTransaction S' (fst (last tr)) \<triangleq> tx) 
      \<and> (\<exists>i txns. i<length tr \<and> tr!i = (fst (last tr), ABeginAtomic tx txns)
           \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (fst (last tr), AEndAtomic)))" 
  using steps packed status noFails noSwitch proof (induct arbitrary: tx  rule: steps_induct)
  case initial
  with \<open>transactionStatus S tx \<noteq> Some Uncommitted\<close> show ?case by blast
next
  case (step S' tr a S'' tx)

  from \<open>noContextSwitchesInTransaction (tr @ [a])\<close>
  have noContextSwitch: "noContextSwitchesInTransaction tr"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast

  { 
    assume "transactionStatus S' tx \<triangleq> Uncommitted"
    with \<open> S ~~ tr \<leadsto>* S'\<close>
    have IH: "currentTransaction S' (fst (last tr)) \<triangleq> tx 
          \<and> (\<exists>i txns. i<length tr \<and> tr!i = (fst (last tr), ABeginAtomic tx txns)
                   \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (fst (last tr), AEndAtomic)))"
      using isPrefix_appendI prefixes_are_packed step.IH \<open>\<And>s. (s, AFail) \<notin> set (tr @ [a])\<close> \<open>packed_trace (tr @ [a])\<close> noContextSwitch
      by (metis butlast_snoc in_set_butlastD) 



    obtain i' action where a_split[simp]: "a = (i',action)"
      by fastforce

    from IH
    have IH1: "currentTransaction S' (fst (last tr)) \<triangleq> tx"
      by blast


    from IH
    obtain i txns
      where i1: "i<length tr"
        and i2: "tr!i = (fst (last tr), ABeginAtomic tx txns)"
        and i3: "\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (fst (last tr), AEndAtomic)"
      by fastforce

    then have "(tr @ [a]) ! i = (fst (last tr), ABeginAtomic tx txns)"
      by (simp add: nth_append_first)

    have "a \<noteq> (fst (last tr), AEndAtomic)" 
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open>transactionStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps IH1 split: if_splits )


    from \<open>noContextSwitchesInTransaction (tr @ [a])\<close> \<open>(tr @ [a]) ! i = (fst (last tr), ABeginAtomic tx txns)\<close>
    have "\<not>allowed_context_switch (snd ((tr@[a])!length tr))" 
    proof (rule use_noContextSwitchesInTransaction)
      show "\<forall>j. i < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last tr), AEndAtomic)"
        using \<open>a \<noteq> (fst (last tr), AEndAtomic)\<close> i3 less_Suc_eq nth_append_first by fastforce
      show "i < length tr"
        by (simp add: i1)
      show "Suc (length tr) \<le> length (tr @ [a])"
        by simp
      show "i < Suc (length tr)"
        by (simp add: i1 less_SucI)
      show "length tr < Suc (length tr)"
        by simp
    qed
    then have "\<not>allowed_context_switch action"
      by simp 

    then have i'_simps: "i' = fst (last tr)"
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"]
      apply (auto simp add: nth_append)
      by (metis i1 One_nat_def gr_implies_not_zero last_conv_nth length_0_conv)




    from \<open>S' ~~ a \<leadsto> S''\<close> IH1
    have "currentTransaction S'' (fst (last (tr@[a]))) \<triangleq> tx"
      using \<open>a \<noteq> (fst (last tr), AEndAtomic)\<close>  \<open>\<And>s. (s, AFail) \<notin> set (tr @ [a])\<close> by (auto simp add: step.simps  i'_simps)

    moreover have "(\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (fst (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last (tr @ [a])), AEndAtomic)))"
      apply (rule_tac x=i in exI)
      apply (rule_tac x=txns in exI)
      apply (auto simp add: )
      using i1 less_SucI apply blast
      using \<open>(tr @ [a]) ! i = (fst (last tr), ABeginAtomic tx txns)\<close> a_split i'_simps apply blast
      by (metis \<open>a \<noteq> (fst (last tr), AEndAtomic)\<close> a_split i'_simps i3 less_SucE nth_append_first nth_append_length)

    ultimately have "currentTransaction S'' (fst (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (fst (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last (tr @ [a])), AEndAtomic)))"
      by simp
  }
  moreover
  {
    assume "transactionStatus S' tx \<noteq> Some Uncommitted"
    then have  "currentTransaction S'' (fst (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (fst (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last (tr @ [a])), AEndAtomic)))"
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open> transactionStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps split: if_splits)
  }
  ultimately show "currentTransaction S'' (fst (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (fst (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last (tr @ [a])), AEndAtomic)))"
    by auto
qed


lemma currentTransaction_exists_beginAtomic:
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and inTx: "currentTransaction S' i \<triangleq> tx"
    and noTx: "currentTransaction S i = None"
    and wf: "state_wellFormed S"
    and noFails: "\<And>i. (i, AFail) \<notin> set tr"
  shows "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
  using steps inTx noFails proof (induct arbitrary: tx rule: steps_induct)
  case initial
  then show ?case
    by (simp add: noTx)

next
  case (step S' tr a S'')

  from step 
  have IH: "\<lbrakk>currentTransaction S' i \<triangleq> tx\<rbrakk> \<Longrightarrow> \<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))" for tx
    by auto


  from \<open> S' ~~ a \<leadsto> S''\<close>
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ls')
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  local)
      show "\<And>i. (i, AFail) \<notin> set tr"
        using step.prems(2) by auto

    qed

    then show ?thesis
      using \<open>a = (s, ALocal)\<close> by (auto simp add: nth_append)

  next
    case (newId s ls f ls' uid)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  newId)
      show "\<And>i. (i, AFail) \<notin> set tr"
        using step.prems(2) by auto
    qed

    then show ?thesis
      using \<open>a = (s, ANewId uid)\<close> by (auto simp add: nth_append)
  next
    case (beginAtomic s ls f ls' t vis snapshot)
    show ?thesis 
    proof (cases "t=tx")
      case True
      then have "s = i"
        using local.beginAtomic(1) local.beginAtomic(7) local.wf state_wellFormed_combine step.prems step.step step.steps unchangedInTransaction(3)
        by (metis Un_insert_right append_Nil2 insert_iff list.simps(15) not_None_eq set_append wellFormed_currentTransaction_unique_h(2))

      show ?thesis 
        apply (rule_tac x="length tr" in exI)
        using beginAtomic by (auto simp add: nth_append True \<open>s = i\<close>)
    next
      case False

      have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
      proof (rule step)
        show "currentTransaction S' i \<triangleq> tx"
          using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: False  beginAtomic split: if_splits)
        show " \<And>i. (i, AFail) \<notin> set tr"
          using step.prems(2) by auto

      qed

      then show ?thesis
        using \<open>a = (s, ABeginAtomic t snapshot)\<close> by (auto simp add: nth_append split: if_splits)
    qed
  next
    case (endAtomic s ls f ls' t)

    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: endAtomic split: if_splits)
    qed

    then show ?thesis 
      apply auto
      apply (rule_tac x=ib in exI)
      using endAtomic \<open>currentTransaction S'' i \<triangleq> tx\<close> by (auto simp add: nth_append)
  next
    case (dbop s ls f Op args ls' t c res vis)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  dbop)
    qed

    then show ?thesis
      using \<open>a = (s, ADbOp c Op args res)\<close> by (auto simp add: nth_append)
  next
    case (invocId s procName args initialState impl)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  invocId)
    qed

    then show ?thesis
      using invocId by (auto simp add: nth_append)
  next
    case (return s ls f res)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  return)
    qed

    then show ?thesis
      using return by (auto simp add: nth_append)
  next
    case (fail s ls)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> 
        by (auto simp add:  fail split: if_splits)
    qed

    then show ?thesis
      using fail by (auto simp add: nth_append)
  next
    case (invCheck res s)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule IH)
      show "currentTransaction S' i \<triangleq> tx"
        using \<open>currentTransaction S'' i \<triangleq> tx\<close> by (simp add:  invCheck)
    qed

    then show ?thesis
      using invCheck by (auto simp add: nth_append)
  qed
qed


lemma at_most_one_active_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
  shows "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTransaction S' i = Some tx)
       \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  using steps  packed noFails noCtxtSwitchInTx proof (induct rule: steps_induct)
  case initial
  then show ?case 
    using wellFormed_currentTransaction_unique_h(2) noUncommitted S_wellformed open_transactions_empty by (auto simp add:  allowed_context_switch_simps)

next
  case (step S' tr a S'')

  have IH: "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTransaction S' i = Some tx)
            \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  proof (rule step)
    show "packed_trace tr"
      using packed_trace_prefix step.prems(1) by auto
    show "\<And>s. (s, AFail) \<notin> set tr"
      using step.prems(2) by auto
    show "noContextSwitchesInTransaction tr"
      using isPrefix_appendI prefixes_noContextSwitchesInTransaction step.prems(3) by blast
  qed

  from \<open>S' ~~ a \<leadsto> S''\<close>
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis 
      using IH by (auto simp add: open_transactions_append_one)
  next
    case (newId s ls f ls' uid)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (beginAtomic s ls f ls' t vis snapshot)

    have openTransactions_empty: "openTransactions tr = {}"
    proof (auto simp add: openTransactions_def)
      fix i' tx' j txns
      assume a0: "j < length tr"
        and a1: "\<forall>k<length tr. j < k \<longrightarrow> tr ! k \<noteq> (i', AEndAtomic)"
        and a2: "tr ! j = (i', ABeginAtomic tx' txns)"

      have "\<not> allowed_context_switch (snd ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>noContextSwitchesInTransaction (tr @ [a])\<close>])
        show "(tr @ [a]) ! j = (i', ABeginAtomic tx' txns)"
          by (simp add: a0 a2 nth_append_first)
        show "\<forall>ja. j < ja \<and> ja < Suc (length tr) \<longrightarrow> (tr @ [a]) ! ja \<noteq> (i', AEndAtomic)"
          by (simp add: a1 local.beginAtomic(1) nth_append)
        show "j < Suc (length tr)"
          by (simp add: a0 less_SucI)
        show " j < length tr"
          by (simp add: a0) 
        show "Suc (length tr) \<le> length (tr @ [a])" 
          by simp
        show "length tr < Suc (length tr)"
          by simp
      qed

      then show "False"
        by (simp add: \<open>a = (s, ABeginAtomic t snapshot)\<close>  allowed_context_switch_simps)
    qed

    from beginAtomic
    show ?thesis using IH 
      by (auto simp add: open_transactions_append_one openTransactions_empty )
  next
    case (endAtomic s ls f ls' t)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (dbop s ls f Op args ls' t c res vis)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (invocId s procName args initialState impl)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (return s ls f res)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (fail s ls)
    then show ?thesis
      using step.prems(2) by auto 
  next
    case (invCheck res s)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  qed
qed


lemma at_most_one_current_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    and packed: "packed_trace tr"
    and wf: "state_wellFormed S"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "\<forall>i. currentTransaction S' i \<noteq> None \<longrightarrow> i = fst (last tr)"
  using steps noCtxtSwitchInTx packed  noFails
proof (induct rule: steps_induct)
  case initial
  then have "currentTransaction S i = None" for i
    using noUncommitted
    by (meson local.wf option.exhaust wellFormed_currentTransactionUncommitted) 
  then show ?case
    by simp
next
  case (step S' tr a S'')
  have IH: "\<forall>i. currentTransaction S' i \<noteq> None \<longrightarrow> i = fst (last tr)"
  proof (rule step)
    show " noContextSwitchesInTransaction tr"
      using isPrefix_appendI prefixes_noContextSwitchesInTransaction step.prems(1) by blast
    show "packed_trace tr"
      using packed_trace_prefix step.prems(2) by blast
    show "\<And>s. (s, AFail) \<notin> set tr"
      using step.prems(3) by auto
  qed

  have noFail_tr: "(i, AFail) \<notin> set tr" for i
    using step.prems(3) by auto

  have noFail_a: "snd a \<noteq> AFail"
    using step.prems(3)
    by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 




  show ?case
  proof (cases tr)
    case Nil
    then have "currentTransaction S' i = None" for i
      using noUncommitted \<open>S ~~ tr \<leadsto>* S'\<close>
      apply (auto simp add: steps_empty)
      by (metis local.wf option.exhaust wellFormed_currentTransaction_unique_h(2))

    with \<open>S' ~~ a \<leadsto> S''\<close>
    show ?thesis 
      by (auto simp add: step.simps split: if_splits)

  next
    case (Cons x xs)
    then have tr_nonempty[simp]: "tr \<noteq> []" by simp

    have last_same: "fst (last tr) = fst a" if "\<not> allowed_context_switch (snd a)" 
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"] that
      by (auto simp add: nth_append last_conv_nth)

    have no_tx_if_context_switch: "currentTransaction S' i = None" if "allowed_context_switch (snd a)" for i
    proof (rule ccontr, clarsimp)
      fix tx
      assume tx: "currentTransaction S' i \<triangleq> tx"

      have "currentTransaction S i = None"
        by (meson local.wf noUncommitted option.exhaust wellFormed_currentTransaction_unique_h(2))


      from tx
      obtain ib txns
        where ib: "tr!ib = (i, ABeginAtomic tx txns)"
          and ib_len: "ib < length tr" 
          and ib_no_end: "\<forall>j. ib<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (i, AEndAtomic)"
        using \<open>currentTransaction S i = None\<close> \<open>S ~~ tr \<leadsto>* S'\<close> currentTransaction_exists_beginAtomic local.wf  noFail_tr by blast

      thm step.prems(3)

      have "\<not> allowed_context_switch (snd ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>noContextSwitchesInTransaction (tr @ [a])\<close>, where j="length tr"])
        show "(tr @ [a]) ! ib = (i, ABeginAtomic tx txns)"
          using ib by (simp add: ib_len nth_append) 
        show "\<forall>j. ib < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (i, AEndAtomic)"
          using that by (auto simp add: ib_no_end nth_append allowed_context_switch_simps)

        show "ib < Suc (length tr)"
          by (simp add: ib_len less_Suc_eq)
          apply_end (auto simp add: ib_len)
      qed
      then show False
        using that by simp
    qed


    from \<open>S' ~~ a \<leadsto> S''\<close>
    show ?thesis
    proof (cases rule: step.cases)
      case (local s ls f ls')
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (newId s ls f ls' uid)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (beginAtomic s ls f ls' t vis snapshot)
      then show ?thesis using IH no_tx_if_context_switch by (auto simp add: allowed_context_switch_simps)
    next
      case (endAtomic s ls f ls' t)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (dbop s ls f Op args ls' t c res vis)
      then show ?thesis using IH by auto
    next
      case (invocId s procName args initialState impl)
      then show ?thesis using IH no_tx_if_context_switch by (auto simp add: allowed_context_switch_simps)
    next
      case (return s ls f res)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    next
      case (fail s ls)
      then show ?thesis using IH
        using step.prems(3) by auto
    next
      case (invCheck res s)
      then show ?thesis using IH last_same by (auto simp add: allowed_context_switch_simps)
    qed
  qed
qed




lemma chooseSnapshot_transactionConsistent_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and a3: "transactionConsistent (callOrigin S) (transactionStatus S) vis"
  shows "transactionConsistent (callOrigin S) (transactionStatus S) snapshot"
  using a1 a3 apply (auto simp add: chooseSnapshot_def downwardsClosure_def transactionConsistent_def callsInTransactionH_contains)
  apply (auto simp add: split: option.splits)
  using all_committed apply blast
  apply (metis (no_types, lifting) hb_callOrigin option.distinct(1))
  by (metis (no_types, lifting) hb_tr option.inject)

lemma chooseSnapshot_consistentSnapshot_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and hb_trans: "trans (happensBefore S)"
    and callOrigin_ex: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> \<exists>ci. calls S c \<triangleq> ci"
    and a3: "consistentSnapshot S vis"
  shows "consistentSnapshot S snapshot"
proof (auto simp add: consistentSnapshotH_def)
  show "causallyConsistent (happensBefore S) snapshot"
    using a1 a3 chooseSnapshot_causallyConsistent_preserve consistentSnapshotH_def hb_trans by blast
  from a1
  show "transactionConsistent (callOrigin S) (transactionStatus S) snapshot"
  proof (rule chooseSnapshot_transactionConsistent_preserve)
    show " \<And>x y z tx. \<lbrakk>(x, z) \<in> happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y, z) \<in> happensBefore S"
      using hb_tr by blast
    show "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<triangleq> Committed"
      by (simp add: all_committed)
    show "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb, ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
      using hb_callOrigin by blast
    show "transactionConsistent (callOrigin S) (transactionStatus S) vis"
      using a3 consistentSnapshotH_def by blast
  qed
  show "\<And>x. x \<in> snapshot \<Longrightarrow> \<exists>y. calls S x \<triangleq> y"
    using a1 apply (auto simp add: chooseSnapshot_def)
    apply (meson a3 consistentSnapshotH_def in_dom)
    by (smt assms(6) callsInTransactionH_def downwardsClosure_in hb_callOrigin mem_Collect_eq)
qed




lemma show_transactionConsistent[case_names only_committed[in_vis origin_tx] all_from_same[in_vis origin_same]]:
assumes "\<And>c tx. \<lbrakk>c\<in>vis; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus tx \<triangleq> Committed"
    and "\<And>c1 c2. \<lbrakk>c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
shows "transactionConsistent origin txStatus vis"
using assms by (auto simp add: transactionConsistent_def)

lemma wellFormed_state_callOrigin_transactionStatus:
assumes wf: "state_wellFormed C"
    and "callOrigin C c \<triangleq> tx"
shows "transactionStatus C tx \<noteq> None"   
using assms apply (induct  rule: wellFormed_induct)
  by (auto simp add: initialState_def step_simps_all wellFormed_currentTransaction_unique_h split: if_splits)


lemma wellFormed_state_calls_from_current_transaction_in_vis:
assumes wf: "state_wellFormed C"
    and "callOrigin C c \<triangleq> tx"
    and "currentTransaction C s \<triangleq> tx"
    and "visibleCalls C s \<triangleq> vis"
shows "c\<in>vis"   
using assms apply (induct arbitrary: vis rule: wellFormed_induct)
apply (auto simp add: initialState_def step_simps_all wellFormed_state_callOrigin_transactionStatus split: if_splits)
using wellFormed_currentTransaction_unique_h(1) apply blast
by (simp add: inTransaction_localState)

lemma wellFormed_happensBefore_calls_r:
assumes wf: "state_wellFormed C"
    and "(x,c)\<in>happensBefore C"
shows "calls C c \<noteq> None"   
using wellFormed_visibleCallsSubsetCalls_h(1)[OF wf] assms by auto


lemma wellFormed_happensBefore_calls_l:
assumes wf: "state_wellFormed C"
    and "(c,x)\<in>happensBefore C"
shows "calls C c \<noteq> None"   
using wellFormed_visibleCallsSubsetCalls_h(1)[OF wf] assms by auto

lemma wellFormed_happensBefore_vis:
assumes wf: "state_wellFormed C"
    and "visibleCalls C s \<triangleq> vis"
    and "callOrigin C c1 \<noteq> Some t"
    and "c1 \<in> vis"
    and "currentTransaction C s \<triangleq> t"
    and "callOrigin C c2 \<triangleq> t"
shows "(c1,c2) \<in> happensBefore C"
using assms 
apply (induct arbitrary: c1 c2 vis t rule: wellFormed_induct)
by (auto simp add: initialState_def step_simps_all wellFormed_state_callOrigin_transactionStatus wellFormed_visibleCallsSubsetCalls2  wellFormed_currentTransaction_unique  split: if_splits)


lemma chooseSnapshot_committed2:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a5: "\<And>c c' tx tx'. \<lbrakk>(c', c) \<in> happensBefore S; callOrigin S c \<triangleq> tx; callOrigin S c' \<triangleq> tx'; transactionStatus S tx \<triangleq> Committed\<rbrakk> \<Longrightarrow> transactionStatus S tx' \<triangleq> Committed"
    and a2': "c \<notin> vis"
  shows "transactionStatus S tx \<triangleq> Committed"
  using a1 a2 a2' a3 apply (auto simp add: chooseSnapshot_def)
  apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
  using a5 by blast

lemma chooseSnapshot_transactionConsistent:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a4: "callOrigin S c' \<triangleq> tx"
    and a5: "\<And>c c'. \<lbrakk>c\<in>vis; callOrigin S c \<triangleq> tx; callOrigin S c' \<triangleq> tx\<rbrakk> \<Longrightarrow> c' \<in> vis "
    and a6: "\<And>c ca cb tx tx'. \<lbrakk>(ca,c)\<in>happensBefore S; callOrigin S c \<triangleq> tx; callOrigin S ca \<triangleq> tx'; callOrigin S cb \<triangleq> tx'; tx\<noteq>tx' \<rbrakk> \<Longrightarrow> (cb,c)\<in>happensBefore S"
  shows "c' \<in> snapshot"
  using a1 a2 a3 a4 apply (auto simp add: chooseSnapshot_def)
   apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
  using a5 apply blast
  using a6 by blast





lemma wellFormed_state_transaction_consistent:
assumes wf: "state_wellFormed S"
\<comment> \<open>contains only committed calls and calls from current transaction:\<close>
shows "\<And>s vis c tx. \<lbrakk>visibleCalls S s \<triangleq> vis; c\<in>vis; callOrigin S c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus S tx \<triangleq> Committed \<or> currentTransaction S s \<triangleq> tx"
\<comment> \<open>contains all calls from a transaction\<close>
  and "\<And>s vis c1 c2. \<lbrakk>visibleCalls S s \<triangleq> vis; c1\<in>vis; callOrigin S c1 = callOrigin S c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
\<comment> \<open>happens-before consistent with transactions\<close>
  and "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin S x1 \<noteq> callOrigin S y1; callOrigin S x1 = callOrigin S x2; callOrigin S y1 = callOrigin S y2 \<rbrakk> \<Longrightarrow>  (x1,y1) \<in> happensBefore S \<longleftrightarrow> (x2, y2) \<in> happensBefore S"
\<comment> \<open>happens-before only towards committed transactions or to the same transaction\<close>  
  and "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore S; callOrigin S y \<triangleq> tx; callOrigin S x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus S tx' \<triangleq> Committed \<or> tx' = tx"
using assms  proof (induct  rule: wellFormed_induct)
  case initial
  
  define init where [simp]: "init = (initialState (prog S))"
  
  show "\<And>s vis c tx. \<lbrakk>visibleCalls init s \<triangleq> vis; c\<in>vis; callOrigin init c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus init tx \<triangleq> Committed \<or> currentTransaction init s \<triangleq> tx"
    by (auto simp add: initialState_def )
  show "\<And>s vis c1 c2. \<lbrakk>visibleCalls init s \<triangleq> vis; c1\<in>vis; callOrigin init c1 = callOrigin init c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
    by (auto simp add: initialState_def )
  show "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin init x1 \<noteq> callOrigin init y1; callOrigin init x1 = callOrigin init x2;
                    callOrigin init y1 = callOrigin init y2\<rbrakk>
                   \<Longrightarrow> ((x1, y1) \<in> happensBefore init) = ((x2, y2) \<in> happensBefore init)"
    by (auto simp add: initialState_def )                   
  show "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore init; callOrigin init y \<triangleq> tx; callOrigin init x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus init tx' \<triangleq> Committed \<or> tx' = tx"
    by (auto simp add: initialState_def )
next
  case (step C a C')
  
  \<comment> \<open>contains only committed calls and calls from current transaction:\<close>
  from step 
  have IH1: "\<And>s vis c tx. \<lbrakk>visibleCalls C s \<triangleq> vis; c\<in>vis; callOrigin C c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus C tx \<triangleq> Committed \<or> currentTransaction C s \<triangleq> tx"
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
  have IH4: "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore C; callOrigin C y \<triangleq> tx; callOrigin C x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus C tx' \<triangleq> Committed \<or> tx' = tx"
    by auto
  
  have new_snapshot_cases: "(c \<in> callsInTransactionH orig txns \<down> hb) 
  \<longleftrightarrow> ((\<exists>c2 txn. (c,c2)\<in>hb \<and> orig c2 \<triangleq> txn \<and> txn\<in>txns) 
       \<or> (\<exists>txn. orig c \<triangleq> txn \<and> txn\<in>txns ))" 
    for c orig txns hb
    by (auto simp add: callsInTransactionH_def downwardsClosure_def)  
    
    
  show IH1': "transactionStatus C' tx \<triangleq> Committed \<or> currentTransaction C' s \<triangleq> tx"
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
      using g1 g2 g3 apply (auto simp add: beginAtomic)
      using \<open>transactionStatus C t = None\<close> \<open>state_wellFormed C\<close> wellFormed_state_callOrigin_transactionStatus apply auto[1]
      using IH1 \<open>currentTransaction C s' = None\<close> local.beginAtomic(8) apply fastforce
       defer
      using IH1 apply blast
    proof -
      assume a0: "snapshot = vis"
        and a1: "c \<in> vis"
        and a2: "callOrigin C c \<triangleq> tx"
        and a3: "tx \<noteq> t"
        and a4: "s = s'"

      show "transactionStatus C tx \<triangleq> Committed"
      proof (cases "c \<in> vis'")
        case True
        then show "transactionStatus C tx \<triangleq> Committed"
          using IH1 a2 \<open>currentTransaction C s' = None\<close> \<open>visibleCalls C s' \<triangleq> vis'\<close> by fastforce
      next
        case False
        from \<open>chooseSnapshot snapshot vis' C\<close>
        show "transactionStatus C tx \<triangleq> Committed"
        proof (rule chooseSnapshot_committed2)
          show "c \<in> snapshot"
            by (simp add: a0 g2)
          show " callOrigin C c \<triangleq> tx"
            by (simp add: a2)
          show "c \<notin> vis'" using False  .
          show "\<And>c c' tx tx'. \<lbrakk>(c', c) \<in> happensBefore C; callOrigin C c \<triangleq> tx; callOrigin C c' \<triangleq> tx'; transactionStatus C tx \<triangleq> Committed\<rbrakk> \<Longrightarrow> transactionStatus C tx' \<triangleq> Committed"
            using IH4 by blast
        qed
      qed
    qed
  next
    case (endAtomic s' ls f ls' t)
    show ?thesis 
      using g1 g2 g3 apply (auto simp add: endAtomic)
      using IH1 local.endAtomic(6) apply fastforce
      using IH1 by blast
      
  next
    case (dbop s' ls f Op args ls' t c' res vis')
    show ?thesis 
      using g1 g2 g3 apply (auto simp add: dbop split: if_splits)
      using IH1 local.dbop(6) local.dbop(9) apply fastforce
      using local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 apply blast
      using IH1 by blast
      
  next
    case (invocId s' procName args initialState impl)
    show ?thesis 
      using IH1 g1 g2 g3 by (auto simp add: invocId split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocId split: if_splits)
  next
    case (fail s ls)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocId split: if_splits)
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
          and c3: "C' = C \<lparr>localState := localState C(s' \<mapsto> ls'), currentTransaction := currentTransaction C(s' \<mapsto> t), transactionStatus := transactionStatus C(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin C(t \<mapsto> s'), visibleCalls := visibleCalls C(s' \<mapsto> vis)\<rparr>"
          and c4: "localState C s' \<triangleq> ls"
          and c5: "currentProc C s' \<triangleq> f"
          and c6: "f ls = BeginAtomic ls'"
          and c7: "currentTransaction C s' = None"
          and c8: "transactionStatus C t = None"
          and c9: "visibleCalls C s' \<triangleq> vis'"
          and c10: "chooseSnapshot vis vis' C"
          and c11: "s = s'"
          and c12: "snapshot = vis"

      show "c2 \<in> vis"
      proof (cases "callOrigin C c1")
        case None
        then show "c2 \<in> vis"
          by (smt IH1' action.distinct(31) c2 callOrigin_same_committed domD domIff g1 g2 g3 snd_conv state_wellFormed_combine_step step.hyps(1) step.hyps(6) step.hyps(7) subsetCE transactionStatus_mono2 wellFormed_callOrigin_dom wellFormed_state_calls_from_current_transaction_in_vis wellFormed_visibleCallsSubsetCalls_h(2))
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
          and c3: "C' = C \<lparr>localState := localState C(s' \<mapsto> ls'), currentTransaction := currentTransaction C(s' \<mapsto> t), transactionStatus := transactionStatus C(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin C(t \<mapsto> s'), visibleCalls := visibleCalls C(s' \<mapsto> snapshot)\<rparr>"
          and c4: "localState C s' \<triangleq> ls"
          and c5: "currentProc C s' \<triangleq> f"
          and c6: "f ls = BeginAtomic ls'"
          and c7: "currentTransaction C s' = None"
          and c8: "transactionStatus C t = None"
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
    case (dbop s' ls f Op args ls' t c res vis')
    show ?thesis  
    proof (cases "s' = s")
      case True
      then show ?thesis 
      using g1 g2 g3 apply (auto simp add: dbop split: if_splits)
      apply (metis local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_state_calls_from_current_transaction_in_vis)
      using local.dbop(7) local.dbop(9) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 apply blast
      using IH2 local.dbop(9) by blast
      
    next
      case False

      have not_committed_h: "transactionStatus C t \<noteq> Some Committed" if "c1 \<in> vis"
        using local.dbop(6) not_uncommitted_cases step.hyps(1) wellFormed_currentTransactionUncommitted by blast
      
      show ?thesis 
      using False g1 g2 g3 apply (auto simp add: dbop split: if_splits)
      using not_committed_h IH1 local.dbop(6) step.hyps(1) wellFormed_currentTransaction_unique_h(1) apply blast
      using local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 apply blast 
      using IH2 by blast
    qed
  next
    case (invocId s procName args initialState impl)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (fail s ls)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (invCheck res s)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  qed
  
  show IH4': "transactionStatus C' tx' \<triangleq> Committed \<or> tx' = tx"
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
      using g1 g2 g3 apply (auto simp add: beginAtomic split: if_splits)
      using local.beginAtomic(7) step.hyps(1) wellFormed_state_callOrigin_transactionStatus apply blast
      using IH4 by blast
      
  next
    case (endAtomic s ls f ls' t)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (dbop s ls f Op args ls' t c res vis)
    show ?thesis 
      using g1 g2 g3 apply (auto simp add: dbop split: if_splits)
      using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_r apply blast
      using IH1 local.dbop(6) local.dbop(9) apply fastforce
      using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l apply blast
      using IH4 by blast
      
  next
    case (invocId s procName args initialState impl)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (return s ls f res)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (fail s ls)
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
      case (dbop s ls f Op args ls' t c res vis)
      
      from \<open>calls C c = None\<close>
      have c_no_hb1[simp]: "(x, c) \<notin> happensBefore C" for x
        using wellFormed_visibleCallsSubsetCalls_h(1)[OF \<open>state_wellFormed C\<close>] by auto
        
      have [simp]: "callOrigin C c = None"
        by (simp add: local.dbop(7) step.hyps(1) wf_callOrigin_and_calls)
        
      have t_uncomited[simp]:  "transactionStatus C t \<triangleq> Uncommitted"
          using local.dbop(6) step.hyps(1) wellFormed_currentTransactionUncommitted by blast
      
      have origin_t: "callOrigin C y2 \<triangleq> t" 
            if "callOrigin C y1 = callOrigin C y2"
            and "callOrigin C x1 \<triangleq> t"
            and "(x1, y1) \<in> happensBefore C"
            for x1 y1 y2
            by (metis IH3_to \<open>callOrigin C c = None\<close> \<open>transactionStatus C t \<triangleq> Uncommitted\<close> that c_no_hb1 not_None_eq option.inject step.hyps(5) transactionStatus.distinct(1))      
          
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
      case (invocId s procName args initialState impl)
      then show ?thesis using whenUnchanged by auto
    next
      case (return s ls f res)
      then show ?thesis using whenUnchanged by auto
    next
      case (fail s ls)
      then show ?thesis using whenUnchanged by auto
    next
      case (invCheck res s)
      then show ?thesis using whenUnchanged by auto
    qed
  qed
qed  



lemma wellFormed_state_consistent_snapshot:
assumes wf: "state_wellFormed S"
assumes vis: "visibleCalls S s \<triangleq> vis"
assumes noTx: "currentTransaction S s = None" 
shows "consistentSnapshot S vis"
unfolding consistentSnapshotH_def proof (intro conjI)
  show "vis \<subseteq> dom (calls S)"
    using wf vis
    using wellFormed_visibleCallsSubsetCalls_h(2) by fastforce 
    
  show "causallyConsistent (happensBefore S) vis"
    using local.wf vis wellFormed_state_causality(1) by auto
    
  show "transactionConsistent (callOrigin S) (transactionStatus S) vis"
  proof (induct rule: show_transactionConsistent)
    case (only_committed c tx)
    then show ?case 
      using noTx vis
      using local.wf wellFormed_state_transaction_consistent(1) by fastforce 
  next
    case (all_from_same c1 c2)
    then show ?case
      using local.wf vis wellFormed_state_transaction_consistent(2) by blast 
  qed
qed
    
lemma happensBefore_in_calls_left:
assumes wf: "state_wellFormed S"
    and "(x,y)\<in>happensBefore S"
shows "x\<in>dom (calls S)"
using assms  apply (induct rule: wellFormed_induct) 
apply (auto simp add: initialState_def step_simps_all)
  by (meson domD domIff wellFormed_visibleCallsSubsetCalls2)

lemma happensBefore_in_calls_right:
assumes wf: "state_wellFormed S"
    and "(x,y)\<in>happensBefore S"
shows "y\<in>dom (calls S)"
using assms  apply (induct rule: wellFormed_induct) 
by (auto simp add: initialState_def step_simps_all)

lemma happensBefore_transitive:
assumes wf: "state_wellFormed S"
shows "trans (happensBefore S)"
using assms  apply (induct rule: wellFormed_induct) 
apply (auto simp add: initialState_def step_simps_all)
apply (subst trans_def)
apply (auto dest: transD)
  apply (meson causallyConsistent_def wellFormed_state_causality(1))
  by (meson domIff happensBefore_in_calls_left)
  





lemma causallyConsistent_downwards:
  assumes  cs: "causallyConsistent hb vis"
    and trans: "trans hb"
  shows "causallyConsistent hb (vis \<union> S \<down> hb)"
proof -
  show ?thesis
    using cs apply (auto simp add: causallyConsistent_def downwardsClosure_def)
    by (meson local.trans transE)
qed

lemma wf_vis_downwards_closed:
  assumes wf: "state_wellFormed S"
    and "trans (happensBefore S)"
    and "visibleCalls S i \<triangleq> Vis"
    and "(X,Y) \<in> happensBefore S"
    and "Y\<in>Vis"
  shows "X\<in>Vis"
  by (meson assms causallyConsistent_def local.wf wellFormed_state_causality(1))


lemma wf_causallyConsistent1:
  assumes wf: "state_wellFormed S"
and "visibleCalls S i \<triangleq> vis"
shows "causallyConsistent (happensBefore S) vis"
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
    and "currentTransaction S i \<noteq> Some tx"
  shows "transactionStatus S tx \<triangleq> Committed"
  using assms(2) assms(3) assms(4) assms(5) local.wf wellFormed_state_transaction_consistent(1) by blast

lemma flip: "(\<not>Q \<Longrightarrow> \<not>P) \<Longrightarrow> P \<longrightarrow> Q"
  by auto




lemma wf_transactionConsistent_noTx:
  assumes wf: "state_wellFormed S"
and "visibleCalls S i \<triangleq> vis"
and "currentTransaction S i = None"
shows "transactionConsistent (callOrigin S) (transactionStatus S) vis"

proof (auto simp add: transactionConsistent_def)
  show "transactionStatus S tx \<triangleq> Committed" if "c \<in> vis" and "callOrigin S c \<triangleq> tx" for c tx
    using assms(2) assms(3) local.wf that(1) that(2) wellFormed_state_transaction_consistent(1) by fastforce

  show "\<And>c1 c2. \<lbrakk>c1 \<in> vis; callOrigin S c1 = callOrigin S c2\<rbrakk> \<Longrightarrow> c2 \<in> vis"
    using assms(2) local.wf wellFormed_state_transaction_consistent(2) by blast

qed

text \<open>
If we have an execution on a a single invocId starting with state satisfying the invariant, then we can convert 
this trace to a single-invocId trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
\<close>
lemma convert_to_single_session_trace:
  fixes tr :: "'any::valueType trace"
    and s :: invocId      
    and S S' :: "('ls,'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds on all states in the execution\<close>
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
    \<comment> \<open>TODO special case for fail, pull (and others?)\<close>
  using steps S_wellformed packed inv noFails noUncommitted noCtxtSwitchInTx proof (induct rule: steps.induct)
  case (steps_refl S)

  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="S"], intro conjI; simp?)
    show "S ~~ (s, []) \<leadsto>\<^sub>S* S"
      by (simp add: steps_s_refl) 
    show "state_coupling S S s True"
      unfolding state_coupling_def 
      by auto
  qed
next
  case (steps_step S tr S' a S'')
  then have  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; packed_trace tr; 
               \<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
                   \<and> (\<forall>a. (a, False) \<notin> set tr') 
                   \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
    and  step: "S' ~~ a \<leadsto> S''"
    and  packed: "packed_trace (tr @ [a])"
    and prefix_invariant: "\<And>tr' S'.  \<lbrakk>isPrefix tr' (tr @ [a]); S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
    and noFails: "\<And>s. (s, AFail) \<notin> set (tr @ [a])"
    and noContextSwitch: "noContextSwitchesInTransaction (tr @ [a])"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by (auto, blast)

  have noFails_tr: "\<And>i. (i, AFail) \<notin> set tr"
    using steps_step.prems(4) by auto

  have steps': "S ~~ tr @ [a] \<leadsto>* S''"
    using steps step steps.steps_step by blast 

  from prefix_invariant steps
  have inv': "invariant_all S'"
    using isPrefix_appendI by blast


  from prefix_invariant steps'
  have inv'': "invariant_all S''"
    by (metis append.right_neutral isPrefix_appendI)

  have "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
         \<and> (\<forall>a. (a, False) \<notin> set tr') 
         \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
  proof (rule IH)
    have "isPrefix tr (tr@[a])"
      by (simp add: isPrefix_appendI)
    then show "packed_trace tr"
      using packed prefixes_are_packed by blast 
    show "\<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using prefix_invariant isPrefix_append by blast 
    show "state_wellFormed S" using S_wf .
  qed

  from this obtain tr' S2
    where ih1: "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
      and ih2: "\<And>a. (a, False) \<notin> set tr'"
      and ih3': "state_coupling S' S2 s  (tr = [] \<or> fst (last tr) = s)"
    by blast

  show  "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s (tr @ [a] = [] \<or> fst (last (tr @ [a])) = s)"  
  proof (cases "fst a = s"; simp)
    case True \<comment> \<open>the new action is on invocId s\<close>
    then have [simp]: "fst a = s" .

    show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s True"  (is ?goal) 
    proof (cases "tr = [] \<or> fst (last tr) = s")
      case True \<comment> \<open>the previous action was on the same trace (if there was a previous action)\<close>
      then have [simp]: "tr = [] \<or> fst (last tr) = s" by simp
      then have ih3: "state_coupling S' S2 s True"
        using ih3' by simp

      have ih3_tx: "S2 = S'"
        using ih3' state_coupling_def by force

(*
      have ih3_noTx: "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>" if "currentTransaction S' s = None"
        using ih3 that by (auto simp add: state_coupling_def)
      have ih3_tx: "S2 = S'" if "currentTransaction S' s \<triangleq> tx" for tx
        using ih3 that by (auto simp add: state_coupling_def)
*)

      have S2_calls: "calls S2 = calls S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_happensBefore: "happensBefore S2 = happensBefore S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_prog: "prog S2 = prog S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_localState: "localState S2 = localState S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_currentProc: "currentProc S2 = currentProc S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_currentTransaction: "currentTransaction S2 = currentTransaction S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_transactionStatus: "transactionStatus S2 = transactionStatus S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_callOrigin: "callOrigin S2 = callOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_transactionOrigin: "transactionOrigin S2 = transactionOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_generatedIds: "generatedIds S2 = generatedIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_knownIds: "knownIds S2 = knownIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocationOp: "invocationOp S2 = invocationOp S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
      have S2_invocationRes: "invocationRes S2 = invocationRes S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)

      note S2_simps = 
        S2_calls S2_happensBefore S2_prog S2_localState S2_currentProc S2_currentTransaction
        S2_transactionStatus S2_callOrigin S2_transactionOrigin S2_generatedIds S2_knownIds S2_invocationOp S2_invocationRes


      have S'_wf: "state_wellFormed S'"
        using S_wf steps noFails_tr by (rule state_wellFormed_combine)


      have vis_defined: "visibleCalls S' s \<noteq> None" if "currentTransaction S' s \<noteq> None"
        using S'_wf state_wellFormed_tx_to_visibleCalls that by auto
          (*
      obtain vis'
        where vis'_sub: "vis' orElse {} \<subseteq>visibleCalls S' s orElse {}"
          and vis'_else: "currentTransaction S' s \<noteq> None \<Longrightarrow> vis' = visibleCalls S' s"
          and S2_vis': "S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
      proof (atomize_elim, cases "currentTransaction S' s")
        case None
        hence currentTxNone: "currentTransaction S' s = None" .

        from ih3_noTx[OF currentTxNone] obtain vis''  
          where vis''1: "vis'' orElse {} \<subseteq> visibleCalls S' s orElse {}" 
            and vis''2: "S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis'')\<rparr>"
          by metis

        show " \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> (currentTransaction S' s \<noteq> None \<longrightarrow> vis' = visibleCalls S' s) \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
          by (rule_tac x="vis''" in exI, auto simp add: currentTxNone vis''1 vis''2) 

      next
        case (Some tx)
        hence currentTxSome: "currentTransaction S' s \<triangleq> tx" .

        from ih3_tx[OF currentTxSome] have sameStates: "S2 = S'" .


        show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> (currentTransaction S' s \<noteq> None \<longrightarrow> vis' = visibleCalls S' s) \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
          by (rule exI[where x="visibleCalls S' s"], auto simp add: sameStates)
      qed   
*)

      have tr_noSwitch: "noContextSwitchesInTransaction tr"
        using isPrefix_appendI noContextSwitch prefixes_noContextSwitchesInTransaction by blast

      have tr_packed: "packed_trace tr"
        using packed packed_trace_prefix by blast

      have tr_noFail: "\<And>s. (s, AFail) \<notin> set tr"
        using steps_step.prems(4) by auto


      show ?goal
      proof (cases "snd a")
        case ALocal
        then have "a = (s, ALocal)"
          by (simp add: prod.expand) 

        with step
        have step': "S' ~~ (s, ALocal) \<leadsto> S''" by simp

        from step_elim_ALocal[OF step']
        obtain ls f ls' 
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls')\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = LocalStep ls'"
          by metis

        have a2': "localState S2 s \<triangleq> ls" 
          using a2 ih3 by (auto simp add: state_coupling_def split: if_splits)
        have a3': "currentProc S2 s \<triangleq> f" 
          using a3 ih3 by (auto simp add: state_coupling_def split: if_splits)
        from a2' a3' a4
        have step_s: "S2 ~~ (s,(ALocal,True)) \<leadsto>\<^sub>S S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr>"
          by (rule step_s.local)

        have S''_S2: "S'' = S2\<lparr>localState := localState S2(s \<mapsto> ls'), visibleCalls := visibleCalls S''\<rparr>"  
          by (auto simp add: state_ext \<open>S2 = S'\<close>  a1)

        then have S''_S2_a: "S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr> = S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"  
          by (auto simp add: state_ext)

        from ih1
        have steps_s: "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
        proof (rule steps_s_step)
          from step_s
          show "S2 ~~ (s, ALocal, True) \<leadsto>\<^sub>S S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
            using a1 S''_S2_a by auto
        qed  

        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>" using steps_s .
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ALocal, True)])"
            by (simp add: ih2) 
          show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s True"
            (*show "if currentTransaction S'' s = None 
            then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>
            else S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"*)
            unfolding state_coupling_def
          proof auto
            show " S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"
              by (auto simp add: ih3_tx a1)
          qed
        qed
      next
        case (ANewId uid)
        then have [simp]: "a = (s, ANewId uid)"
          by (simp add: prod_eqI steps_step.prems) 

        with step
        have step': "S' ~~ (s, ANewId uid) \<leadsto> S''" by simp

        from step_elim_ANewId[OF step']
        obtain ls f ls' ls''
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls''), generatedIds :=  generatedIds S'(uid \<mapsto> s)\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = NewId ls'"
            and a5: "generatedIds S' uid = None"
            and a6: "uniqueIds uid = {uid}"
            and a7: "ls' uid \<triangleq> ls''"
          by metis  

        have a2':  "localState S2 s \<triangleq> ls" using a2 by (simp add: S2_localState) 
        have a3':  "currentProc S2 s \<triangleq> f" using a3 by (simp add: S2_currentProc)
        have a5':  "generatedIds S2 uid = None" using a5 by (simp add: S2_generatedIds)

        from a2' a3' a4 a5' a6 a7
        have step_s: "S2 ~~ (s,(ANewId uid,True)) \<leadsto>\<^sub>S S2\<lparr>localState := localState S2(s \<mapsto> ls''), generatedIds :=  generatedIds S2(uid \<mapsto> s)\<rparr>"
          by (rule step_s.newId)

        have S''_S2: "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S2\<lparr>localState := localState S2(s \<mapsto> ls''), generatedIds := generatedIds S2(uid \<mapsto> s)\<rparr>" 
          by (auto simp add: a1 S2_simps)


        from ih1
        have steps_s: "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
        proof (rule steps_s_step)
          from step_s
          show "S2 ~~ (s, ANewId uid, True) \<leadsto>\<^sub>S S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
            using S''_S2 by auto
        qed  

        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>" using steps_s .
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ANewId uid, True)])"
            by (simp add: ih2) 
          show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s True"
            unfolding state_coupling_def
            by (simp add: a1 ih3_tx)

        qed  

      next
        case (ABeginAtomic txId snapshot)
        then have [simp]: "a = (s, ABeginAtomic txId snapshot)"
          by (simp add: prod_eqI steps_step.prems) 

        with step
        have step': "S' ~~ (s, ABeginAtomic txId snapshot) \<leadsto> S''" by simp

        from step_elim_ABeginAtomic[OF step']
        obtain ls f ls' vis
          where a1: "S'' = S'\<lparr>
                  localState := localState S'(s \<mapsto> ls'), 
                  currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                  transactionStatus := transactionStatus S'(txId \<mapsto> Uncommitted),
                  transactionOrigin := transactionOrigin S'(txId \<mapsto> s),
                  visibleCalls := visibleCalls S'(s \<mapsto> snapshot)\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' s = None"
            and a6: "transactionStatus S' txId = None"
            and a7: "visibleCalls S' s \<triangleq> vis"
            and a8: " chooseSnapshot snapshot vis S'"
          by smt
            (*
      where a1: "S'' = S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommitted)\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = BeginAtomic ls'"
        and a5: "currentTransaction S' s = None"
        and a6: "transactionStatus S' txId = None"*)

        have a2': "localState S2 s \<triangleq> ls" using a2 S2_simps by auto
        have a3': "currentProc S2 s \<triangleq> f" using a3 S2_simps by auto 
        have a5': "currentTransaction S2 s = None" using a5 S2_simps by auto
        have a6': "transactionStatus S2 txId = None" using a6 S2_simps by auto

        have inv': "invariant_all S'" 
        proof (rule prefix_invariant)
          show "S ~~ tr \<leadsto>* S'" using steps .
          show "isPrefix tr (tr @ [a])"
            by (simp add: isPrefix_appendI) 
        qed



        define newS where "newS =  (S'\<lparr>
          localState := localState S2(s \<mapsto> ls'),
          currentTransaction := currentTransaction S2(s \<mapsto> txId), 
          transactionStatus := transactionStatus S2(txId \<mapsto> Uncommitted),
          transactionOrigin := transactionOrigin S2(txId \<mapsto> s),
          visibleCalls := visibleCalls S'(s \<mapsto> snapshot)
        \<rparr>)"  


        from a2' a3' a4 a5' a6' 
        have step_s: "S2 ~~ (s,(ABeginAtomic txId snapshot,True)) \<leadsto>\<^sub>S newS"
        proof (rule step_s.beginAtomic)  
          show "prog S' = prog S2"
            by (simp add: S2_prog)

          show "localState S' s \<triangleq> ls"
            by (simp add: a2)

          show "currentTransaction S' s = None"
            by (simp add: a5)

          show "transactionStatus S' txId = None"  
            by (simp add: a6)

          show "transactionOrigin S' txId = None"
            using S'_wf a6 wf_transaction_status_iff_origin by blast



(*
          have [simp]: "consistentSnapshot newS vis \<Longrightarrow> consistentSnapshot S' vis" for vis
            apply (auto simp add: consistentSnapshotH_def newS_def a6' transactionConsistent_def split: if_splits)
            by (metis S2_transactionStatus option.inject transactionStatus.distinct(1))
*)

          have noFail1: "(i, AFail) \<notin> set (tr @ [a])" for i
            using steps_step.prems by blast
          then have noFail2: "(i, AFail) \<notin> set tr" for i
            by force


          show "invariant_all S'" 
            using inv'
            using S2_currentTransaction S2_localState S2_transactionStatus  a1 inv''  S2_transactionOrigin  by fastforce

          show "state_wellFormed newS"
            using S2_currentTransaction S2_localState S2_transactionOrigin S2_transactionStatus S_wf newS_def a1 state_wellFormed_combine steps' noFail2  by fastforce


          have " state_wellFormed S'"
            using S'_wf by auto


          show "state_monotonicGrowth s S2 S'"
            using ih3 S'_wf state_monotonicGrowth_refl by (auto simp add: state_coupling_def )


          show "\<And>t. transactionOrigin S2 t \<triangleq> s = transactionOrigin S' t \<triangleq> s"
            by (simp add: ih3_tx)


          show "currentProc S' s \<triangleq> f"
            by (simp add: a3 newS_def)


          show "state_wellFormed S'"
            using S'_wf by blast 

          show "\<And>c. callOrigin S' c \<noteq> Some txId"
            using \<open>transactionStatus S' txId = None\<close> \<open>state_wellFormed S'\<close>
            by (simp add: wf_no_transactionStatus_origin_for_nothing)




          have "transactionStatus S' tx \<noteq> Some Uncommitted" if "tx \<noteq> txId" for tx
          proof (rule notI)
            assume a: " transactionStatus S' tx \<triangleq> Uncommitted"

            {
              assume "0 < length tr"
              from \<open>S ~~ tr \<leadsto>* S'\<close> S_wf
              have "currentTransaction S' (fst (last tr)) \<triangleq> tx "
              proof (rule only_one_commmitted_transaction_h[THEN conjunct1])

                show "packed_trace tr"
                  using isPrefix_appendI packed prefixes_are_packed by blast 
                show "transactionStatus S' tx \<triangleq> Uncommitted"
                  by (simp add: a)


                show "\<And>s. (s, AFail) \<notin> set tr"
                  using \<open>\<And>s. (s, AFail) \<notin> set (tr@[a])\<close> by auto

                show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
                  using \<open>\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted\<close> .

                show "noContextSwitchesInTransaction tr"
                  using \<open>noContextSwitchesInTransaction (tr @ [a])\<close> isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast 

              qed

              then have False
                using True \<open>0 < length tr\<close> a5 by fastforce
            }
            moreover
            {
              assume "tr = []"
              with \<open>S ~~ tr \<leadsto>* S'\<close>
              have "S' = S"
                by (simp add: steps_empty)
              then have False
                using a \<open>\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted\<close>  by blast
            }
            ultimately show "False"
              by auto
          qed
          then show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
            using a6 by force


          find_theorems S2

          show "visibleCalls S2 s \<triangleq> vis"
            using a7 ih3_tx by blast

          have wf_S2: "state_wellFormed S2"
            by (simp add: S'_wf ih3_tx)

          show "visibleCalls S' s \<triangleq> vis"
            by (simp add: a7)

          show "newS = S'\<lparr>transactionStatus := transactionStatus S'(txId \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(txId \<mapsto> s),
                currentTransaction := currentTransaction S'(s \<mapsto> txId), localState := localState S'(s \<mapsto> ls'), visibleCalls := visibleCalls S'(s \<mapsto> snapshot )\<rparr>"
            using ih3_tx by (auto simp add: newS_def state_ext)

          show "chooseSnapshot snapshot vis S'"
            by (simp add: a8)


          show "consistentSnapshot S' snapshot"
          proof (rule show_consistentSnapshot)
            show "snapshot \<subseteq> dom (calls S')"
              using a8 apply (auto simp add: chooseSnapshot_def)
               apply (meson S'_wf a7 domD subsetCE wellFormed_visibleCallsSubsetCalls_h(2))
              apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
              using S'_wf wellFormed_callOrigin_dom apply fastforce
              by (meson S'_wf option.exhaust wellFormed_happensBefore_calls_l)

            show "causallyConsistent (happensBefore S') snapshot"
              using a8 S'_wf a7 chooseSnapshot_causallyConsistent_preserve happensBefore_transitive wellFormed_state_causality(1) by blast 

            show "transactionConsistent (callOrigin S') (transactionStatus S') snapshot"
              using a8 proof (rule chooseSnapshot_transactionConsistent_preserve)
              show " transactionConsistent (callOrigin S') (transactionStatus S') vis"
                using S'_wf a5 a7 wf_transactionConsistent_noTx by auto
              show "\<And>c tx. callOrigin S' c \<triangleq> tx \<Longrightarrow> transactionStatus S' tx \<triangleq> Committed"
                using S'_wf \<open>\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted\<close> not_uncommitted_cases wf_no_transactionStatus_origin_for_nothing by fastforce
              show "\<And>x y z tx. \<lbrakk>(x, z) \<in> happensBefore S'; callOrigin S' x \<triangleq> tx; callOrigin S' y \<triangleq> tx; callOrigin S' z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y, z) \<in> happensBefore S'"
                by (simp add: S'_wf wf_happensBefore_txns_left)
              show "\<And>ca cb tx. \<lbrakk>callOrigin S' ca \<triangleq> tx; (cb, ca) \<in> happensBefore S'\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S' cb \<triangleq> tx"
                by (meson S'_wf domD domIff wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l)
            qed
          qed
        qed


        

        moreover have "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
          using ih1 by auto


        moreover have "S'' = newS"
          by (auto simp add: a1 newS_def S2_localState S2_currentTransaction S2_transactionStatus S2_transactionOrigin)  



        ultimately have steps_S''_s: "S ~~ (s, tr'@[(ABeginAtomic txId snapshot, True)]) \<leadsto>\<^sub>S* S''"
          using steps_s_step by blast



        show ?thesis
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ABeginAtomic txId snapshot, True)]) \<leadsto>\<^sub>S* S''"
            using steps_S''_s .
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic txId snapshot, True)])"
            by (simp add: ih2)     
          show "state_coupling S'' S'' s True"  
            unfolding state_coupling_def
            by (simp add: a1)
        qed    

      next
        case AEndAtomic
        then have [simp]: "a = (s, AEndAtomic)"
          by (simp add: local.steps_step(5) prod_eqI)

        with step
        have step': "S' ~~ (s, AEndAtomic) \<leadsto> S''" by simp

        from step_elim_AEndAtomic[OF step']  
        obtain ls f ls' t 
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls'), 
              currentTransaction := (currentTransaction S')(s := None), 
              transactionStatus := transactionStatus S'(t \<mapsto> Committed)\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = EndAtomic ls'"
            and a5: "currentTransaction S' s \<triangleq> t"
          by metis  

        have "S2 = S'"
          using a5 ih3_tx by blast

        have "invariant_all S'"
          using  steps
          by (metis (no_types, lifting) isPrefix_appendI steps_step.prems(3)) 


\<comment> \<open>from a2 a3 a4 a5\<close>
        from a2 a3 a4 a5 a1
        have step_s: "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
        proof (rule step_s.endAtomic)  
          from \<open>invariant_all S'\<close>
          show "True = invariant_all S''"
            by (simp add: inv'')
          show "state_wellFormed S''"
            using S_wf noFails state_wellFormed_combine steps' by blast
        qed  

        with \<open>S2 = S'\<close>
        have "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
          by simp

        then have steps_S''_s: "S ~~ (s, tr'@[(AEndAtomic,True)]) \<leadsto>\<^sub>S* S''"
          using \<open>S2 = S'\<close> ih1 steps_s_step by blast  


        show ?thesis
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(AEndAtomic,True)]) \<leadsto>\<^sub>S* S''" using steps_S''_s.
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(AEndAtomic, True)])"
            by (simp add: ih2)
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def
            by (auto simp add: a1)
        qed
      next
        case (ADbOp cId operation args res)
        then have [simp]: "a = (s, ADbOp cId operation args res)"
          by (simp add: prod.expand steps_step.prems(2)) 

        with step
        have step': "S' ~~ (s, ADbOp cId operation args res) \<leadsto> S''" by simp

        from step_elim_ADbOp[OF step']  
        obtain ls f ls' t vis 
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls' res), 
                        calls := calls S'(cId \<mapsto> Call operation args res), 
                        callOrigin := callOrigin S'(cId \<mapsto> t), 
                        visibleCalls := visibleCalls S'(s \<mapsto> insert cId vis),
                        happensBefore := happensBefore S' \<union> vis \<times> {cId}\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = DbOperation operation args ls'"
            and a5: "currentTransaction S' s \<triangleq> t"
            and a6: "calls S' cId = None"
            and a7: "querySpec (prog S') operation args (getContextH (calls S') (happensBefore S') (Some vis)) res"
            and a8: "visibleCalls S' s \<triangleq> vis"
          by metis  

        have "S2 = S'"
          using ih3 by (auto simp add: a5 ih3 state_coupling_def)

        from a2 a3 a4 a5 a6 
        have step_s: "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S'\<lparr>localState := localState S'(s \<mapsto> ls' res), 
                        calls := calls S'(cId \<mapsto> Call operation args res), 
                        callOrigin := callOrigin S'(cId \<mapsto> t), 
                        visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> {cId}),
                        happensBefore := happensBefore S' \<union> vis \<times> {cId}\<rparr>"
        proof (rule step_s.dbop)  
          show "querySpec (prog S') operation args (getContext S' s) res"
            using a7 by (simp add: a8) 
          show "visibleCalls S' s \<triangleq> vis" using a8 .
        qed  
        then have step_s': "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S''"
          by (simp add: a1)


        show ?thesis
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ADbOp cId operation args res,True)]) \<leadsto>\<^sub>S* S''" 
            using step_s' \<open>S2 = S'\<close> ih1 steps_s_step by blast 
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ADbOp cId operation args res, True)])"
            by (simp add: ih2)
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def
            by (auto simp add: a1 a5 state_ext)
        qed    
      next
        case (AInvoc procName args)
        then have "a = (s, AInvoc procName args)"
          by (simp add: prod_eqI steps_step.prems(2))

        with step
        have step': "S' ~~ (s, AInvoc procName args) \<leadsto> S''" by simp  

        from step_elim_AInvoc[OF step'] 
        obtain initialState impl
          where a1: "S'' = S'\<lparr>
                   localState := localState S'(s \<mapsto> initialState), 
                   currentProc := currentProc S'(s \<mapsto> impl), 
                   visibleCalls := visibleCalls S'(s \<mapsto> {}), 
                   invocationOp := invocationOp S'(s \<mapsto> (procName, args))\<rparr>"
            and a2: "localState S' s = None"
            and a3: "procedure (prog S') procName args \<triangleq> (initialState, impl)"
            and a4: "uniqueIdsInList args \<subseteq> knownIds S'"
            and a5: "invocationOp S' s = None"
          by metis


        have inv_S': "invariant_all S'"
          using inv' by blast

        have vis_None: "visibleCalls S' s = None"
          using  S_wf a2 state_wellFormed_combine steps state_wellFormed_ls_visibleCalls tr_noFail by blast 

        have "visibleCalls S2 s = None \<or> visibleCalls S2 s \<triangleq> {}"
          by (simp add: ih3_tx vis_None)



        then have invContextSame: "invContext S2 =  invContext S'"
          by (auto simp add: S2_simps vis_None invContextH_def)


        find_theorems steps tr


        have at_most_one_tx: "(\<forall>i tx. ((i, tx) \<in> openTransactions tr) = currentTransaction S' i \<triangleq> tx) \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
        proof (rule at_most_one_active_tx[OF \<open> S ~~ tr \<leadsto>* S'\<close>])
          show "state_wellFormed S"
            using S_wf by auto
          show "packed_trace tr"
            using packed packed_trace_prefix by auto
          show " \<And>s. (s, AFail) \<notin> set tr"
            using steps_step.prems(4) by auto
          show  " \<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
            using steps_step.prems(5) by blast
          show  "noContextSwitchesInTransaction tr"
            using isPrefix_appendI noContextSwitch prefixes_noContextSwitchesInTransaction by blast
        qed


        have noCurrentTransaction_s: "currentTransaction S' s = None"
          using vis_None vis_defined by blast 





        have noCurrentTransaction: "currentTransaction S' i = None" for i
          using \<open>S' ~~ a \<leadsto> S''\<close>
          using \<open>fst a = s\<close> a2 \<open>snd a = AInvoc procName args\<close> apply (auto simp add: step.simps)

          using at_most_one_current_tx[OF \<open>S ~~ tr \<leadsto>* S'\<close> \<open>noContextSwitchesInTransaction tr\<close> \<open>packed_trace tr\<close> \<open>state_wellFormed S\<close> \<open>\<And>s. (s, AFail) \<notin> set tr\<close>]
          by (metis S_wf True noCurrentTransaction_s option.exhaust steps steps_empty steps_step.prems(5) wellFormed_currentTransactionUncommitted)

        from at_most_one_tx and noCurrentTransaction
        have noOpenTxns: "openTransactions tr = {}" \<comment> \<open>TODO allgemeines lemma raus ziehen\<close>
          by auto



        with at_most_one_tx
        have currentTxNone: "\<And>i. currentTransaction S' i = None"
          by auto


        find_theorems S
        have step_s': "S ~~ (s, (AInvoc procName args, True)) \<leadsto>\<^sub>S S'' "
        proof (rule step_s.invocId)
          show "invocationOp S' s = None"
            by (simp add: S2_invocationOp a5)
          show "procedure (prog S) procName args \<triangleq> (initialState, impl)"
            using a3 steps steps_do_not_change_prog by force
          show "uniqueIdsInList args \<subseteq> knownIds S'"
            by (simp add: S2_knownIds a4)
          have "invocationOp S2 s = None"
            by (simp add: S2_invocationOp a5)
          have "invocationOp S' s = None"
            by (simp add: S2_invocationOp a5)
          then show "invocationOp S s = None"
            using steps steps_do_not_change_invocationOp by (metis not_Some_eq) 
          show "S'' = S'\<lparr>localState := localState S'(s \<mapsto> initialState), currentProc := currentProc S'(s \<mapsto> impl), visibleCalls := visibleCalls S'(s \<mapsto> {}), invocationOp := invocationOp S'(s \<mapsto> (procName, args))\<rparr>"
            by (auto simp add: state_ext S2_simps a1 )
          show "invariant_all S'"
            using ih3' inv_S' state_coupling_same_inv by auto
          show "True = invariant_all S''"
            by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps.steps_step)
          show "prog S' = prog S"
            using steps steps_do_not_change_prog by blast
          show "state_wellFormed S'"
            using S_wf state_wellFormed_combine steps tr_noFail by auto


          show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
            using currentTxNone \<open>state_wellFormed S'\<close> wellFormed_currentTransaction_back
            by (metis S_wf butlast_snoc in_set_butlastD option.distinct(1) steps steps_step.prems(4) steps_step.prems(5))

          have "\<And>tx. transactionOrigin S' tx \<noteq> Some s"
            by (simp add: S'_wf a5 wf_no_invocation_no_origin)

          then show "\<And>tx. transactionOrigin S'' tx \<noteq> Some s"
            using step' by (auto simp add: step_simps)

        qed



        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, [(AInvoc procName args, True)]) \<leadsto>\<^sub>S* S''"
            by (simp add: step_s' steps_s_single)
          show " \<forall>a. (a, False) \<notin> set ([(AInvoc procName args, True)])"
            by (simp add: ih2)
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def  
            by (auto simp add: a1 state_ext)
        qed    
      next
        case (AReturn res)
        then have "a = (s, AReturn res)"
          by (simp add: prod_eqI steps_step.prems(2))

        with step
        have step': "S' ~~ (s, AReturn res) \<leadsto> S''" by simp  

        from step_elim_AReturn[OF step']  
        obtain ls f
          where a1: "S'' = S'\<lparr>
                  localState := (localState S')(s := None), 
                  currentProc := (currentProc S')(s := None), 
                  visibleCalls := (visibleCalls S')(s := None), 
                  invocationRes := invocationRes S'(s \<mapsto> res),
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = Return res"
            and a5: "currentTransaction S' s = None"
          by metis

        have inv_S': "invariant_all S'"
          using isPrefix_appendI step_prog_invariant steps steps_step.prems(3) by fastforce  

        have inv_S'': "invariant_all S''"
          by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps_appendBack)


        have step_s': "S2 ~~ (s, (AReturn res, True)) \<leadsto>\<^sub>S S'' "
        proof (rule step_s.return)
          show "localState S2 s \<triangleq> ls"
            by (simp add: S2_localState a2)
          show "currentProc S2 s \<triangleq> f"
            by (simp add: S2_currentProc a3)
          show "f ls = Return res"
            by (simp add: a4)  
          show "currentTransaction S2 s = None"
            by (simp add: S2_currentTransaction a5)
          show "True = invariant_all S''" using inv_S''
            by simp
          show "S'' = S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S2(s \<mapsto> res), knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"  
            by (auto simp add: a1 state_ext S2_simps ih3_tx)

        qed    
        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(AReturn res, True)]) \<leadsto>\<^sub>S* S''"    
            using step_s' ih1 steps_s_step by blast 
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(AReturn res, True)])"
            using ih2 by auto
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def  
            by auto
        qed    
      next
        case AFail
        then have "a = (s, AFail)"
          by (simp add: prod_eqI steps_step.prems(2))
        with \<open>\<And>i. (i, AFail) \<notin> set (tr @ [a])\<close>  have "False"
          by auto
        then show ?thesis ..
      next
        case (AInvcheck res)
        then have "a = (s, AInvcheck  res)"
          by (simp add: prod_eqI steps_step.prems(2))

        with step
        have step': "S' ~~ (s, AInvcheck  res) \<leadsto> S''" by simp  

        from step_elim_AInvcheck[OF step']
        have a1: "S'' = S'" 
          (*and a2': "\<forall>t\<in>txns. transactionStatus S' t \<triangleq> Committed"
          and a4: "res = invariant (prog S') (invContextVis S' (callsInTransaction S' txns \<down> happensBefore S'))"*)
          by auto

        text \<open>We already assumed it holds for all possible set of visible calls\<close>

        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
            by (simp add: ih1)
          show "\<forall>a. (a, False) \<notin> set tr'"
            by (simp add: ih2)
          show "state_coupling S'' S2 s True"
            using ih3 by (auto simp add: state_coupling_def a1)
        qed
      qed
    next
      case False \<comment> \<open>we are coming from a different invocId and executing an action on s now\<close>
      then have [simp]: "tr \<noteq> []" and [simp]: "fst (last tr) \<noteq> s" by auto

      then have ih3: "state_coupling S' S2 s  False" using ih3' by simp

      from ih3  
      have S2_simps: "state_monotonicGrowth s S2 S'" 
        "localState S2 s = localState S' s" 
        "currentProc S2 s = currentProc S' s" 
        "currentTransaction S2 s = currentTransaction S' s" 
        "visibleCalls S2 s = visibleCalls S' s"
        by (auto simp add: state_coupling_def)


      text \<open>Because the trace is packed, there can only be two cases where we can go from another invocId to s:\<close>
      have "allowed_context_switch (snd a)"
      proof (rule context_switches_in_packed[OF packed])
        show "tr @ [a] = butlast tr @ [(fst (last tr), snd (last tr)), (s, snd a)] @ []"
          apply auto
          by (metis True prod.collapse)
        show "fst (last tr) \<noteq> s"
          by simp
      qed
      then have "(\<exists>tx txns. (snd a) = ABeginAtomic tx txns) \<or> (\<exists>p ar. (snd a) = AInvoc p ar)"
        using allowed_context_switch_def by blast
      then show ?thesis
      proof (rule disjE; clarsimp)
        fix tx snapshot
        assume "snd a = ABeginAtomic tx snapshot"

        with step
        have step': "S' ~~ (s, ABeginAtomic tx snapshot) \<leadsto> S''"
          by (metis True surjective_pairing) 

        from step_elim_ABeginAtomic[OF step']  
        obtain ls f ls' vis
          where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted),
                    transactionOrigin := transactionOrigin S'(tx \<mapsto> s), 
                    visibleCalls := visibleCalls S'(s \<mapsto> snapshot)\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' s = None"
            and a6: "transactionStatus S' tx = None"
            and a7: "visibleCalls S' s \<triangleq> vis"
            and a9: "chooseSnapshot snapshot vis S'"
          by smt
(*

          where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted),
                    transactionOrigin := transactionOrigin S'(tx \<mapsto> s),
                    visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> callsInTransaction S' txns \<down> happensBefore S')\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' s = None"
            and a6: "transactionStatus S' tx = None"
            and a7: "visibleCalls S' s \<triangleq> vis"
            and a8: "txns \<subseteq> committedTransactions S'"
          by smt
*)
            (*
      where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted)\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = BeginAtomic ls'"
        and a5: "currentTransaction S' s = None"
        and a6: "transactionStatus S' tx = None"
        by metis
    *)
        find_theorems "S'" S2    

        show ?thesis
        proof (intro exI conjI)
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic tx snapshot, True)])"
            using ih2 by auto

          show "state_coupling S'' S'' s True"
            by (auto simp add: state_coupling_def)

          have "S2 ~~ (s, ABeginAtomic tx snapshot, True) \<leadsto>\<^sub>S S''"
          proof (rule step_s.beginAtomic)
            show "localState S2 s \<triangleq> ls"
              using a2 ih3 by (simp add: state_coupling_def) 
            show "currentProc S2 s \<triangleq> f"  
              using a3 ih3  by (simp add: state_coupling_def)
            show "f ls = BeginAtomic ls'" using a4 .
            show "currentTransaction S2 s = None"
              using a5 ih3  by (auto simp add: state_coupling_def)
            show "transactionStatus S2 tx = None"
            proof -
              from ih3 have "transactionStatus S2 tx \<le> transactionStatus S' tx"
                by (auto simp add: state_coupling_def state_monotonicGrowth_transactionStatus)
              with a6
              show ?thesis
                by (simp add: less_eq_option_None_is_None)
            qed
            show "prog S' = prog S2"
              using ih3  prog_inv[OF local.step]
              by (auto simp add: state_coupling_def state_monotonicGrowth_prog)
            show "invariant_all S'"
              using inv' by blast
            show "localState S' s \<triangleq> ls"
              using a2 by auto
            show "currentTransaction S' s = None"
              by (simp add: a5)
            show "transactionStatus S' tx = None"
              by (simp add: a6)
            show "transactionOrigin S' tx = None"
              using S_wf a6 noFails_tr state_wellFormed_combine steps wf_transaction_status_iff_origin by blast

            show "state_wellFormed S''"
              using S_wf state_wellFormed_combine steps' noFails by blast
            show "state_monotonicGrowth s S2 S'"
              using ih3 by (auto simp add: state_coupling_def)
            show "currentProc S' s \<triangleq> f"
              by (simp add: a1 a3)
            show "\<And>c. callOrigin S' c \<noteq> Some tx"
              using S_wf a6 state_wellFormed_combine steps wf_callOrigin_implies_transactionStatus_defined a1 noFails by (auto, blast)


            have "\<forall>i. currentTransaction S'' i \<noteq> None \<longrightarrow> i = fst (last (tr@[a]))"
            proof (rule at_most_one_current_tx)
              show "S ~~ tr @ [a] \<leadsto>* S''"
                using steps' by auto

              show " noContextSwitchesInTransaction (tr@[a])"
                using  noContextSwitch  by blast
              show "packed_trace (tr@[a])"
                using packed by blast
              show "state_wellFormed S"
                by (simp add: S_wf)
              show "\<And>s. (s, AFail) \<notin> set (tr@[a])"
                using noFails by blast
              show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
                by (simp add: steps_step.prems(5))
            qed
            then have noCurrentTransaction: "currentTransaction S'' i = None" if "i\<noteq>s" for i
              using that by auto
            have "\<And>tx'. tx' \<noteq> tx \<Longrightarrow> transactionStatus S'' tx' \<noteq> Some Uncommitted"
            proof (rule wellFormed_currentTransaction_back4[OF \<open>state_wellFormed S''\<close>])
              fix tx' i
              assume a: "tx' \<noteq> tx"

              show "currentTransaction S'' i \<noteq> Some tx'"
              proof (cases "i=s")
                case True
                then show ?thesis 
                  using a by (simp add: a1)
              next
                case False
                then show ?thesis
                  by (simp add: noCurrentTransaction)
              qed
            qed


            then show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
              apply (simp add: a1)
              using a6 by force

            show "S'' = S'\<lparr>transactionStatus := transactionStatus S'(tx \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(tx \<mapsto> s), currentTransaction := currentTransaction S'(s \<mapsto> tx),
               localState := localState S'(s \<mapsto> ls'), visibleCalls := visibleCalls S'(s \<mapsto> snapshot)\<rparr>"
              by (auto simp add: a1 state_ext)

            show "chooseSnapshot snapshot vis S'" using a9 .



            show "state_wellFormed S'"
              using S_wf noFails_tr state_wellFormed_combine steps by auto



            show "visibleCalls S' s \<triangleq> vis"
              using a7 by auto


            from \<open>visibleCalls S' s \<triangleq> vis\<close>
            show "visibleCalls S2 s \<triangleq> vis"
              by (auto simp add: S2_simps)


            show " \<And>t. transactionOrigin S2 t \<triangleq> s = transactionOrigin S' t \<triangleq> s"
              using ih3 state_coupling_def by force

            have wf_S': "state_wellFormed S'"
              using S_wf noFails_tr state_wellFormed_combine steps by auto


            from a9
            show "consistentSnapshot S' snapshot"
            proof (rule chooseSnapshot_consistentSnapshot_preserve)
              show "\<And>x y z tx. \<lbrakk>(x, z) \<in> happensBefore S'; callOrigin S' x \<triangleq> tx; callOrigin S' y \<triangleq> tx; callOrigin S' z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y, z) \<in> happensBefore S'"
                by (simp add: wf_S' wf_happensBefore_txns_left)
              show "\<And>c tx. callOrigin S' c \<triangleq> tx \<Longrightarrow> transactionStatus S' tx \<triangleq> Committed"
                by (metis (full_types) \<open>\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted\<close> domD domIff transactionStatus.exhaust wf_S' wf_no_transactionStatus_origin_for_nothing)
              show "\<And>ca cb tx. \<lbrakk>callOrigin S' ca \<triangleq> tx; (cb, ca) \<in> happensBefore S'\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S' cb \<triangleq> tx"
                by (simp add: domD happensBefore_in_calls_left wellFormed_callOrigin_dom wf_S')
              show "trans (happensBefore S')"
                using happensBefore_transitive wf_S' by blast
              show "\<And>c tx. callOrigin S' c \<triangleq> tx \<Longrightarrow> \<exists>ci. calls S' c \<triangleq> ci"
                using wellFormed_callOrigin_dom wf_S' by fastforce
              show "consistentSnapshot S' vis"
                using a5 a7 wellFormed_state_consistent_snapshot wf_S' by blast
            qed
          qed

          then show "S ~~ (s, tr'@[(ABeginAtomic tx snapshot, True)]) \<leadsto>\<^sub>S*  S''"
            using ih1 steps_s_step by blast
        qed
      next
        fix p ar
        assume a0: "snd a = AInvoc p ar"

        with step
        have step': "S' ~~ (s, AInvoc p ar) \<leadsto> S''"
          by (metis True surjective_pairing) 

        from step_elim_AInvoc[OF step']  
        obtain initial impl 
          where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> initial), 
                    currentProc := currentProc S'(s \<mapsto> impl), 
                    visibleCalls := visibleCalls S'(s \<mapsto> {}), 
                    invocationOp := invocationOp S'(s \<mapsto> (p, ar))\<rparr>"
            and a2: "localState S' s = None"
            and a3: "procedure (prog S') p ar \<triangleq> (initial, impl)"
            and a4: "uniqueIdsInList ar \<subseteq> knownIds S'"
            and a5: "invocationOp S' s = None"
          by metis

        show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s True"
        proof (intro exI conjI)
          have "S2 ~~ (s, AInvoc p ar, True) \<leadsto>\<^sub>S S''"
          proof (rule step_s.intros)
            have "\<And>p. invocationOp S2 s \<noteq> Some p"
              using a5 ih3  by (metis option.distinct(1) state_coupling_def state_monotonicGrowth_invocationOp)  
            then show "invocationOp S2 s = None" by blast
            have [simp]: "prog S2 = prog S'"
              using ih3 state_coupling_def state_monotonicGrowth_prog by force 
            show "procedure (prog S2) p ar \<triangleq> (initial, impl)"
              using a3 state_coupling_def by auto
            show "uniqueIdsInList ar \<subseteq> knownIds S'"
              using a4 ih3 state_coupling_def by auto
            show "invariant_all S'"
              by (simp add: inv')
            show "invocationOp S' s = None" using a5  .
            show "S'' = S'\<lparr>localState := localState S'(s \<mapsto> initial), currentProc := currentProc S'(s \<mapsto> impl), visibleCalls := visibleCalls S'(s \<mapsto> {}), invocationOp := invocationOp S'(s \<mapsto> (p, ar))\<rparr>"
              using a1 by auto
            show "True = invariant_all S''"
              by (simp add: inv'')
            show "prog S' = prog S2"
              by simp
            show "state_wellFormed S'"
              using S_wf state_wellFormed_combine steps noFails by auto

            have "currentTransaction S' s = None"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wellFormed_invoc_notStarted(1))

            have "\<And>s. (s, AFail) \<notin> set tr"
              using steps_step.prems(4) by auto


            have "currentTransaction S' s = None" for s
              by (metis S_wf True \<open>state_wellFormed S'\<close> a5 at_most_one_current_tx last_snoc noContextSwitch packed step' steps' steps_step.prems(4) steps_step.prems(5) unchangedInTransaction(3) wellFormed_invoc_notStarted(1))

            from this
            show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
              using wellFormed_currentTransaction_back[OF steps \<open>\<And>s. (s, AFail) \<notin> set tr\<close> \<open>\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted\<close> \<open>state_wellFormed S\<close>]
              by auto


            have "\<And>tx. transactionOrigin S' tx \<noteq> Some s"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wf_no_invocation_no_origin)

            then show "\<And>tx. transactionOrigin S'' tx \<noteq> Some s"
              using step' by (auto simp add: step_simps)
          qed
          then show "S ~~ (s, tr'@[(AInvoc p ar, True)]) \<leadsto>\<^sub>S* S''"
            using ih1 steps_s_step by blast
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(AInvoc p ar, True)])"
            using ih2 by auto
          show "state_coupling S'' S'' s True"
            by (auto simp add: state_coupling_def)
        qed
      qed
    qed
  next
    case False
    then have different_session[simp]:  "fst a \<noteq> s" by simp

    text \<open>we are now in the case of doing steps in a different session.
   We show that all of these preserve the coupling. 
\<close>

    have "state_wellFormed S'"
      using S_wf noFails_tr state_wellFormed_combine steps by auto

    have wf_S2: "state_wellFormed S2"
      by (metis \<open>state_wellFormed S'\<close> ih3' state_coupling_def state_monotonicGrowth_wf1)


    text \<open>no matter what he had before, the coupling with "False" will hold:\<close>
    have old_coupling: "state_coupling S' S2 s False"
      using ih3' by (auto simp add: \<open>state_wellFormed S'\<close> state_coupling_def state_monotonicGrowth_refl  split: if_splits)


    have wf_S'': "state_wellFormed S''"
      using S_wf noFails state_wellFormed_combine steps' by blast


    from step
    have new_coupling: "state_coupling S'' S2 s False"
    proof (induct rule: step.cases) \<comment> \<open>prove this with a case distinction on the action\<close>
      case (local C s ls f ls')
      then show ?case 
        using old_coupling different_session wf_S'' by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])

    next
      case (newId C s ls f ls' uid)
      then show ?case 
        using old_coupling different_session wf_S'' by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
    next
      case (beginAtomic C s' ls f ls' t vis  vis')
      then show ?case using old_coupling different_session wf_S''
        apply (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
        using \<open>state_wellFormed S'\<close> wf_transaction_status_iff_origin by force
    next
      case (endAtomic C s ls f ls' t)
      then show ?case using old_coupling different_session wf_S'' 
        by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
    next
      case (dbop C s' ls f Op args ls' t c res vis)
      then show ?case using old_coupling different_session wf_S'' 
        by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
    next
      case (invocId C s procName args initialState impl)
      then show ?case using old_coupling different_session wf_S'' by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
    next
      case (return C s ls f res)
      then show ?case using old_coupling different_session wf_S'' by (auto simp add: state_coupling_def step_simps intro: state_monotonicGrowth_step[OF wf_S2, where i'="fst a" and a="snd a"])
    next
      case (fail C s ls)

      then show ?case
        using noFails by auto

    next
      case (invCheck C s res)
      then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
    qed


    then show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s False"
      using ih1 ih2 by blast


  qed
qed


lemma convert_to_single_session_trace_invFail_step:
fixes tr :: "'any::valueType trace"
  and s :: invocId      
  and S S' :: "('ls, 'any) state"
assumes step: "S ~~ (s,a) \<leadsto> S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "a \<noteq> AFail"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not>invariant_all S'"
    and coupling: "state_coupling S S2 s sameSession"
    and ctxtSwitchCases: "\<not>sameSession \<Longrightarrow> allowed_context_switch a" \<comment> \<open>(\<exists>tx txns. a = ABeginAtomic tx txns) \<or> (\<exists>p ar. a = AInvoc p ar)\<close>
    and noUncommitted:  "a \<noteq> AEndAtomic \<Longrightarrow>  \<forall>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    \<comment> \<open>we assume that we are not in a transaction (inside a transaction it is not necessary for invariants to hold)\<close>
    \<comment> \<open>and not_in_transaction: "currentTransaction S s = None "\<close>
shows "\<exists>tr' S2'. (S2 ~~ (s, tr') \<leadsto>\<^sub>S* S2') 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
using step proof (cases rule: step.cases)
  case (local ls f ls')
  text \<open>a local step does not change the invariant\<close>
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S'  = invContext S "
      using local by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed
  
  with inv and not_inv
  have False by simp
    
  then show ?thesis ..
next
  case (newId ls f ls' uid)
  text \<open>generating a new id does not change the invariant\<close>
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S' = invContext S"
      using newId by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed
  
  with inv and not_inv
  have False by simp
  
  then show ?thesis ..
next
  case (beginAtomic ls f ls' t)
  text \<open>starting a transaction does not change the invariant\<close>
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContext S' = invContext S " 
      using beginAtomic by (auto simp add: invContextH_def restrict_map_def   committedCallsH_update_uncommitted )

    show "prog S' = prog S"
      using local.step prog_inv by auto
  qed
  
  with inv and not_inv
  have False by simp
  
  then show ?thesis ..
next
  case (endAtomic ls f ls' t)
  text \<open>Ending a transaction includes an invariant-check in the single-invocId semantics, so we get a failing trace.\<close>
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Committed)\<rparr>"
  
  have [simp]: "sameSession"
    using allowed_context_switch_def[where action=a] ctxtSwitchCases local.endAtomic(1) by blast
  
  have "S2 ~~ (s,(AEndAtomic, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls" 
     and "currentProc S2 s \<triangleq> f"  
     and "f ls = EndAtomic ls'"
     and "currentTransaction S2 s \<triangleq> t"
      using coupling local.endAtomic state_coupling_def by force+
    show "S2' 
        = S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Committed)\<rparr>"
     using S2'_def by simp
     
    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add:  state_coupling_def local.endAtomic(6) split: if_splits)
      show "False" if "\<not> invariant_all S'" and "S2 = S" and "invariant_all S2'"
        using that apply (auto simp add: S2'_def \<open>S2 = S\<close>)
        using S2'_def local.endAtomic(2) that(2) that(3) by blast
    qed
    show "state_wellFormed S2'"
      by (metis (full_types) S2'_def S_wellformed \<open>sameSession\<close> action.distinct(49) coupling local.endAtomic(1) local.endAtomic(2) local.step snd_conv state_coupling_def state_wellFormed_combine_step)

  qed
  
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (dbop ls f Op args ls' t c res vis)
  text \<open>uncommitted operations do not affect the invariant\<close>
  
  have hb': "happensBefore S' = happensBefore S \<union> vis \<times> {c}"
    using dbop by auto
    
    
  
  have "invariant_all S'" if "invariant_all S"
    using S_wellformed local.dbop(1) local.dbop(6) noUncommitted wellFormed_currentTransactionUncommitted by blast

  then have False
    by (simp add: inv not_inv)
  then show ?thesis ..
next
  case (invocId procName args initialState impl)
  text \<open>invocations include an invariant-check\<close>
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> initialState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"
  
  have "S2 ~~ (s,(AInvoc procName args, False)) \<leadsto>\<^sub>S S'"
  proof (rule step_s.intros)
    
    have "localState S2 s = None"
      using invocId coupling by (auto simp add: state_coupling_def split: if_splits)
    have "\<And>x. invocationOp S2 s \<noteq> Some x"      
      using invocId coupling by (auto simp add: state_coupling_def state_monotonicGrowth_invocationOp split: if_splits)
    then show "invocationOp S2 s = None" by blast     
    show "procedure (prog S2) procName args \<triangleq> (initialState, impl)"
      using invocId coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "uniqueIdsInList args \<subseteq> knownIds S"
      using invocId coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invocationOp S s = None"
      using invocId coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invariant_all S"
      by (simp add: inv)
    show "S' = S\<lparr>localState := localState S(s \<mapsto> initialState), currentProc := currentProc S(s \<mapsto> impl), visibleCalls := visibleCalls S(s \<mapsto> {}), invocationOp := invocationOp S(s \<mapsto> (procName, args))\<rparr>"
      using local.invocId(2) by blast  
    show "False = invariant_all S'"
      by (simp add: not_inv)
    show "prog S = prog S2" 
      using coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "state_wellFormed S"
      by (simp add: S_wellformed)
    show " \<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      by (metis local.invocId(3) local.step noUncommitted option.distinct(1) preconditionI precondition_endAtomic)

    have "\<And>tx. transactionOrigin S tx \<noteq> Some s"
      by (simp add: S_wellformed local.invocId(6) wf_no_invocation_no_origin)
    then show "\<And>tx. transactionOrigin S' tx \<noteq> Some s"
      using step \<open>a = AInvoc procName args\<close> by (auto simp add: step_simps)

  qed    
    
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (return ls f res)
  text \<open>return contains an invariant check\<close>
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := (localState S2)(s := None), 
                              currentProc := (currentProc S2)(s := None), 
                              visibleCalls := (visibleCalls S2)(s := None), 
                              invocationRes := invocationRes S2(s \<mapsto> res), 
                              knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"
  
  have [simp]: sameSession
    using ctxtSwitchCases local.return(1) allowed_context_switch_def[where action = a] by blast                            
                              
  have "S2 ~~ (s,(AReturn res, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls"
     and "currentProc S2 s \<triangleq> f"
     and "f ls = Return res"
     and "currentTransaction S2 s = None"
      using return coupling by (auto simp add: state_coupling_def)
  
    show "S2' = S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S2(s \<mapsto> res), knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"
      using S2'_def by simp
  
    have not_in_transaction: "currentTransaction S s = None"
      using S_wellformed return wellFormed_invoc_notStarted(1) by auto  
      
    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add:  state_coupling_def not_in_transaction)
      fix vis
      assume a3: "S2 = S"
        and a0: "invariant_all S2'"
        and a1: "\<not> invariant_all S'"

      show False
        using S2'_def a0 a3 local.return(2) not_inv by blast
    qed
  qed
      
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (fail ls)
  text \<open>we assumed that there are no fails\<close>
  then show ?thesis
    using noFails by blast
next
  case (invCheck  res)
  then show ?thesis
    using inv not_inv by blast \<comment> \<open>same state\<close>
qed

lemma uncommitted_tx_is_current_somewhere:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and tx_uncommitted: "transactionStatus S' tx \<triangleq> Uncommitted"
  shows "\<exists>invoc. currentTransaction S' invoc \<triangleq> tx" 
using steps noFails tx_uncommitted proof (induct rule: steps_induct)
  case initial
  then show ?case
    using noUncommittedTx by blast 
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: step.simps split: if_splits, force+)
qed

lemma no_current_transaction_when_invariant_fails:
  assumes "S ~~ a \<leadsto> S_fail"
    and "\<not> invariant_all S_fail"
    and "state_wellFormed S"
    and " invariant_all S"
    and wf: "state_wellFormed S"
    and noEndAtomic: "snd a \<noteq> AEndAtomic"
  shows "currentTransaction S (fst a) = None"
proof (rule ccontr)
  assume " currentTransaction S (fst a) \<noteq> None"
  from this obtain tx where ctx: "currentTransaction S (fst a) \<triangleq> tx"
    by (metis not_None_eq)

  have uncommitted: "transactionStatus S tx \<triangleq> Uncommitted"
    by (metis ctx local.wf wellFormed_currentTransactionUncommitted)


  have snapshotSame: "consistentSnapshot S_fail vis \<longleftrightarrow> consistentSnapshot S vis" for vis
    using \<open>S ~~ a \<leadsto> S_fail\<close>
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  next
    case (newId s ls f ls' uid)
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  next
    case (beginAtomic s ls f ls' t vis snapshot)
    then show ?thesis
      by (metis \<open>currentTransaction S (fst a) \<noteq> None\<close> fst_conv) 

  next
    case (endAtomic s ls f ls' t)
    then show ?thesis
      by (metis noEndAtomic sndI) 
  next
    case (dbop s ls f Op args ls' t c res vis')
    show ?thesis 
    proof (auto simp add: consistentSnapshotH_def dbop)

      show "\<exists>y. calls S x \<triangleq> y" 
        if a1: "vis \<subseteq> insert c (dom (calls S))" 
          and a2: "causallyConsistent (happensBefore S \<union> vis' \<times> {c}) vis" 
          and a3: "transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis"
          and a4: "x \<in> vis" for x
      proof (cases "x=c")
        case True
        then have "c \<in> vis"
          by (metis a4)
        with transactionConsistent_Committed[OF a3] have False
          apply auto
          by (metis local.dbop(6) local.wf option.inject transactionStatus.distinct(1) wellFormed_currentTransactionUncommitted)
        then show ?thesis by simp
      next case False
        then show ?thesis
          by (metis a1 a4 domD insertE set_rev_mp)
      qed

      show "\<lbrakk>vis \<subseteq> insert c (dom (calls S)); causallyConsistent (happensBefore S \<union> vis' \<times> {c}) vis; transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis\<rbrakk>
    \<Longrightarrow> causallyConsistent (happensBefore S) vis"
        by (auto simp add: causallyConsistent_def)

      show " \<lbrakk>vis \<subseteq> dom (calls S); causallyConsistent (happensBefore S) vis; transactionConsistent (callOrigin S) (transactionStatus S) vis\<rbrakk>
    \<Longrightarrow> causallyConsistent (happensBefore S \<union> vis' \<times> {c}) vis"
        apply (auto simp add: causallyConsistent_def)
        by (metis domIff local.dbop(7) set_mp)


      show "\<lbrakk>vis \<subseteq> insert c (dom (calls S)); causallyConsistent (happensBefore S \<union> vis' \<times> {c}) vis; transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis\<rbrakk>
    \<Longrightarrow> transactionConsistent (callOrigin S) (transactionStatus S) vis"
        apply (subst transactionConsistent_def)
        apply (auto simp add: )
         apply (metis (mono_tags, lifting) domI domIff local.dbop(7) local.wf map_upd_Some_unfold transactionConsistent_Committed wellFormed_callOrigin_dom2)
        by (metis \<open>\<And>x. \<lbrakk>vis \<subseteq> insert c (dom (calls S)); causallyConsistent (happensBefore S \<union> vis' \<times> {c}) vis; transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis; x \<in> vis\<rbrakk> \<Longrightarrow> \<exists>y. calls S x \<triangleq> y\<close> fun_upd_same fun_upd_triv fun_upd_twist local.dbop(7) local.wf option.distinct(1) transactionConsistent_all_from_same wellFormed_callOrigin_dom3)

      show " \<lbrakk>vis \<subseteq> dom (calls S); causallyConsistent (happensBefore S) vis; transactionConsistent (callOrigin S) (transactionStatus S) vis\<rbrakk>
    \<Longrightarrow> transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis"
        apply (subst transactionConsistent_def)
        apply (auto simp add: )
            apply (metis domIff in_mono local.dbop(7))
           apply (metis transactionConsistent_Committed)
          apply (metis domIff local.dbop(7) subsetD)
         apply (metis ctx fst_conv local.dbop(1) local.dbop(6) option.inject transactionConsistent_Committed transactionStatus.distinct(1) uncommitted)
        by (metis transactionConsistent_all_from_same)

    qed

  next
    case (invocId s procName args initialState impl)
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  next
    case (return s ls f res)
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  next
    case (fail s ls)
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  next
    case (invCheck res s)
    then show ?thesis by (auto simp add: consistentSnapshotH_def)
  qed

  have committedCallsH_same: "committedCallsH (callOrigin S_fail) (transactionStatus S_fail) = committedCallsH (callOrigin S) (transactionStatus S)"
    using \<open>S ~~ a \<leadsto> S_fail\<close>
    using \<open>currentTransaction S (fst a) \<noteq> None\<close> noEndAtomic apply (auto simp add: step.simps committedCallsH_def )
     apply (auto simp add: isCommittedH_def split: if_splits)
    using wellFormed_currentTransactionUncommitted[OF wf] apply auto
    by (metis local.wf option.distinct(1) wellFormed_callOrigin_dom2)


  have committedCallsExist: "calls S c = None \<Longrightarrow> c \<notin> committedCalls S" for c
    by (metis local.wf wellFormed_committedCallsExist)


  have "invContext S_fail = invContext S" 
    apply (auto simp add: invContextH_def committedCallsH_same)
    using \<open>S ~~ a \<leadsto> S_fail\<close> noEndAtomic \<open>currentTransaction S (fst a) \<noteq> None\<close>
    by (auto simp add: step.simps restrict_map_def restrict_relation_def committedCallsExist inTransaction_localState[OF wf])

  with   \<open>\<not> invariant_all S_fail\<close> \<open>invariant_all S\<close>
  show False
    by (metis (no_types, lifting)  prog_inv[OF \<open>S ~~ a \<leadsto> S_fail\<close>] )
qed


lemma convert_to_single_session_trace_invFail:
fixes tr :: "'any::valueType trace"
  and S S' :: "('ls, 'any) state"
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommittedTx: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and noContextSwitches: "noContextSwitchesInTransaction tr"
    \<comment> \<open>invariant holds in the initial state\<close>
    and inv: "invariant_all S"
    \<comment> \<open>invariant no longer holds\<close>
    and not_inv: "\<not> invariant_all S'"
shows "\<exists>tr' S2 s. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
proof -
  
  have not_inv_ex: "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"
    by (rule exI[where x="tr"], rule exI[where x="S'"], auto  simp add: not_inv steps isPrefix_refl)

    

  text \<open>There must be a place where the invariant fails for the first time:\<close>
  obtain tr1 a tr2 S1 S_fail
    where tr_split: "tr = tr1@a#tr2"
      and steps1: "S ~~ tr1 \<leadsto>* S1"
      and stepA: "S1 ~~ a \<leadsto> S_fail"
      and first_not_inv: "\<not>invariant_all S_fail"
      and inv_before: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr1; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  proof (atomize_elim)  
    show "\<exists>tr1 a tr2 S1 S_fail. tr = tr1 @ a # tr2 \<and> (S ~~ tr1 \<leadsto>* S1) \<and> (S1 ~~ a \<leadsto> S_fail) \<and> \<not> invariant_all S_fail \<and> (\<forall>S' tr'. isPrefix tr' tr1 \<longrightarrow> (S ~~ tr' \<leadsto>* S') \<longrightarrow> invariant_all S')"
    using steps inv not_inv_ex proof (induct rule: steps_induct)
      case initial
      then show ?case
        by (simp add: isPrefix_empty steps_empty)
    next
      case (step S' tr a S'')
      then show ?case 
      proof (cases "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail")
        case True
        then show ?thesis
          using inv step.IH by force 
      next
        case False
        
        then have invariant_in_tr: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
          by blast
        
        from \<open>\<exists>tr_pre S_fail. isPrefix tr_pre (tr @ [a]) \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail\<close>
        obtain tr_pre S_fail 
          where "isPrefix tr_pre (tr @ [a])" 
          and "S ~~ tr_pre \<leadsto>* S_fail" 
          and "\<not> invariant_all S_fail"
          by blast
        
        have "tr_pre = tr @ [a]"
        proof (rule ccontr)
          assume "tr_pre \<noteq> tr @ [a]"
          with \<open>isPrefix tr_pre (tr @ [a])\<close>
          have "isPrefix tr_pre tr"
            by (metis (no_types, lifting) append_eq_append_conv_if append_take_drop_id isPrefix_def length_append_singleton not_less_eq_eq take_all)
          
          with invariant_in_tr
          have "invariant_all S_fail"
            using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> by blast
          with \<open>\<not> invariant_all S_fail\<close>
          show False ..
        qed
        
        then have "S_fail = S''"
          using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> step.step step.steps steps_step traceDeterministic by blast
          
        with \<open>\<not> invariant_all S_fail\<close>
        have "\<not>invariant_all S''"
          by auto
          
        
        show ?thesis 
         using step invariant_in_tr \<open>\<not>invariant_all S''\<close> by blast 
      qed
    qed  
  qed
  
  obtain as aa where a_def: "a = (as,aa)"
    by force


  have noFails_tr1: "\<And>i. (i, AFail) \<notin> set tr1"
    using noFails tr_split by auto

  have noFails_tr2: "\<And>i. (i, AFail) \<notin> set tr2"
    using noFails tr_split by auto


  thm convert_to_single_session_trace
  obtain tr1' S1' 
    where tr1'_steps: "S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'"
      and tr1'_ok: "\<forall>a. (a, False)\<notin>set tr1'"
      and tr1'_coupling: "state_coupling S1 S1' as (tr1 = [] \<or> fst (last tr1) = as)"
  proof (atomize_elim, rule convert_to_single_session_trace)
    show "S ~~ tr1 \<leadsto>* S1" using steps1 .
    show "state_wellFormed S" using S_wellformed .
    show "packed_trace tr1"
      using isPrefix_appendI packed prefixes_are_packed tr_split by blast 
    show "\<And>s. (s, AFail) \<notin> set tr1"
      using noFails tr_split by auto
    show "\<And>S' tr1'. \<lbrakk>isPrefix tr1' tr1; S ~~ tr1' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using inv_before by auto
    show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      by (simp add: noUncommittedTx)
    show "noContextSwitchesInTransaction tr1"
      using isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split by blast
  qed


  have tr1_packed: "packed_trace (tr1@[a])"     
  using packed proof (rule prefixes_are_packed)
    have "isPrefix (tr1 @ [a]) ((tr1 @ [a]) @ tr2)" by (rule isPrefix_appendI)
    then show "isPrefix (tr1 @ [a]) tr" using tr_split by auto
  qed  
    
  
  obtain tr_a S_fail'
    where steps_tr_a: "S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'"
      and tr_a_fails: "\<exists>a. (a, False)\<in>set tr_a"
  proof (atomize_elim, rule convert_to_single_session_trace_invFail_step)
    show "S1 ~~ (as,aa) \<leadsto> S_fail"
      using a_def stepA by blast
    show "state_wellFormed S1"
      using S_wellformed state_wellFormed_combine steps1 noFails_tr1 by blast
    show "aa \<noteq> AFail"
      using a_def noFails tr_split by auto
    show "invariant_all S1"
      using inv_before isPrefix_refl steps1 by blast
    show "\<not> invariant_all S_fail"
      by (simp add: first_not_inv)
    show "state_coupling S1 S1' as (tr1 = [] \<or> fst (last tr1) = as)"  
      using tr1'_coupling .



    show "\<forall>tx. transactionStatus S1 tx \<noteq> Some Uncommitted " if "aa \<noteq> AEndAtomic"
    proof -
      have  noFails_tr1: "\<And>s. (s, AFail) \<notin> set tr1"
        using noFails tr_split by auto

      have current_tx:  "\<forall>i. currentTransaction S1 i \<noteq> None \<longrightarrow> i = fst (last tr1)"
      proof (rule at_most_one_current_tx[OF \<open>S ~~ tr1 \<leadsto>* S1\<close>])
        show "noContextSwitchesInTransaction tr1"
          using isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split by blast

        show "packed_trace tr1"
          using packed_trace_prefix tr1_packed by blast

        show "state_wellFormed S"
          by (simp add: S_wellformed)

        show "\<And>s. (s, AFail) \<notin> set tr1" using noFails_tr1 .

        show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
          by (simp add: noUncommittedTx)
      qed



      have noCurrentTx_a: "currentTransaction S1 (fst a) = None"
      proof (rule no_current_transaction_when_invariant_fails[OF \<open>S1 ~~ a \<leadsto> S_fail\<close> \<open>\<not> invariant_all S_fail\<close>])
        show "state_wellFormed S1"
          by (simp add: \<open>state_wellFormed S1\<close>) 
        show "invariant_all S1"
          by (simp add: \<open>invariant_all S1\<close>)
        show "state_wellFormed S1"
          by (metis \<open>state_wellFormed S1\<close>)
        show "snd a \<noteq> AEndAtomic"
          by (metis a_def sndI that) 
      qed

      have noCurrentTx: "currentTransaction S1 (fst (last tr1)) = None"
      proof (cases "tr1")
        case Nil
        then have "S1 = S"
          using steps1 steps_refl traceDeterministic by blast
        then show ?thesis 
          by (meson S_wellformed noUncommittedTx not_Some_eq wellFormed_currentTransactionUncommitted)
      next
        case (Cons tr1_first tr1_rest)
        then have tr1_len: "0 < length tr1"
          by simp

        show ?thesis 
        proof (cases "fst (last tr1) = fst a")
          case True
          then show ?thesis
            by (simp add: noCurrentTx_a) 
        next
          case False
          show ?thesis
          proof (rule ccontr)
            assume a0: "currentTransaction S1 (fst (last tr1)) \<noteq> None"

            define invoc where "invoc \<equiv> fst (last tr1)"

            from a0 obtain tx where "currentTransaction S1 invoc \<triangleq> tx"
              by (metis not_Some_eq invoc_def)


            have "\<exists>ib txns. tr1 ! ib = (invoc, ABeginAtomic tx txns) \<and> ib < length tr1 \<and> (\<forall>j. ib < j \<and> j < length tr1 \<longrightarrow> tr1 ! j \<noteq> (invoc, AEndAtomic))"
            proof (rule currentTransaction_exists_beginAtomic[OF \<open>S ~~ tr1 \<leadsto>* S1\<close> \<open>currentTransaction S1 invoc \<triangleq> tx\<close>])
              show "currentTransaction S invoc = None"
                by (metis S_wellformed noUncommittedTx option.exhaust wellFormed_currentTransaction_unique_h(2))
              show "state_wellFormed S"
                by (metis S_wellformed)
              show "\<And>i. (i, AFail) \<notin> set tr1"
                by (simp add: noFails_tr1) 
            qed
            from this obtain ib txns 
              where ib1: "tr1 ! ib = (invoc, ABeginAtomic tx txns)"
                and ib2: "ib < length tr1"
                and ib3: "\<forall>j. ib < j \<and> j < length tr1 \<longrightarrow> tr1 ! j \<noteq> (invoc, AEndAtomic)"
              by blast


            have steps_fail: "S ~~ tr1@[a] \<leadsto>* S_fail"
              using stepA steps1 steps_step by blast

            have "allowed_context_switch (snd ((tr1@[a]) ! length tr1))"
            proof (rule use_packed_trace)  
              show " packed_trace (tr1 @ [a])"
                by (simp add: tr1_packed)
              show "0 < length tr1"
                using tr1_len .
              show "length tr1 < length (tr1 @ [a])"
                by simp
              show "fst ((tr1 @ [a]) ! (length tr1 - 1)) \<noteq> fst ((tr1 @ [a]) ! length tr1)"
                by (metis False One_nat_def diff_Suc_less last_conv_nth list.simps(3) local.Cons nth_append nth_append_length tr1_len)
            qed

            find_theorems "allowed_context_switch" packed_trace

            moreover have "\<not> allowed_context_switch (snd ((tr1@[a]) ! length tr1))"
            proof (rule use_noContextSwitchesInTransaction)
              show "noContextSwitchesInTransaction (tr1 @ [a])"
                by (metis append.assoc append_Cons append_Nil isPrefix_appendI noContextSwitches prefixes_noContextSwitchesInTransaction tr_split)
              show "(tr1 @ [a]) ! ib = (invoc, ABeginAtomic tx txns)"
                by (metis ib1 ib2 nth_append)
              show " ib < length (tr1@[a])"
                using ib2  by simp
              show "length (tr1 @ [a]) \<le> length (tr1 @ [a])" 
                by simp
              show "\<forall>j. ib < j \<and> j < length (tr1 @ [a]) \<longrightarrow> (tr1 @ [a]) ! j \<noteq> (invoc, AEndAtomic)"
                apply (auto simp add: nth_append ib3)
                by (metis False fst_conv invoc_def)
              show "ib < length tr1" using ib2 .
              show "length tr1 < length (tr1 @ [a])"
                by simp
            qed
            ultimately show False by simp
          qed
        qed
      qed


      have "transactionStatus S1 tx \<noteq> Some Uncommitted" for tx
      proof 
        assume a: "transactionStatus S1 tx \<triangleq> Uncommitted"

        obtain invoc where "currentTransaction S1 invoc = Some tx"
          using uncommitted_tx_is_current_somewhere[OF \<open>S ~~ tr1 \<leadsto>* S1\<close> \<open>state_wellFormed S\<close> noFails_tr1 noUncommittedTx a] by blast

        then have "invoc = fst (last tr1)"
          by (simp add: current_tx)

        with \<open>currentTransaction S1 invoc = Some tx\<close> show False
          by (simp add: noCurrentTx)
      qed
      then show "\<forall>tx. transactionStatus S1 tx \<noteq> Some Uncommitted"
        by simp
    qed



       
    assume "\<not> (tr1 = [] \<or> fst (last tr1) = as)"
    then have "tr1 \<noteq> []" and "fst (last tr1) \<noteq> as"
      by auto
    show "allowed_context_switch aa"  
    using tr1_packed proof (rule context_switches_in_packed)
      show "tr1 @ [a] = butlast tr1 @ [(fst (last tr1), snd (last tr1)), (as, aa)] @ []"
        by (simp add: \<open>tr1 \<noteq> []\<close> a_def)
      show "fst (last tr1) \<noteq> as"
        by (simp add: \<open>fst (last tr1) \<noteq> as\<close>)
    qed    
  qed    
    
  show ?thesis
  proof (rule exI[where x="tr1'@tr_a"], rule exI[where x="S_fail'"], rule exI[where x="as"], intro conjI)
    from \<open>S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'\<close> 
     and \<open>S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'\<close>
    show " S ~~ (as, tr1' @ tr_a) \<leadsto>\<^sub>S* S_fail'"
      by (rule steps_s_append)  
    show "\<exists>a. (a, False) \<in> set (tr1' @ tr_a)"
      using tr_a_fails by auto
  qed
qed


text \<open>if there is an failing invariant check in the trace, then there is a prefix of the trace leading to a
  state that does not satisfy the invariant\<close>
lemma invCheck_to_failing_state:
assumes steps: "S ~~ trace \<leadsto>* S'"
    and inv_fail: "(s, AInvcheck False) \<in> set trace"
    and state_wf: "state_wellFormed S"
    and noFail: "\<And>i. (i, AFail) \<notin> set trace"
shows "\<exists>tr' S_fail. isPrefix tr' trace \<and> (S ~~ tr' \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail" 
using steps inv_fail noFail proof (induct rule: steps_induct)
  case initial
  then show ?case
    by auto 
next
  case (step S' tr a S'')

  have noFail_tr: "\<And>i. (i, AFail) \<notin> set tr"
    using step by auto


  show ?case 
  proof (cases "(s, AInvcheck False) \<in> set tr")
    case True
    with step.IH
    obtain tr' S_fail 
      where "isPrefix tr' tr" 
        and"S ~~ tr' \<leadsto>* S_fail" 
        and "\<not> invariant_all S_fail"
      using noFail_tr by blast
      
    then show ?thesis
      using isPrefix_append by blast 
      
  next
    case False
    with \<open>(s, AInvcheck False) \<in> set (tr @ [a])\<close>
    have "a = (s, AInvcheck False)" by auto
    
    show ?thesis
    proof (intro exI conjI)
      show "isPrefix (tr @ [a]) (tr @ [a])"
        by (simp add: isPrefix_refl)
      show "S ~~ tr @ [a] \<leadsto>* S''"
        using step.step step.steps steps_step by fastforce   
      
      from \<open>S' ~~ a \<leadsto> S''\<close>
      have "S' ~~ (s, AInvcheck False) \<leadsto> S''" using \<open>a = (s, AInvcheck False)\<close> by simp
      then have  [simp]: "S'' = S'" 
       and invFail: "\<not> invariant (prog S') (invContext S')"
        by (auto simp add: step_simps)
        
        
      show "\<not> invariant_all S''"
        using invFail by auto  
    qed
  qed
qed

lemma GreatestI: 
"\<lbrakk>P k; \<forall>y. P y \<longrightarrow> y < b\<rbrakk> \<Longrightarrow> P (GREATEST x. P x)"
for k :: nat
  by (metis GreatestI_nat le_eq_less_or_eq)
           
lemma GreatestI2:
assumes example: "Q k"
   and impl: "\<And>i. Q i \<Longrightarrow> P i"
   and bound: "\<And>i. Q i \<Longrightarrow> i < bound"
 shows "P (GREATEST x::nat. Q x)"
  using assms GreatestI by blast 

lemma prefix_induct[case_names Nil snoc[IH]]:
assumes empty: "P []"
    and step: "\<And>ys a. \<lbrakk>\<And>xs. isPrefix xs ys \<Longrightarrow> P xs\<rbrakk> \<Longrightarrow> P (ys@[a])"
shows "P xs"
proof -
  have "\<forall>xs'. isPrefix xs' xs \<longrightarrow> P xs'"
  using assms proof (induct rule: rev_induct)
    case Nil
    then show ?case
      by (simp add: isPrefix_empty)
  next
    case (snoc x ys)
    find_theorems name: local.snoc
    show ?case
    proof auto
      fix xs' 
      assume a1: "isPrefix xs' (ys @ [x])"
      show "P xs'"
      proof (cases "isPrefix xs' ys")
        case True
        then show ?thesis
          using local.empty local.step snoc.hyps by blast 
      next
        case False
        with a1
        have "xs' = ys@[x]"
          apply (auto simp add: isPrefix_def)
          by (metis append_self_conv butlast.simps(2) diff_is_0_eq nat_le_linear not_le take_all take_butlast take_eq_Nil)
        
        have " P (ys@[x])"
        proof (rule local.snoc(3))
          show "\<And>xs. isPrefix xs ys \<Longrightarrow> P xs"
            using local.empty local.step snoc.hyps by blast
        qed    
        then show "P xs'" using \<open>xs' = ys@[x]\<close> by simp
      qed
    qed
  qed
  then show "P xs"
    using isPrefix_refl by blast
qed  

lemma smallestPrefix_exists:
fixes tr :: "'a list"
  and  x :: 'b
assumes example: "P tr x"
shows "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not>isPrefix tr' tr)"
using example proof (induct tr arbitrary: x rule: prefix_induct)
  case Nil
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="x"], auto simp add: isPrefix_empty)
    show "P [] x" using Nil .
  qed
next
  case (snoc xs a)
  show ?case 
  proof (cases "\<exists>tr' x'. P tr' x' \<and> isPrefix tr' xs")
  case True
    from this obtain tr' x'
      where "isPrefix tr' xs" and "P tr' x'"
      by blast
    then show "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
      by (rule snoc.IH)
  next 
    case False
    then have noPrefix: "\<not>isPrefix tr' xs" if "P tr' x'" for tr' x'
      using that by blast
      
    show " \<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
    proof (rule exI[where x="xs@[a]"], rule exI[where x=x], intro conjI allI impI; (elim conjE)?)
      show "P (xs @ [a]) x"
        using snoc.prems .
      fix tr' x'
      assume "P tr' x'"
      then have "\<not>isPrefix tr' xs"
        using False by blast
      fix tr' x'
      assume a0: "P tr' x'"
         and a1: "tr' \<noteq> xs @ [a]"
      
      show "\<not> isPrefix tr' (xs @ [a])"
        by (metis False a0 a1 butlast_snoc isPrefix_def not_le take_all take_butlast)
    qed    
  qed 
qed
    

text \<open>
When a program is correct in the single invocId semantics, 
it is also correct when executed in the concurrent interleaving semantics.
\<close>
theorem show_correctness_via_single_session:
assumes works_in_single_session: "programCorrect_s program"
    and inv_init: "invariant_all (initialState program)"
shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving'')
(* \<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace\<rbrakk> \<Longrightarrow> traceCorrect trace *)
  thm show_programCorrect_noTransactionInterleaving''
  text \<open>Assume we have a trace and a final state S\<close>
  fix trace S
  text \<open>Such that executing the trace finishes in state S.\<close>
  assume steps: "initialState program ~~ trace \<leadsto>* S"
  
  text \<open>We can assume the trace is packed.\<close>
  assume packed: "packed_trace trace"
  
  text \<open>We may also assume that there are no failures\<close>
  assume noFail: "\<And>s. (s, AFail) \<notin> set trace"

  assume "allTransactionsEnd trace"

  assume noInvchecksInTxns: "no_invariant_checks_in_transaction trace"

  text \<open>We show that the trace must be correct (proof by contradiction).\<close>
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"
    
    text \<open>If the trace is incorrect, there must be a failing invariant check in the trace:\<close>
    from this obtain s where "(s, AInvcheck False) \<in> set trace"
       using steps by (auto simp add: traceCorrect_def)
    
    obtain tr' S_fail
       where "isPrefix tr' trace"
         and "initialState program ~~ tr' \<leadsto>* S_fail"
         and "\<not> invariant_all S_fail"
      using \<open>(s, AInvcheck False) \<in> set trace\<close> invCheck_to_failing_state state_wellFormed_init steps noFail by blast 
    
    text \<open>No take the first state where the invariant fails\<close>
    from this
    obtain tr'_min S_fail_min
       where tr'_min_prefix: "isPrefix tr'_min trace"
         and S_fail_min_steps:"initialState program ~~ tr'_min \<leadsto>* S_fail_min"
         and S_fail_min_fail: "\<not> invariant_all S_fail_min"    
         and S_fail_min_min: "\<And>tr' S_fail. \<lbrakk>isPrefix tr' trace; initialState program ~~ tr' \<leadsto>* S_fail; \<not> invariant_all S_fail; tr' \<noteq> tr'_min\<rbrakk> \<Longrightarrow> \<not>isPrefix tr' tr'_min"
      using smallestPrefix_exists[where P="\<lambda>tr x. isPrefix tr trace \<and> (initialState program ~~ tr \<leadsto>* x) \<and> \<not> invariant_all x"]
      by metis
    
    text \<open>Next get the invocId start before the failure\<close>  
      
    find_theorems "(\<exists>x y. ?P x y) \<longleftrightarrow> (\<exists>y x. ?P x y)"
    
      
    obtain tr'_s S_fail_s s'
      where "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        and "\<exists>a. (a, False) \<in> set tr'_s"
    proof (atomize_elim)
      have "\<exists>tr'_s S_fail_s s'. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
      proof (rule convert_to_single_session_trace_invFail[OF \<open>initialState program ~~ tr' \<leadsto>* S_fail\<close>])
        show "state_wellFormed (initialState program)"
          by (simp add: state_wellFormed_init)
        show "packed_trace tr'"
          using \<open>isPrefix tr' trace\<close> packed prefixes_are_packed by blast
        show "\<And>s'. (s', AFail) \<notin> set tr'"
          using \<open>isPrefix tr' trace\<close> noFail apply (auto simp add: isPrefix_def) \<comment> \<open>IMPROVE extract lemma for isPrefix with \<in> or \<subseteq>\<close>
          by (metis in_set_takeD)
        show "invariant_all (initialState program)"
          using inv_init .
        show "\<not> invariant_all S_fail"
          by (simp add: \<open>\<not> invariant_all S_fail\<close>)
        show "\<And>tx. transactionStatus (initialState program) tx \<noteq> Some Uncommitted"
          by (simp add: initialState_def)
        show " noContextSwitchesInTransaction tr'"
          by (metis \<open>allTransactionsEnd trace\<close> \<open>isPrefix tr' trace\<close> \<open>state_wellFormed (initialState program)\<close> noContextSwitchesInTransaction_when_packed_and_all_end noFail packed prefixes_noContextSwitchesInTransaction steps)

      qed
      then show "\<exists>s' tr'_s S_fail_s. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
        by blast
    qed
    
    have not_correct: "\<not>traceCorrect_s program tr'_s"
      by (simp add: \<open>\<exists>a. (a, False) \<in> set tr'_s\<close> traceCorrect_s_def)
      
 
      
    (*
    from works_in_single_session
    have use_single_session: "traceCorrect_s program trace" if "invariant program (invContext init s)" and "prog init = program" and "init ~~ (s, trace) \<leadsto>\<^sub>S* S" for init trace s S
      using that by (auto simp add: programCorrect_s_def)
    *)
    from works_in_single_session
    have use_single_session: "traceCorrect_s program trace" if "initialState program ~~ (s, trace) \<leadsto>\<^sub>S* S" for  trace s S
      using that by (auto simp add: programCorrect_s_def)  
      
    have correct: "traceCorrect_s program tr'_s" 
    proof (rule use_single_session)
      show "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        using \<open>initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s\<close> .
    qed    
    
    with not_correct
    show False ..
  qed
qed  
   


end
