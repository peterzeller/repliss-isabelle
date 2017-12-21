theory approach
  imports Main commutativity
    repliss_sem_single_invocation
begin

find_consts name: fold
section {* Proof approach *}

text {* This theory includes the soundness proof of our proof approach. *}

(*
TODO:

1. single invocation semantics

2. show that multi-invocation trace with fixed invocation can be reduced to multiple single invocation traces by chopping

3. other things

*)


declare length_dropWhile_le[simp]  

(*
split a trace into maximal chunks of actions in the same session.
Each chunk can be used in single-invocation semantics.

Remember that a trace is just a (invocation\<times>action) list
*)
fun split_trace :: "'any trace \<Rightarrow> (invocation \<times> ('any action list)) list" where
  "split_trace [] = []"
| "split_trace ((s,a)#rest) = (
   let same = map snd (takeWhile (\<lambda>x. fst x = s) rest);
       rest' = dropWhile (\<lambda>x. fst x = s) rest
   in (s, a#same) # split_trace rest'
)"





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



text {* Coupling invariant: S is state from distributed execution and S is state from single-invocation execution.  *}
definition state_coupling :: "('ls,'any) state \<Rightarrow> ('ls,'any) state \<Rightarrow> invocation \<Rightarrow> bool \<Rightarrow> bool" where
  "state_coupling S S' i sameSession \<equiv> 
   if sameSession then
      (* did a step in the same invocation *)
      if currentTransaction S i = None 
      then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S i orElse {} \<and> S' = S\<lparr>visibleCalls := (visibleCalls S)(i := vis') \<rparr> (* TODO maybe can get equality here*)
      else S' = S
   else 
      (* did step in a different invocation *)
        state_monotonicGrowth S' S
      (* local state on s unchanged *)
      \<and> localState S i = localState S' i
      \<and> currentProc S i = currentProc S' i
      \<and> currentTransaction S i = currentTransaction S' i
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
  invocationOp :: "invocation \<rightharpoonup> (procedureName \<times> 'any list)"
  invocationRes :: "invocation \<rightharpoonup> 'any"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

record state = distributed_state + 
  localState :: "invocation \<rightharpoonup> localState"
  currentProc :: "invocation \<rightharpoonup> procedureImpl"
  visibleCalls :: "invocation \<rightharpoonup> callId set"
  currentTransaction :: "invocation \<rightharpoonup> txid"
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
    by  (auto simp add: invariant_all_def consistentSnapshot_def)
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
    and status: "transactionStatus S' tx \<triangleq> Uncommited"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    (*    and tr_len: "length tr > 0"*)
    (*    and allEnd: "allTransactionsEnd tr"*)
    and noSwitch: "noContextSwitchesInTransaction tr"
    and initial: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
  shows "(currentTransaction S' (fst (last tr)) \<triangleq> tx) 
      \<and> (\<exists>i txns. i<length tr \<and> tr!i = (fst (last tr), ABeginAtomic tx txns)
           \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (fst (last tr), AEndAtomic)))" 
  using steps packed status noFails noSwitch proof (induct arbitrary: tx  rule: steps_induct)
  case initial
  with `transactionStatus S tx \<noteq> Some Uncommited` show ?case by blast
next
  case (step S' tr a S'' tx)

  from `noContextSwitchesInTransaction (tr @ [a])`
  have noContextSwitch: "noContextSwitchesInTransaction tr"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast

  { 
    assume "transactionStatus S' tx \<triangleq> Uncommited"
    with ` S ~~ tr \<leadsto>* S'`
    have IH: "currentTransaction S' (fst (last tr)) \<triangleq> tx 
          \<and> (\<exists>i txns. i<length tr \<and> tr!i = (fst (last tr), ABeginAtomic tx txns)
                   \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (fst (last tr), AEndAtomic)))"
      using isPrefix_appendI prefixes_are_packed step.IH `\<And>s. (s, AFail) \<notin> set (tr @ [a])` `packed_trace (tr @ [a])` noContextSwitch
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

    hence "(tr @ [a]) ! i = (fst (last tr), ABeginAtomic tx txns)"
      by (simp add: nth_append_first)

    have "a \<noteq> (fst (last tr), AEndAtomic)" 
      using `S' ~~ a \<leadsto> S''` `transactionStatus S'' tx \<triangleq> Uncommited`
      by (auto simp add: step.simps IH1 split: if_splits )


    from `noContextSwitchesInTransaction (tr @ [a])` `(tr @ [a]) ! i = (fst (last tr), ABeginAtomic tx txns)`
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
    hence "\<not>allowed_context_switch action"
      by simp 

    hence i'_simps: "i' = fst (last tr)"
      using use_packed_trace[OF `packed_trace (tr@[a])`, where i="length tr"]
      apply (auto simp add: nth_append)
      by (metis i1 One_nat_def gr_implies_not_zero last_conv_nth length_0_conv)




    from `S' ~~ a \<leadsto> S''` IH1
    have "currentTransaction S'' (fst (last (tr@[a]))) \<triangleq> tx"
      using \<open>a \<noteq> (fst (last tr), AEndAtomic)\<close>  `\<And>s. (s, AFail) \<notin> set (tr @ [a])` by (auto simp add: step.simps  i'_simps)

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
    assume "transactionStatus S' tx \<noteq> Some Uncommited"
    hence  "currentTransaction S'' (fst (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (fst (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (fst (last (tr @ [a])), AEndAtomic)))"
      using `S' ~~ a \<leadsto> S''` ` transactionStatus S'' tx \<triangleq> Uncommited`
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
  shows "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
  using steps inTx proof (induct arbitrary: tx rule: steps_induct)
  case initial
  then show ?case
    by (simp add: noTx)

next
  case (step S' tr a S'')

  from ` S' ~~ a \<leadsto> S''`
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ls')
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  local)
    qed

    then show ?thesis
      using `a = (s, ALocal)` by (auto simp add: nth_append)

  next
    case (newId s ls f ls' uid)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  newId)
    qed

    then show ?thesis
      using `a = (s, ANewId uid)` by (auto simp add: nth_append)
  next
    case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
    show ?thesis 
    proof (cases "t=tx")
      case True
      hence "s = i"
        using local.beginAtomic(1) local.beginAtomic(7) local.wf state_wellFormed_combine step.prems step.step step.steps unchangedInTransaction(3) by fastforce

      show ?thesis 
        apply (rule_tac x="length tr" in exI)
        using beginAtomic by (auto simp add: nth_append True `s = i`)
    next
      case False

      have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
      proof (rule step)
        show "currentTransaction S' i \<triangleq> tx"
          using `currentTransaction S'' i \<triangleq> tx` by (auto simp add: False  beginAtomic split: if_splits)
      qed

      then show ?thesis
        using `a = (s, ABeginAtomic t newTxns)` by (auto simp add: nth_append split: if_splits)
    qed
  next
    case (endAtomic s ls f ls' t)

    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (auto simp add: endAtomic split: if_splits)
    qed

    then show ?thesis 
      apply auto
      apply (rule_tac x=ib in exI)
      using endAtomic `currentTransaction S'' i \<triangleq> tx` by (auto simp add: nth_append)
  next
    case (dbop s ls f Op args ls' t c res vis)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  dbop)
    qed

    then show ?thesis
      using `a = (s, ADbOp c Op args res)` by (auto simp add: nth_append)
  next
    case (invocation s procName args initialState impl)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  invocation)
    qed

    then show ?thesis
      using invocation by (auto simp add: nth_append)
  next
    case (return s ls f res)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  return)
    qed

    then show ?thesis
      using return by (auto simp add: nth_append)
  next
    case (fail s ls)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` 
        by (auto simp add:  fail split: if_splits)
    qed

    then show ?thesis
      using fail by (auto simp add: nth_append)
  next
    case (invCheck txns res s)
    have "\<exists>ib txns. tr ! ib = (i, ABeginAtomic tx txns) \<and> ib < length tr \<and> (\<forall>j. ib < j \<and> j < length tr \<longrightarrow> tr ! j \<noteq> (i, AEndAtomic))"
    proof (rule step)
      show "currentTransaction S' i \<triangleq> tx"
        using `currentTransaction S'' i \<triangleq> tx` by (simp add:  invCheck)
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
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
  shows "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTransaction S' i = Some tx)
       \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
  using steps  packed noFails noCtxtSwitchInTx proof (induct rule: steps_induct)
  case initial
  then show ?case 
    using wellFormed_currentTransaction_unique_h(2) noUncommitted S_wellformed  apply auto
    by (meson not_None_eq wellFormed_currentTransaction_unique_h(2))

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

  from `S' ~~ a \<leadsto> S''`
  show ?case
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis 
      using IH by (auto simp add: open_transactions_append_one)
  next
    case (newId s ls f ls' uid)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)

    have openTransactions_empty: "openTransactions tr = {}"
    proof (auto simp add: openTransactions_def)
      fix i' tx' j txns
      assume a0: "j < length tr"
        and a1: "\<forall>k<length tr. j < k \<longrightarrow> tr ! k \<noteq> (i', AEndAtomic)"
        and a2: "tr ! j = (i', ABeginAtomic tx' txns)"

      have "\<not> allowed_context_switch (snd ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF `noContextSwitchesInTransaction (tr @ [a])`])
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

      thus "False"
        by (simp add: `a = (s, ABeginAtomic t newTxns)`)
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
    case (invocation s procName args initialState impl)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (return s ls f res)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (fail s ls)
    then show ?thesis
      using step.prems(2) by auto 
  next
    case (invCheck txns res s)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  qed
qed


lemma at_most_one_current_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    and packed: "packed_trace tr"
    and wf: "state_wellFormed S"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
  shows "\<forall>i. currentTransaction S' i \<noteq> None \<longrightarrow> i = fst (last tr)"
  using steps noCtxtSwitchInTx packed  noFails
proof (induct rule: steps_induct)
  case initial
  hence "currentTransaction S i = None" for i
    using noUncommitted
    by (meson local.wf option.exhaust wellFormed_currentTransactionUncommited) 
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

  show ?case
  proof (cases tr)
    case Nil
    hence "currentTransaction S' i = None" for i
      using noUncommitted `S ~~ tr \<leadsto>* S'`
      apply auto
      by (metis local.wf option.exhaust wellFormed_currentTransaction_unique_h(2))

    with `S' ~~ a \<leadsto> S''`
    show ?thesis 
      by (auto simp add: step.simps split: if_splits)

  next
    case (Cons x xs)
    hence tr_nonempty[simp]: "tr \<noteq> []" by simp

    have last_same: "fst (last tr) = fst a" if "\<not> allowed_context_switch (snd a)" 
      using use_packed_trace[OF `packed_trace (tr@[a])`, where i="length tr"] that
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
        using `currentTransaction S i = None` `S ~~ tr \<leadsto>* S'` currentTransaction_exists_beginAtomic local.wf by blast 

      have "\<not> allowed_context_switch (snd ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF `noContextSwitchesInTransaction (tr @ [a])`, where j="length tr"])
        show "(tr @ [a]) ! ib = (i, ABeginAtomic tx txns)"
          using ib by (simp add: ib_len nth_append) 
        show "\<forall>j. ib < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (i, AEndAtomic)"
          using that by (auto simp add: ib_no_end nth_append)
        show "ib < Suc (length tr)"
          by (simp add: ib_len less_Suc_eq)
          apply_end (auto simp add: ib_len)
      qed
      thus False
        using that by simp
    qed


    from `S' ~~ a \<leadsto> S''`
    show ?thesis
    proof (cases rule: step.cases)
      case (local s ls f ls')
      then show ?thesis using IH last_same by auto
    next
      case (newId s ls f ls' uid)
      then show ?thesis using IH last_same by auto
    next
      case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
      then show ?thesis using IH no_tx_if_context_switch by auto
    next
      case (endAtomic s ls f ls' t)
      then show ?thesis using IH last_same by auto
    next
      case (dbop s ls f Op args ls' t c res vis)
      then show ?thesis using IH by auto
    next
      case (invocation s procName args initialState impl)
      then show ?thesis using IH no_tx_if_context_switch by auto
    next
      case (return s ls f res)
      then show ?thesis using IH last_same by auto
    next
      case (fail s ls)
      then show ?thesis using IH
        using step.prems(3) by auto
    next
      case (invCheck txns res s)
      then show ?thesis using IH last_same by auto
    qed
  qed
qed


text {*
If we have an execution on a a single invocation starting with state satisfying the invariant, then we can convert 
this trace to a single-invocation trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
*}
lemma convert_to_single_session_trace:
  fixes tr :: "'any trace"
    and s :: invocation      
    and S S' :: "('ls,'any) state"
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    and noUncommitted:  "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
    and noCtxtSwitchInTx: "noContextSwitchesInTransaction tr"
    (* invariant holds on all states in the execution *)
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
    (* TODO special case for fail, pull (and others?) *)
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
  hence  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; packed_trace tr; 
               \<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
                   \<and> (\<forall>a. (a, False) \<notin> set tr') 
                   \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
    and  step: "S' ~~ a \<leadsto> S''"
    and  packed: "packed_trace (tr @ [a])"
    and prefix_invariant: "\<And>tr' S'.  \<lbrakk>isPrefix tr' (tr @ [a]); S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
    and noFails: "(s, AFail) \<notin> set (tr @ [a])"
    and noContextSwitch: "noContextSwitchesInTransaction (tr @ [a])"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by (auto, blast)


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
      by simp
    thus "packed_trace tr"
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
    case True (* the new action is on invocation s *)
    hence [simp]: "fst a = s" .

    show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s True"  (is ?goal) 
    proof (cases "tr = [] \<or> fst (last tr) = s")
      case True (* the previous action was on the same trace (if there was a previous action) *)
      hence [simp]: "tr = [] \<or> fst (last tr) = s" by simp
      hence ih3: "state_coupling S' S2 s True"
        using ih3' by simp


      have ih3_noTx: "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>" if "currentTransaction S' s = None"
        using ih3 that by (auto simp add: state_coupling_def)
      have ih3_tx: "S2 = S'" if "currentTransaction S' s \<triangleq> tx" for tx
        using ih3 that by (auto simp add: state_coupling_def)

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

      have vis_defined: "visibleCalls S' s \<noteq> None" if "currentTransaction S' s \<noteq> None"
        using state_wellFormed_combine[OF S_wf] state_wellFormed_tx_to_visibleCalls S_wf steps that by fastforce

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

      have tr_noSwitch: "noContextSwitchesInTransaction tr"
        using isPrefix_appendI noContextSwitch prefixes_noContextSwitchesInTransaction by blast

      have tr_packed: "packed_trace tr"
        using packed packed_trace_prefix by blast

      have tr_noFail: "\<And>s. (s, AFail) \<notin> set tr"
        using steps_step.prems(4) by auto


      show ?goal
      proof (cases "snd a")
        case ALocal
        hence "a = (s, ALocal)"
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
          by (auto simp add: state_ext S2_vis' a1)

        hence S''_S2_a: "S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr> = S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"  
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
            assume no_tx_S': "currentTransaction S'' s = None"
            hence no_tx_S': "currentTransaction S' s = None"
              using a1 by auto
            from ih3_noTx[OF no_tx_S']  
            show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>"
              using a1 by auto
          next
            fix tx
            assume tx: "currentTransaction S'' s \<triangleq> tx"
            hence tx': "currentTransaction S' s \<triangleq> tx" using a1 by auto
            from ih3_tx[OF tx']
            show "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"
              using a1 by auto
          qed
        qed
      next
        case (ANewId uid)
        hence [simp]: "a = (s, ANewId uid)"
          by (simp add: prod_eqI steps_step.prems) 

        with step
        have step': "S' ~~ (s, ANewId uid) \<leadsto> S''" by simp

        from step_elim_ANewId[OF step']
        obtain ls f ls' 
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls' uid), generatedIds := insert uid (generatedIds S')\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = NewId ls'"
            and a5: "uid \<notin> generatedIds S'"
          by metis  

        have a2':  "localState S2 s \<triangleq> ls" using a2 by (simp add: S2_localState) 
        have a3':  "currentProc S2 s \<triangleq> f" using a3 by (simp add: S2_currentProc)
        have a5':  "uid \<notin> generatedIds S2" using a5 by (simp add: S2_generatedIds)

        from a2' a3' a4 a5'
        have step_s: "S2 ~~ (s,(ANewId uid,True)) \<leadsto>\<^sub>S S2\<lparr>localState := localState S2(s \<mapsto> ls' uid), generatedIds := generatedIds S2 \<union> {uid}\<rparr>"
          by (rule step_s.newId)

        have S''_S2: "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S2\<lparr>localState := localState S2(s \<mapsto> ls' uid), generatedIds := generatedIds S2 \<union> {uid}\<rparr>" 
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
          proof auto
            assume no_tx_S': "currentTransaction S'' s = None"
            hence no_tx_S': "currentTransaction S' s = None"
              using a1 by auto
            from ih3_noTx[OF no_tx_S']  
            show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>"
              using a1 by auto
          next
            fix tx
            assume tx: "currentTransaction S'' s \<triangleq> tx"
            hence tx': "currentTransaction S' s \<triangleq> tx" using a1 by auto
            from ih3_tx[OF tx']
            show "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"
              using a1 by auto
          qed

        qed  

      next
        case (ABeginAtomic txId txns)
        hence [simp]: "a = (s, ABeginAtomic txId txns)"
          by (simp add: prod_eqI steps_step.prems) 

        with step
        have step': "S' ~~ (s, ABeginAtomic txId txns) \<leadsto> S''" by simp

        from step_elim_ABeginAtomic[OF step']
        obtain ls f ls' vis
          where a1: "S'' = S'\<lparr>
                  localState := localState S'(s \<mapsto> ls'), 
                  currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                  transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited),
                  transactionOrigin := transactionOrigin S'(txId \<mapsto> s),
                  visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> callsInTransaction S' txns \<down> happensBefore S')\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' s = None"
            and a6: "transactionStatus S' txId = None"
            and a7: "visibleCalls S' s \<triangleq> vis"
            and a8: "txns \<subseteq> commitedTransactions S'"
          by smt
            (*
      where a1: "S'' = S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited)\<rparr>"
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
          show "isPrefix tr (tr @ [a])" by simp
        qed


        define newS where "newS =  (S'\<lparr>
          localState := localState S2(s \<mapsto> ls'), 
          currentTransaction := currentTransaction S2(s \<mapsto> txId), 
          transactionStatus := transactionStatus S2(txId \<mapsto> Uncommited),
          transactionOrigin := transactionOrigin S2(txId \<mapsto> s),
          visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> callsInTransaction S' txns \<down> happensBefore S')\<rparr>)"  

        from a2' a3' a4 a5' a6' 
        have step_s: "S2 ~~ (s,(ABeginAtomic txId txns,True)) \<leadsto>\<^sub>S newS"
        proof (rule step_s.beginAtomic)  
          show "prog newS = prog S2"
            by (simp add: S2_prog newS_def)
          show "localState newS s \<triangleq> ls'"
            by (simp add: newS_def)
          show "currentTransaction newS s \<triangleq> txId"
            by (simp add: newS_def)
          show "transactionStatus newS txId \<triangleq> Uncommited"  
            by (simp add: newS_def)
          show "transactionOrigin newS txId \<triangleq> s"
            by (simp add: newS_def)

          have [simp]: "consistentSnapshot newS vis \<Longrightarrow> consistentSnapshot S' vis" for vis
            apply (auto simp add: consistentSnapshot_def newS_def a6' transactionConsistent_def)
            by (metis S2_transactionStatus option.inject transactionStatus.distinct(1))

          show "invariant_all newS" 
            using inv' apply (auto simp add: invariant_all_def)
            using S2_currentTransaction S2_localState S2_transactionStatus newS_def a1 inv'' invariant_all_def S2_transactionOrigin  by fastforce

          show "state_wellFormed newS"
            using S2_currentTransaction S2_localState S2_transactionOrigin S2_transactionStatus S_wf newS_def a1 state_wellFormed_combine steps' by auto

          show "state_monotonicGrowth S2 newS"
            using ih3 by (auto simp add: state_coupling_def state_monotonicGrowth_def S2_invocationOp newS_def a6 split: if_splits)

          show "currentProc newS s \<triangleq> f"
            by (simp add: a3 newS_def)


          have "state_wellFormed S'"
            using S_wf state_wellFormed_combine steps by auto

          have "\<And>c. callOrigin S' c \<noteq> Some txId"
            using `transactionStatus S' txId = None` `state_wellFormed S'`
            by (simp add: wf_no_transactionStatus_origin_for_nothing)


          thus "\<And>c. callOrigin newS c \<noteq> Some txId"
            by (simp add: newS_def)


          have "transactionStatus S' tx \<noteq> Some Uncommited" if "tx \<noteq> txId" for tx
          proof (rule notI)
            assume a: " transactionStatus S' tx \<triangleq> Uncommited"

            {
              assume "0 < length tr"
              from `S ~~ tr \<leadsto>* S'` S_wf
              have "currentTransaction S' (fst (last tr)) \<triangleq> tx "
              proof (rule only_one_commmitted_transaction_h[THEN conjunct1])

                show "packed_trace tr"
                  using isPrefix_appendI packed prefixes_are_packed by blast 
                show "transactionStatus S' tx \<triangleq> Uncommited"
                  by (simp add: a)


                show "\<And>s. (s, AFail) \<notin> set tr"
                  using `\<And>s. (s, AFail) \<notin> set (tr@[a])` by auto

                show "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
                  using `\<And>tx. transactionStatus S tx \<noteq> Some Uncommited` .

                show "noContextSwitchesInTransaction tr"
                  using `noContextSwitchesInTransaction (tr @ [a])` isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast 

              qed

              hence False
                using True \<open>0 < length tr\<close> a5 by fastforce
            }
            moreover
            {
              assume "tr = []"
              with `S ~~ tr \<leadsto>* S'`
              have "S' = S"
                by auto
              hence False
                using a `\<And>tx. transactionStatus S tx \<noteq> Some Uncommited`  by blast
            }
            ultimately show "False"
              by auto
          qed


          thus "\<And>tx. tx \<noteq> txId \<Longrightarrow> transactionStatus newS tx \<noteq> Some Uncommited"
            by (auto simp add: newS_def S2_transactionStatus)




        qed

        moreover have "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
          using ih1 by auto


        moreover have "S'' = newS"
          by (auto simp add: a1 newS_def S2_localState S2_currentTransaction S2_transactionStatus S2_transactionOrigin)  



        ultimately have steps_S''_s: "S ~~ (s, tr'@[(ABeginAtomic txId txns, True)]) \<leadsto>\<^sub>S* S''"
          using S2_currentTransaction S2_localState S2_transactionStatus steps_s_step by auto      


        show ?thesis
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ABeginAtomic txId txns, True)]) \<leadsto>\<^sub>S* S''"
            using steps_S''_s .
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic txId txns, True)])"
            by (simp add: ih2)     
          show "state_coupling S'' S'' s True"  
            unfolding state_coupling_def
            by (simp add: a1)
        qed    

      next
        case AEndAtomic
        hence [simp]: "a = (s, AEndAtomic)"
          by (simp add: local.steps_step(5) prod_eqI)

        with step
        have step': "S' ~~ (s, AEndAtomic) \<leadsto> S''" by simp

        from step_elim_AEndAtomic[OF step']  
        obtain ls f ls' t 
          where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls'), 
              currentTransaction := (currentTransaction S')(s := None), 
              transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = EndAtomic ls'"
            and a5: "currentTransaction S' s \<triangleq> t"
          by metis  

        have "S2 = S'"
          using a5 ih3_tx by blast

        have "invariant_all S'"
          using step_prog_invariant steps
          by (metis (no_types, lifting) isPrefix_appendI steps_step.prems(3)) 


(*from a2 a3 a4 a5 *)
        from a2 a3 a4 a5 a1
        have step_s: "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
        proof (rule step_s.endAtomic)  
          from `invariant_all S'`
          show "True = invariant_all S''"
            by (simp add: inv'')
        qed  

        with `S2 = S'`
        have "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
          by simp

        hence steps_S''_s: "S ~~ (s, tr'@[(AEndAtomic,True)]) \<leadsto>\<^sub>S* S''"
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
        hence [simp]: "a = (s, ADbOp cId operation args res)"
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
        hence step_s': "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S''"
          by (simp add: a1)


        show ?thesis
        proof (intro exI conjI)
          show "S ~~ (s, tr'@[(ADbOp cId operation args res,True)]) \<leadsto>\<^sub>S* S''" 
            using step_s' `S2 = S'` ih1 steps_s_step by blast 
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ADbOp cId operation args res, True)])"
            by (simp add: ih2)
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def
            by (auto simp add: a1 a5 state_ext)
        qed    
      next
        case (AInvoc procName args)
        hence "a = (s, AInvoc procName args)"
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
          using step_prog_invariant steps steps_step.prems(3) by force  

        have vis_None: "visibleCalls S' s = None"
          using  S_wf a2 state_wellFormed_combine steps state_wellFormed_ls_visibleCalls by blast 

        have "visibleCalls S2 s = None \<or> visibleCalls S2 s \<triangleq> {}"
          using S2_vis' option.sel vis'_sub vis_None by fastforce



        hence invContextSame: "invContext S2 s =  invContext S' s"
          by (auto simp add: S2_simps vis_None invContextH_def)


        find_theorems steps tr


        have at_most_one_tx: "(\<forall>i tx. ((i, tx) \<in> openTransactions tr) = currentTransaction S' i \<triangleq> tx) \<and> (\<forall>i j. currentTransaction S' i \<noteq> None \<and> currentTransaction S' j \<noteq> None \<longrightarrow> i = j)"
        proof (rule at_most_one_active_tx[OF ` S ~~ tr \<leadsto>* S'`])
          show "state_wellFormed S"
            using S_wf by auto
          show "packed_trace tr"
            using packed packed_trace_prefix by auto
          show " \<And>s. (s, AFail) \<notin> set tr"
            using steps_step.prems(4) by auto
          show  " \<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
            using steps_step.prems(5) by blast
          show  "noContextSwitchesInTransaction tr"
            using isPrefix_appendI noContextSwitch prefixes_noContextSwitchesInTransaction by blast
        qed


        have noCurrentTransaction_s: "currentTransaction S' s = None"
          using vis_None vis_defined by blast 





        have noCurrentTransaction: "currentTransaction S' i = None" for i
          using `S' ~~ a \<leadsto> S''`
          using \<open>fst a = s\<close> a2 `snd a = AInvoc procName args` apply (auto simp add: step.simps)

          using at_most_one_current_tx[OF `S ~~ tr \<leadsto>* S'` `noContextSwitchesInTransaction tr` `packed_trace tr` `state_wellFormed S` `\<And>s. (s, AFail) \<notin> set tr`]
          by (metis S_wf True noCurrentTransaction_s option.exhaust steps steps_empty steps_step.prems(5) wellFormed_currentTransactionUncommited)

        from at_most_one_tx and noCurrentTransaction
        have noOpenTxns: "openTransactions tr = {}" (* TODO allgemeines lemma raus ziehen *)
          by auto



        with at_most_one_tx
        have currentTxNone: "\<And>i. currentTransaction S' i = None"
          by auto


        find_theorems S
        have step_s': "S ~~ (s, (AInvoc procName args, True)) \<leadsto>\<^sub>S S'' "
        proof (rule step_s.invocation)
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
          thus "invocationOp S s = None"
            using steps steps_do_not_change_invocationOp by (metis not_Some_eq) 
          show "S'' = S'\<lparr>localState := localState S'(s \<mapsto> initialState), currentProc := currentProc S'(s \<mapsto> impl), visibleCalls := visibleCalls S'(s \<mapsto> {}), invocationOp := invocationOp S'(s \<mapsto> (procName, args))\<rparr>"
            by (auto simp add: state_ext S2_simps a1 S2_vis')
          show "invariant_all S'"
            using ih3' inv_S' state_coupling_same_inv by auto
          show "True = invariant_all S''"
            by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps.steps_step)
          show "prog S' = prog S"
            using steps steps_do_not_change_prog by blast
          show "state_wellFormed S'"
            using S_wf state_wellFormed_combine steps by auto


          show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommited"
            using currentTxNone `state_wellFormed S'` wellFormed_currentTransaction_back
            by (metis S_wf butlast_snoc in_set_butlastD option.distinct(1) steps steps_step.prems(4) steps_step.prems(5))

        qed



        show ?thesis 
        proof (intro exI conjI)
          show "S ~~ (s, [(AInvoc procName args, True)]) \<leadsto>\<^sub>S* S''"
            by (simp add: step_s' steps_s_single)
          show " \<forall>a. (a, False) \<notin> set ([(AInvoc procName args, True)])"
            by (simp add: ih2)
          show "state_coupling S'' S'' s True"
            unfolding state_coupling_def  
            apply (auto simp add: a1 state_ext)
            by force
        qed    
      next
        case (AReturn res)
        hence "a = (s, AReturn res)"
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
            by (auto simp add: a1 state_ext S2_simps S2_vis')
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
        hence "a = (s, AFail)"
          by (simp add: prod_eqI steps_step.prems(2))
        with noFails have "False"
          by simp
        thus ?thesis ..
      next
        case (AInvcheck txns res)
        hence "a = (s, AInvcheck  txns res)"
          by (simp add: prod_eqI steps_step.prems(2))

        with step
        have step': "S' ~~ (s, AInvcheck txns res) \<leadsto> S''" by simp  

        from step_elim_AInvcheck[OF step']
        have a1: "S'' = S'" 
          and a2': "\<forall>t\<in>txns. transactionStatus S' t \<triangleq> Commited"
          and a4: "res = invariant (prog S') (invContextVis S' (callsInTransaction S' txns \<down> happensBefore S'))"
          by auto

        text {* We already assumed it holds for all possible set of visible calls *}

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
      case False (* we are coming from a different invocation and executing an action on s now  *)
      hence [simp]: "tr \<noteq> []" and [simp]: "fst (last tr) \<noteq> s" by auto

      hence ih3: "state_coupling S' S2 s  False" using ih3' by simp

      text {* Because the trace is packed, there can only be two cases where we can go from another invocation to s: *}
      have "allowed_context_switch (snd a)"
      proof (rule context_switches_in_packed[OF packed])
        show "tr @ [a] = butlast tr @ [(fst (last tr), snd (last tr)), (s, snd a)] @ []"
          apply auto
          by (metis True prod.collapse)
        show "fst (last tr) \<noteq> s"
          by simp
      qed
      hence "(\<exists>tx txns. (snd a) = ABeginAtomic tx txns) \<or> (\<exists>p ar. (snd a) = AInvoc p ar)"
        using allowed_context_switch_def by blast
      thus ?thesis
      proof (rule disjE; clarsimp)
        fix tx txns
        assume "snd a = ABeginAtomic tx txns"

        with step
        have step': "S' ~~ (s, ABeginAtomic tx txns) \<leadsto> S''"
          by (metis True surjective_pairing) 

        from step_elim_ABeginAtomic[OF step']  
        obtain ls f ls' vis
          where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommited),
                    transactionOrigin := transactionOrigin S'(tx \<mapsto> s),
                    visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> callsInTransaction S' txns \<down> happensBefore S')\<rparr>"
            and a2: "localState S' s \<triangleq> ls"
            and a3: "currentProc S' s \<triangleq> f"
            and a4: "f ls = BeginAtomic ls'"
            and a5: "currentTransaction S' s = None"
            and a6: "transactionStatus S' tx = None"
            and a7: "visibleCalls S' s \<triangleq> vis"
            and a8: "txns \<subseteq> commitedTransactions S'"
          by smt
            (*
      where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommited)\<rparr>"
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
          show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic tx txns, True)])"
            using ih2 by auto

          show "state_coupling S'' S'' s True"
            by (auto simp add: state_coupling_def)

          have "S2 ~~ (s, ABeginAtomic tx txns, True) \<leadsto>\<^sub>S S''"
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
            show "prog S'' = prog S2"
              using ih3  prog_inv[OF local.step]
              by (simp add: state_coupling_def state_monotonicGrowth_prog)
            show "invariant_all S''"
              using inv'' by blast
            show "localState S'' s \<triangleq> ls'"
              using a2 a1 by auto
            show "currentTransaction S'' s \<triangleq> tx"
              using a1 by auto
            show "transactionStatus S'' tx \<triangleq> Uncommited"
              using a1 by auto
            show "transactionOrigin S'' tx \<triangleq> s"
              using a1 by auto
            show "state_wellFormed S''"
              using S_wf state_wellFormed_combine steps' by blast
            show "state_monotonicGrowth S2 S''"
              using ih3 by (auto simp add:  map_le_def a1 state_coupling_def state_monotonicGrowth_def \<open>transactionStatus S2 tx = None\<close>)
            show "currentProc S'' s \<triangleq> f"
              by (simp add: a1 a3)
            show "\<And>c. callOrigin S'' c \<noteq> Some tx"
              using S_wf a6 state_wellFormed_combine steps wf_callOrigin_implies_transactionStatus_defined a1 by (auto, blast)

            show "\<And>txa. txa \<noteq> tx \<Longrightarrow> transactionStatus S'' txa \<noteq> Some Uncommited"
              by (metis (no_types, lifting) S_wf \<open>currentTransaction S'' s \<triangleq> tx\<close> at_most_one_current_tx noContextSwitch option.discI option.inject packed steps' steps_step.prems(4) steps_step.prems(5) wellFormed_currentTransaction_back)

          qed

          thus "S ~~ (s, tr'@[(ABeginAtomic tx txns, True)]) \<leadsto>\<^sub>S*  S''"
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
            thus "invocationOp S2 s = None" by blast
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
              using S_wf state_wellFormed_combine steps by auto

            have "currentTransaction S' s = None"
              by (simp add: \<open>state_wellFormed S'\<close> a5 wellFormed_invoc_notStarted(1))

            have "\<And>s. (s, AFail) \<notin> set tr"
              using steps_step.prems(4) by auto


            have "currentTransaction S' s = None" for s
              by (metis S_wf True \<open>state_wellFormed S'\<close> a5 at_most_one_current_tx last_snoc noContextSwitch packed step' steps' steps_step.prems(4) steps_step.prems(5) unchangedInTransaction(3) wellFormed_invoc_notStarted(1))

            from this
            show "\<And>tx. transactionStatus S' tx \<noteq> Some Uncommited"
              using wellFormed_currentTransaction_back[OF steps `\<And>s. (s, AFail) \<notin> set tr` `\<And>tx. transactionStatus S tx \<noteq> Some Uncommited` `state_wellFormed S`]
              by auto
      qed
      thus "S ~~ (s, tr'@[(AInvoc p ar, True)]) \<leadsto>\<^sub>S* S''"
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
  hence different_session[simp]:  "fst a \<noteq> s" by simp
  
  text {* we are now in the case of doing steps in a different session.
   We show that all of these preserve the coupling. 
   *}
   
  text {* no matter what he had before, the coupling with "False" will hold: *}
  from ih3'
  have old_coupling: "state_coupling S' S2 s False"
    by (auto simp add: state_coupling_def state_monotonicGrowth_def split: if_splits)
  
  from step
  have new_coupling: "state_coupling S'' S2 s False"
  proof (induct rule: step.cases) (* prove this with a case distinction on the action *)
    case (local C s ls f ls')
    then show ?case 
      using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (newId C s ls f ls' uid)
    thus ?case 
      using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (beginAtomic C s ls f ls' t)
    then show ?case using old_coupling different_session 
      apply (auto simp add: state_coupling_def state_monotonicGrowth_def)
      by (metis less_eq_option_None_code less_eq_option_Some_None not_None_eq)
  next
    case (endAtomic C s ls f ls' t)
    then show ?case using old_coupling different_session 
      apply (auto simp add: state_coupling_def state_monotonicGrowth_def)
      by (metis domD domIff less_eq_option_None less_eq_option_None_code less_eq_option_Some less_eq_transactionStatus_def)
  next
    case (dbop C s ls f Op args ls' t c res vis)
    
    have "callOrigin C c = None"
      using `calls C c = None`
      using S_wf dbop.hyps(1) state_wellFormed_combine steps wellFormed_callOrigin_dom2 by blast
      
    hence "callOrigin S2 c = None"
      using dbop.hyps(1) old_coupling state_coupling_def state_monotonicGrowth_callOrigin2 by force
      
    with dbop
    show ?case using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (invocation C s procName args initialState impl)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (return C s ls f res)
    
    have "state_wellFormed S'"
      using S_wf state_wellFormed_combine steps by blast
      
    
    have "invocationRes C s = None"
      using  return.hyps(1) return.hyps(4)  state_wellFormed_no_result_when_running[OF `state_wellFormed S'`] steps by blast
    
    with return
    show ?case using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (fail C s ls)
    
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def state_monotonicGrowth_def)
  next
    case (invCheck C s vis res)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  qed
  
    
  thus "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s False"
    using ih1 ih2 by blast
    
    
qed
qed


lemma convert_to_single_session_trace_invFail_step:
fixes tr :: "'any trace"
  and s :: invocation      
  and S S' :: "('ls, 'any) state"
assumes step: "S ~~ (s,a) \<leadsto> S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "a \<noteq> AFail"
    (* invariant holds in the initial state *)
    and inv: "invariant_all S"
    (* invariant no longer holds *)
    and not_inv: "\<not>invariant_all S'"
    and coupling: "state_coupling S S2 s sameSession"
    and ctxtSwitchCases: "\<not>sameSession \<Longrightarrow> allowed_context_switch a" (* (\<exists>tx txns. a = ABeginAtomic tx txns) \<or> (\<exists>p ar. a = AInvoc p ar) *)
    (* we assume that we are not in a transaction (inside a transaction it is not necessary for invariants to hold)*)
    (* and not_in_transaction: "currentTransaction S s = None " *)
shows "\<exists>tr' S2'. (S2 ~~ (s, tr') \<leadsto>\<^sub>S* S2') 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
using step proof (cases rule: step.cases)
  case (local ls f ls')
  text {* a local step does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using local by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using local by (auto simp add: consistentSnapshot_def)
  qed
  
  with inv and not_inv
  have False by simp
    
  thus ?thesis ..
next
  case (newId ls f ls' uid)
  text {* generating a new id does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using newId by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using newId by (auto simp add: consistentSnapshot_def)
  qed
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (beginAtomic ls f ls' t)
  text {* starting a transaction does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using beginAtomic by (auto simp add: invContextH_def restrict_map_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    have "consistentSnapshot S' vis = consistentSnapshot S vis" for vis
      using beginAtomic by (auto simp add: consistentSnapshot_def transactionConsistent_def)
    thus "consistentSnapshot S' = consistentSnapshot S" ..
  qed
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (endAtomic ls f ls' t)
  text {* Ending a transaction includes an invariant-check in the single-invocation semantics, so we get a failing trace. *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Commited)\<rparr>"
  
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
        = S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Commited)\<rparr>"
     using S2'_def by simp
     
    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add: invariant_all_def state_coupling_def local.endAtomic(6) split: if_splits)
      fix vis
      assume a0: "S2 = S"
         and a1: "consistentSnapshot S' vis"
         and a2: "\<not> invariant (prog S') (invContextVis S' vis)"
      
      show "\<exists>vis. consistentSnapshot S2' vis \<and> \<not> invariant (prog S2') (invContextVis S2' vis)"
      proof (rule exI[where x=vis], intro conjI)
        from a1
        show "consistentSnapshot S2' vis"
          by (auto simp add: consistentSnapshot_def S2'_def `S2 = S`  local.endAtomic(2))
          
        from a2
        show "\<not> invariant (prog S2') (invContextVis S2' vis)"  
          by (auto simp add: S2'_def `S2 = S`  local.endAtomic(2))
      qed    
    qed
  qed  
  
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (dbop ls f Op args ls' t c res vis)
  text {* uncommitted operations do not affect the invariant *}
  
  have hb': "happensBefore S' = happensBefore S \<union> vis \<times> {c}"
    using dbop by auto
    
    
  
  have "invariant_all S'" if "invariant_all S"
  using that proof (auto simp add: invariant_all_def)
    fix vis'
    assume a0: "\<forall>vis. consistentSnapshot S vis \<longrightarrow> invariant (prog S) (invContextVis S vis)"
       and a1: "consistentSnapshot S' vis'"
    
    from a1
    have "vis' \<subseteq> insert c (dom (calls S))" 
      by (auto simp add: consistentSnapshot_def dbop)
    
    
      
    from a1  
    have "causallyConsistent (happensBefore S \<union> vis \<times> {c}) vis'" 
      using hb' by (auto simp add: consistentSnapshot_def causallyConsistent_def)
    
    hence "causallyConsistent (happensBefore S) vis'"
      by (auto simp add: causallyConsistent_def)
         
    
    from a1
    have "transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis'"
      by (auto simp add: consistentSnapshot_def dbop)
    
    hence "c \<notin> vis'"
      by (metis (full_types) S_wellformed fun_upd_same local.dbop(6) map_upd_eqD1 transactionConsistent_def transactionStatus.distinct(1) wellFormed_currentTransaction_unique_h(2)) (* takes long *) 
      
    with `vis' \<subseteq> insert c (dom (calls S)) `
    have "vis' \<subseteq> dom (calls S)"
      by blast 
      
    from `transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis'`  
    have "transactionConsistent (callOrigin S) (transactionStatus S) vis'"
      apply (subst transactionConsistent_def)
      apply auto
      using transactionConsistent_Commited \<open>c \<notin> vis'\<close> apply (metis (mono_tags, lifting) map_upd_Some_unfold)
      by (smt S_wellformed \<open>vis' \<subseteq> dom (calls S)\<close> domIff fun_upd_idem_iff fun_upd_triv fun_upd_twist local.dbop(7) subset_eq transactionConsistent_all_from_same wellFormed_callOrigin_dom)
      
      
      
   (*   by (metis (full_types) S_wellformed fun_upd_same local.dbop(6) map_upd_eqD1 transactionConsistent_def transactionStatus.distinct(1) wellFormed_currentTransaction_unique_h(2))*)
      
    from `transactionConsistent (callOrigin S) (transactionStatus S) vis'`
     and `vis' \<subseteq> dom (calls S)`
     and `causallyConsistent (happensBefore S) vis'`
    have "consistentSnapshot S vis'"
      by (simp add: consistentSnapshot_def)
      
    with a0  
    have "invariant (prog S) (invContextVis S vis')"
      by blast  
    
    have [simp]: "prog S' = prog S"
      using local.step prog_inv by auto
    
    have commitedCalls_simp: 
         "commitedCallsH (callOrigin S(c \<mapsto> t)) (transactionStatus S) 
        = commitedCallsH (callOrigin S) (transactionStatus S)"
      using S_wellformed local.dbop(6) local.dbop(7) by auto
        
    have "c \<notin> commitedCalls S"
      by (simp add: S_wellformed local.dbop(7))
      
      
    have "invContextVis S' vis' = invContextVis S vis'"
      by (auto simp add: invContextH_def dbop commitedCalls_simp S_wellformed restrict_relation_def `c \<notin> commitedCalls S`)
      
    with `invariant (prog S) (invContextVis S vis')`   
    show "invariant (prog S') (invContextVis S' vis')"
      by simp
  qed    

  hence False
    by (simp add: inv not_inv)
  thus ?thesis ..
next
  case (invocation procName args initialState impl)
  text {* invocations include an invariant-check *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> initialState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"
  
  have "S2 ~~ (s,(AInvoc procName args, False)) \<leadsto>\<^sub>S S'"
  proof (rule step_s.intros)
    
    have "localState S2 s = None"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    have "\<And>x. invocationOp S2 s \<noteq> Some x"      
      using invocation coupling by (auto simp add: state_coupling_def state_monotonicGrowth_invocationOp split: if_splits)
    thus "invocationOp S2 s = None" by blast     
    show "procedure (prog S2) procName args \<triangleq> (initialState, impl)"
      using invocation coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "uniqueIdsInList args \<subseteq> knownIds S"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invocationOp S s = None"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invariant_all S"
      by (simp add: inv)
    show "S' = S\<lparr>localState := localState S(s \<mapsto> initialState), currentProc := currentProc S(s \<mapsto> impl), visibleCalls := visibleCalls S(s \<mapsto> {}), invocationOp := invocationOp S(s \<mapsto> (procName, args))\<rparr>"
      using local.invocation(2) by blast  
    show "False = invariant_all S'"
      by (simp add: not_inv)
    show "prog S = prog S2" 
      using coupling by (auto simp add: state_coupling_def state_monotonicGrowth_prog split: if_splits)
    show "state_wellFormed S"
      by (simp add: S_wellformed)
  qed    
    
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (return ls f res)
  text {* return contains an invariant check *}
  
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
    proof (auto simp add: invariant_all_def state_coupling_def not_in_transaction)
      fix vis vis'
      assume a0: "consistentSnapshot S' vis"
         and a1: "\<not> invariant (prog S') (invContextVis S' vis)"
         and a2: "vis' orElse {} \<subseteq> visibleCalls S s orElse {}"
         and a3: "S2 = S\<lparr>visibleCalls := (visibleCalls S)(s := vis')\<rparr>"
      
      show "\<exists>vis. consistentSnapshot S2' vis \<and> \<not> invariant (prog S2') (invContextVis S2' vis)"
      proof (rule exI[where x="vis"], intro conjI)
        show "consistentSnapshot S2' vis"
          using a0 by (auto simp add: consistentSnapshot_def S2'_def a3  return(2))
          
        from a1
        show "\<not> invariant (prog S2') (invContextVis S2' vis)"  
          using a0 by (auto simp add: consistentSnapshot_def S2'_def a3  return(2))
      qed 
    qed
  qed
      
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (fail ls)
  text {* we assumed that there are no fails *}
  then show ?thesis
    using noFails by blast
next
  case (invCheck vis res)
  then show ?thesis
    using inv not_inv by blast (* same state *)
qed

lemma convert_to_single_session_trace_invFail:
fixes tr :: "'any trace"
  and S S' :: "('ls, 'any) state"
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    (* invariant holds in the initial state *)
    and inv: "invariant_all S"
    (* invariant no longer holds *)
    and not_inv: "\<not> invariant_all S'"
shows "\<exists>tr' S2 s. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
proof -
  
  have not_inv_ex: "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"
    by (rule exI[where x="tr"], rule exI[where x="S'"], auto  simp add: not_inv steps)
    

  text {* There must be a place where the invariant fails for the first time: *}
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
        by simp 
    next
      case (step S' tr a S'')
      then show ?case 
      proof (cases "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail")
        case True
        then show ?thesis
          using inv step.IH by force 
      next
        case False
        
        hence invariant_in_tr: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
          by blast
        
        from `\<exists>tr_pre S_fail. isPrefix tr_pre (tr @ [a]) \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail`
        obtain tr_pre S_fail 
          where "isPrefix tr_pre (tr @ [a])" 
          and "S ~~ tr_pre \<leadsto>* S_fail" 
          and "\<not> invariant_all S_fail"
          by blast
        
        have "tr_pre = tr @ [a]"
        proof (rule ccontr)
          assume "tr_pre \<noteq> tr @ [a]"
          with `isPrefix tr_pre (tr @ [a])`
          have "isPrefix tr_pre tr"
            by (metis (no_types, lifting) append_eq_append_conv_if append_take_drop_id isPrefix_def length_append_singleton not_less_eq_eq take_all)
          
          with invariant_in_tr
          have "invariant_all S_fail"
            using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> by blast
          with `\<not> invariant_all S_fail`
          show False ..
        qed
        
        hence "S_fail = S''"
          using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> step.step step.steps steps_step traceDeterministic by blast
          
        with `\<not> invariant_all S_fail`
        have "\<not>invariant_all S''"
          by auto
          
        
        show ?thesis 
         using step invariant_in_tr `\<not>invariant_all S''` by blast 
      qed
    qed  
  qed
  
  obtain as aa where a_def: "a = (as,aa)"
    by force


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
    show "(as, AFail) \<notin> set tr1" using tr_split noFails by auto
    show "\<And>S' tr1'. \<lbrakk>isPrefix tr1' tr1; S ~~ tr1' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using inv_before by auto
  qed


  have tr1_packed: "packed_trace (tr1@[a])"     
  using packed proof (rule prefixes_are_packed)
    have "isPrefix (tr1 @ [a]) ((tr1 @ [a]) @ tr2)" by (rule isPrefix_appendI)
    thus "isPrefix (tr1 @ [a]) tr" using tr_split by auto
  qed  
    
  
  obtain tr_a S_fail'
    where steps_tr_a: "S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'"
      and tr_a_fails: "\<exists>a. (a, False)\<in>set tr_a"
  proof (atomize_elim, rule convert_to_single_session_trace_invFail_step)
    show "S1 ~~ (as,aa) \<leadsto> S_fail"
      using a_def stepA by blast
    show "state_wellFormed S1"
      using S_wellformed state_wellFormed_combine steps1 by blast
    show "aa \<noteq> AFail"
      using a_def noFails tr_split by auto
    show "invariant_all S1"
      using inv_before isPrefix_refl steps1 by blast
    show "\<not> invariant_all S_fail"
      by (simp add: first_not_inv)
    show "state_coupling S1 S1' as (tr1 = [] \<or> fst (last tr1) = as)"  
      using tr1'_coupling .
      
       
    assume "\<not> (tr1 = [] \<or> fst (last tr1) = as)"
    hence "tr1 \<noteq> []" and "fst (last tr1) \<noteq> as"
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
    from `S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'` 
     and `S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'`
    show " S ~~ (as, tr1' @ tr_a) \<leadsto>\<^sub>S* S_fail'"
      by (rule steps_s_append)  
    show "\<exists>a. (a, False) \<in> set (tr1' @ tr_a)"
      using tr_a_fails by auto
  qed
qed

lemma wellFormed_state_causality:
assumes wf: "state_wellFormed S"
shows "\<And>s vis. visibleCalls S s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore S) vis"
  and "trans (happensBefore S)"
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
    
  
    
  show "trans (happensBefore C')"
    using `trans (happensBefore C)` `C ~~ a \<leadsto> C'` apply (auto simp add: step_simps_all)
    using causal apply (auto simp add: causallyConsistent_def)
    by (smt Un_iff domIff empty_iff insert_iff mem_Sigma_iff step.hyps(1) subset_eq trans_def wellFormed_visibleCallsSubsetCalls_h(1))
    
  show "visibleCalls C' s \<triangleq> vis \<longrightarrow> causallyConsistent (happensBefore C') vis" for s vis
    using causal `C ~~ a \<leadsto> C'` apply (auto simp add: step_simps_all)
    apply (auto simp add: causallyConsistent_def split: if_splits)
    apply (smt Un_iff downwardsClosure_def mem_Collect_eq step.hyps(3) trans_def)
    apply (metis (no_types, lifting) domIff mem_Sigma_iff set_rev_mp step.hyps(1) wellFormed_visibleCallsSubsetCalls_h(1))
    using step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast
    
qed


lemma show_transactionConsistent[case_names only_commited[in_vis origin_tx] all_from_same[in_vis origin_same]]:
assumes "\<And>c tx. \<lbrakk>c\<in>vis; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus tx \<triangleq> Commited"
    and "\<And>c1 c2. \<lbrakk>c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
shows "transactionConsistent origin txStatus vis"
using assms by (auto simp add: transactionConsistent_def)

lemma wellFormed_state_callOrigin_transactionStatus:
assumes wf: "state_wellFormed C"
    and "callOrigin C c \<triangleq> tx"
shows "transactionStatus C tx \<noteq> None"   
using assms apply (induct  rule: wellFormed_induct)
by (auto simp add: initialState_def step_simps_all split: if_splits)

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






lemma wellFormed_state_transaction_consistent:
assumes wf: "state_wellFormed S"
(* contains only committed calls and calls from current transaction:  *)
shows "\<And>s vis c tx. \<lbrakk>visibleCalls S s \<triangleq> vis; c\<in>vis; callOrigin S c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus S tx \<triangleq> Commited \<or> currentTransaction S s \<triangleq> tx"
(* contains all calls from a transaction *)
  and "\<And>s vis c1 c2. \<lbrakk>visibleCalls S s \<triangleq> vis; c1\<in>vis; callOrigin S c1 = callOrigin S c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
(* happens-before consistent with transactions *)
  and "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin S x1 \<noteq> callOrigin S y1; callOrigin S x1 = callOrigin S x2; callOrigin S y1 = callOrigin S y2 \<rbrakk> \<Longrightarrow>  (x1,y1) \<in> happensBefore S \<longleftrightarrow> (x2, y2) \<in> happensBefore S"
(* happens-before only towards committed transactions or to the same transaction *)  
  and "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore S; callOrigin S y \<triangleq> tx; callOrigin S x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus S tx' \<triangleq> Commited \<or> tx' = tx"
using assms  proof (induct  rule: wellFormed_induct)
  case initial
  
  define init where [simp]: "init = (initialState (prog S))"
  
  show "\<And>s vis c tx. \<lbrakk>visibleCalls init s \<triangleq> vis; c\<in>vis; callOrigin init c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus init tx \<triangleq> Commited \<or> currentTransaction init s \<triangleq> tx"
    by (auto simp add: initialState_def )
  show "\<And>s vis c1 c2. \<lbrakk>visibleCalls init s \<triangleq> vis; c1\<in>vis; callOrigin init c1 = callOrigin init c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
    by (auto simp add: initialState_def )
  show "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin init x1 \<noteq> callOrigin init y1; callOrigin init x1 = callOrigin init x2;
                    callOrigin init y1 = callOrigin init y2\<rbrakk>
                   \<Longrightarrow> ((x1, y1) \<in> happensBefore init) = ((x2, y2) \<in> happensBefore init)"
    by (auto simp add: initialState_def )                   
  show "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore init; callOrigin init y \<triangleq> tx; callOrigin init x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus init tx' \<triangleq> Commited \<or> tx' = tx"
    by (auto simp add: initialState_def )
next
  case (step C a C')
  
  (* contains only committed calls and calls from current transaction:  *)
  from step 
  have IH1: "\<And>s vis c tx. \<lbrakk>visibleCalls C s \<triangleq> vis; c\<in>vis; callOrigin C c \<triangleq> tx\<rbrakk> \<Longrightarrow> transactionStatus C tx \<triangleq> Commited \<or> currentTransaction C s \<triangleq> tx"
    by auto
(* contains all calls from a transaction *)
  from step 
  have IH2: "\<And>s vis c1 c2. \<lbrakk>visibleCalls C s \<triangleq> vis; c1\<in>vis; callOrigin C c1 = callOrigin C c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
    by auto
(* happens-before consistent with transactions *)
  from step 
  have IH3: "\<And>x1 y1 x2 y2. \<lbrakk>callOrigin C x1 \<noteq> callOrigin C y1; callOrigin C x1 = callOrigin C x2; callOrigin C y1 = callOrigin C y2 \<rbrakk> \<Longrightarrow>  (x1,y1) \<in> happensBefore C \<longleftrightarrow> (x2, y2) \<in> happensBefore C"
    by blast
  hence IH3_to: "\<And>x1 y1 x2 y2. \<lbrakk>(x1,y1) \<in> happensBefore C; callOrigin C x1 = callOrigin C x2; callOrigin C y1 = callOrigin C y2; callOrigin C x1 \<noteq> callOrigin C y1 \<rbrakk> \<Longrightarrow> (x2, y2) \<in> happensBefore C"   
    by blast
(* happens-before only towards committed transactions or to the same transaction *)  
  from step 
  have IH4: "\<And>x y tx tx'. \<lbrakk>(x,y)\<in>happensBefore C; callOrigin C y \<triangleq> tx; callOrigin C x \<triangleq> tx'\<rbrakk> \<Longrightarrow> transactionStatus C tx' \<triangleq> Commited \<or> tx' = tx"
    by auto
  
  have new_snapshot_cases: "(c \<in> callsInTransactionH orig txns \<down> hb) 
  \<longleftrightarrow> ((\<exists>c2 txn. (c,c2)\<in>hb \<and> orig c2 \<triangleq> txn \<and> txn\<in>txns) 
       \<or> (\<exists>txn. orig c \<triangleq> txn \<and> txn\<in>txns ))" 
    for c orig txns hb
    by (auto simp add: callsInTransactionH_def downwardsClosure_def)  
    
    
  show IH1': "transactionStatus C' tx \<triangleq> Commited \<or> currentTransaction C' s \<triangleq> tx"
    if g1: "visibleCalls C' s \<triangleq> vis" 
    and g2: "c\<in>vis" 
    and g3: "callOrigin C' c \<triangleq> tx"
    for s vis c tx
  using `C ~~ a \<leadsto> C'`
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using IH1 g1 g2 g3 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis using IH1 g1 g2 g3 by auto
  next
    case (beginAtomic s' ls f ls' t vis' newTxns newCalls snapshot)
    show ?thesis 
      using g1 g2 g3 apply (auto simp add: beginAtomic)
      using local.beginAtomic(7) step.hyps(1) wellFormed_state_callOrigin_transactionStatus apply auto[1]
      using IH1 local.beginAtomic(6) local.beginAtomic(8) apply fastforce
      apply (auto simp add: new_snapshot_cases)
      using IH1 local.beginAtomic(6) local.beginAtomic(8) apply fastforce
      using IH4 local.beginAtomic(9) apply blast
      using local.beginAtomic(9) apply blast
      using IH1 by blast
    
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
      apply (simp add: local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2)
      using IH1 by blast
      
  next
    case (invocation s' procName args initialState impl)
    show ?thesis 
      using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (fail s ls)
    then show ?thesis using IH1 g1 g2 g3 by (auto simp add: invocation split: if_splits)
  next
    case (invCheck txns res s)
    then show ?thesis using IH1 g1 g2 g3 by auto
  qed
    
  
  show IH2': "c2\<in>vis"
    if g1: "visibleCalls C' s \<triangleq> vis"
    and g2: "c1\<in>vis"
    and g3: "callOrigin C' c1 = callOrigin C' c2"
    for s vis c1 c2
  using `C ~~ a \<leadsto> C'`
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using IH2 g1 g2 g3 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  next
    case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
    then show ?thesis  
      using g1 g2 g3 apply (auto split: if_splits)
      using step.hyps(3) apply blast
      apply (auto simp add: new_snapshot_cases)
      apply (metis IH3)
      using IH2 by blast
      
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

      have not_committed_h: "transactionStatus C t \<noteq> Some Commited" if "c1 \<in> vis"
          using that local.dbop(6) step.hyps(1) by auto
      
      show ?thesis 
      using False g1 g2 g3 apply (auto simp add: dbop split: if_splits)
      using not_committed_h IH1 local.dbop(6) step.hyps(1) wellFormed_currentTransaction_unique_h(1) apply blast 
      apply (simp add: local.dbop(7) step.hyps(1) wellFormed_visibleCallsSubsetCalls2)
      using IH2 by blast
    qed
  next
    case (invocation s procName args initialState impl)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (return s ls f res)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (fail s ls)
    then show ?thesis  using IH2 g1 g2 g3 by (auto split: if_splits)
  next
    case (invCheck txns res s)
    then show ?thesis  using IH2 g1 g2 g3 by auto
  qed
  
  show IH4': "transactionStatus C' tx' \<triangleq> Commited \<or> tx' = tx"
      if g1: "(x,y)\<in>happensBefore C'"
      and g2: "callOrigin C' y \<triangleq> tx"
      and g3: "callOrigin C' x \<triangleq> tx'"
      for x y tx tx'
  using `C ~~ a \<leadsto> C'`
  proof (cases rule: step.cases)
    case (local s ls f ls')
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (newId s ls f ls' uid)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
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
    case (invocation s procName args initialState impl)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (return s ls f res)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (fail s ls)
    then show ?thesis using g1 g2 g3 IH4 by auto
  next
    case (invCheck txns res s)
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
    using `C ~~ a \<leadsto> C'`
    proof (cases rule: step.cases)
      case (local s ls f ls')
      then show ?thesis using whenUnchanged by auto
    next
      case (newId s ls f ls' uid)
      then show ?thesis using whenUnchanged by auto
    next
      case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
      then show ?thesis using whenUnchanged by auto
    next
      case (endAtomic s ls f ls' t)
      then show ?thesis using whenUnchanged by auto
    next
      case (dbop s ls f Op args ls' t c res vis)
      
      from `calls C c = None`
      have c_no_hb1[simp]: "(x, c) \<notin> happensBefore C" for x
        using wellFormed_visibleCallsSubsetCalls_h(1)[OF `state_wellFormed C`] by auto
        
      have [simp]: "callOrigin C c = None"
        by (simp add: local.dbop(7) step.hyps(1))
        
      have t_uncomited[simp]:  "transactionStatus C t \<triangleq> Uncommited"
          using local.dbop(6) step.hyps(1) wellFormed_currentTransactionUncommited by blast
      
      have origin_t: "callOrigin C y2 \<triangleq> t" 
            if "callOrigin C y1 = callOrigin C y2"
            and "callOrigin C x1 \<triangleq> t"
            and "(x1, y1) \<in> happensBefore C"
            for x1 y1 y2
            by (metis IH3_to \<open>callOrigin C c = None\<close> \<open>transactionStatus C t \<triangleq> Uncommited\<close> that c_no_hb1 not_None_eq option.inject step.hyps(5) transactionStatus.distinct(1))      
          
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
          by (metis IH3_to causallyConsistent_def local.dbop(6) local.dbop(9) step.hyps(1) wellFormed_state_calls_from_current_transaction_in_vis wellFormed_state_causality(1))
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
      case (invocation s procName args initialState impl)
      then show ?thesis using whenUnchanged by auto
    next
      case (return s ls f res)
      then show ?thesis using whenUnchanged by auto
    next
      case (fail s ls)
      then show ?thesis using whenUnchanged by auto
    next
      case (invCheck txns res s)
      then show ?thesis using whenUnchanged by auto
    qed
  qed
qed  



lemma wellFormed_state_consistent_snapshot:
assumes wf: "state_wellFormed S"
assumes vis: "visibleCalls S s \<triangleq> vis"
assumes noTx: "currentTransaction S s = None" 
shows "consistentSnapshot S vis"
unfolding consistentSnapshot_def proof (intro conjI)
  show "vis \<subseteq> dom (calls S)"
    using wf vis
    using wellFormed_visibleCallsSubsetCalls_h(2) by fastforce 
    
  show "causallyConsistent (happensBefore S) vis"
    using local.wf vis wellFormed_state_causality(1) by auto
    
  show "transactionConsistent (callOrigin S) (transactionStatus S) vis"
  proof (induct rule: show_transactionConsistent)
    case (only_commited c tx)
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
  


find_consts name: trans "'a rel \<Rightarrow> bool"

lemma causallyConsistent_downwards_closure:
assumes wf: "state_wellFormed S"
shows "causallyConsistent (happensBefore S) (cs \<down> happensBefore S)"
apply (auto simp add: causallyConsistent_def downwardsClosure_def)
  by (meson local.wf transD wellFormed_state_causality(2))


lemma consistentSnapshot_txns:
assumes wf: "state_wellFormed S"
  and comitted: "txns \<subseteq> commitedTransactions S"
shows "consistentSnapshot S (callsInTransaction S txns \<down> happensBefore S)"
unfolding consistentSnapshot_def proof (intro conjI)
 
  show "callsInTransaction S txns \<down> happensBefore S \<subseteq> dom (calls S)"
    apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
    using local.wf wellFormed_callOrigin_dom2 apply fastforce
    by (simp add: domD happensBefore_in_calls_left local.wf)
    
  show "causallyConsistent (happensBefore S) (callsInTransaction S txns \<down> happensBefore S)"
    apply (auto simp add: callsInTransactionH_def downwardsClosure_def causallyConsistent_def)
    by (meson happensBefore_transitive local.wf transD)
    
  show "transactionConsistent (callOrigin S) (transactionStatus S) (callsInTransaction S txns \<down> happensBefore S)"
  proof (induct rule: show_transactionConsistent)
    case (only_commited c tx)
    then show ?case 
      apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
      using comitted apply blast
      using comitted local.wf wellFormed_state_transaction_consistent(4) by fastforce
  next
    case (all_from_same c1 c2)
    then show ?case 
      apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
      by (metis local.wf wellFormed_state_transaction_consistent(3))
  qed
qed    

text {* if there is an failing invariant check in the trace, then there is a prefix of the trace leading to a
  state that does not satisfy the invariant *}
lemma invCheck_to_failing_state:
assumes steps: "S ~~ trace \<leadsto>* S'"
    and inv_fail: "(s, AInvcheck txns False) \<in> set trace"
    and state_wf: "state_wellFormed S"
shows "\<exists>tr' S_fail. isPrefix tr' trace \<and> (S ~~ tr' \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail" 
using steps inv_fail proof (induct rule: steps_induct)
  case initial
  then show ?case
    by auto 
next
  case (step S' tr a S'')
  show ?case 
  proof (cases "(s, AInvcheck txns False) \<in> set tr")
    case True
    with step.IH
    obtain tr' S_fail 
      where "isPrefix tr' tr" 
        and"S ~~ tr' \<leadsto>* S_fail" 
        and "\<not> invariant_all S_fail"
      by blast
      
    then show ?thesis
      using isPrefix_append by blast 
      
  next
    case False
    with `(s, AInvcheck txns False) \<in> set (tr @ [a])`
    have "a = (s, AInvcheck txns False)" by auto
    
    show ?thesis
    proof (intro exI conjI)
      show "isPrefix (tr @ [a]) (tr @ [a])"
        by simp
      show "S ~~ tr @ [a] \<leadsto>* S''"
        using step.step step.steps steps_step by fastforce   
      
      from `S' ~~ a \<leadsto> S''`
      have "S' ~~ (s, AInvcheck txns False) \<leadsto> S''" using `a = (s, AInvcheck txns False)` by simp
      hence  [simp]: "S'' = S'" 
       and "\<forall>t\<in>txns. transactionStatus S' t \<triangleq> Commited"
       and invFail: "\<not> invariant (prog S') (invContextVis S' (callsInTransaction S' txns \<down> happensBefore S'))"
        by (auto simp add: step_simps)
        
      define vis where "vis = (callsInTransaction S' txns \<down> happensBefore S')"
        
      show "\<not> invariant_all S''"  
      proof (auto simp add: invariant_all_def, rule exI[where x=vis], intro conjI)
        from invFail
        show "\<not> invariant (prog S') (invContextVis S' vis)"
          by (simp add: vis_def) 
          
        
        have "state_wellFormed S'"
          using state_wellFormed_combine state_wf step.steps by blast
          
        show "consistentSnapshot S' vis"
          apply (auto simp add: vis_def)
          using wellFormed_state_consistent_snapshot
          by (smt \<open>S' ~~ (s, AInvcheck txns False) \<leadsto> S''\<close> \<open>state_wellFormed S'\<close> consistentSnapshot_txns mem_Collect_eq step_elim_AInvcheck subsetI)
      qed    
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
      by simp 
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
        thus "P xs'" using `xs' = ys@[x]` by simp
      qed
    qed
  qed
  thus "P xs"
    by simp
qed  

lemma smallestPrefix_exists:
fixes tr :: "'a list"
  and  x :: 'b
assumes example: "P tr x"
shows "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not>isPrefix tr' tr)"
using example proof (induct tr arbitrary: x rule: prefix_induct)
  case Nil
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="x"], auto)
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
    thus "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
      by (rule snoc.IH)
  next 
    case False
    hence noPrefix: "\<not>isPrefix tr' xs" if "P tr' x'" for tr' x'
      using that by blast
      
    show " \<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
    proof (rule exI[where x="xs@[a]"], rule exI[where x=x], intro conjI allI impI; (elim conjE)?)
      show "P (xs @ [a]) x"
        using snoc.prems .
      fix tr' x'
      assume "P tr' x'"
      hence "\<not>isPrefix tr' xs"
        using False by blast
      fix tr' x'
      assume a0: "P tr' x'"
         and a1: "tr' \<noteq> xs @ [a]"
      
      show "\<not> isPrefix tr' (xs @ [a])"
        by (metis False a0 a1 butlast_snoc isPrefix_def not_le take_all take_butlast)
    qed    
  qed 
qed
    
lemma programCorrect_s_inv_initial:
assumes "programCorrect_s program"
shows "invariant_all (initialState program)"
proof (rule ccontr)
  assume "\<not> invariant_all (initialState program)"
  
  text {* from invariant failure, start some procedure, directly get false in there ??? *}
  
  from assms
  show False
    apply (auto simp add: programCorrect_s_def)
    oops


text {*
When a program is correct in the single invocation semantics, 
it is also correct when executed in the concurrent interleaving semantics.
*}
theorem show_correctness_via_single_session:
assumes works_in_single_session: "programCorrect_s program"
    and inv_init: "invariant_all (initialState program)"
shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving)
  text {* Assume we have a trace and a final state S *}
  fix trace S
  text {* Such that executing the trace finishes in state S. *}
  assume steps: "initialState program ~~ trace \<leadsto>* S"
  
  text {* We can assume the trace is packed. *}
  assume packed: "packed_trace trace"
  
  text {* We may also assume that there are no failures *}
  assume noFail: "\<And>s. (s, AFail) \<notin> set trace"
  
  text {* We show that the trace must be correct (proof by contradiction). *}
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"
    
    text {* If the trace is incorrect, there must be a failing invariant check in the trace: *}
    from this obtain s txns where "(s, AInvcheck txns False) \<in> set trace"
       using steps by (auto simp add: traceCorrect_def)
    
    obtain tr' S_fail
       where "isPrefix tr' trace"
         and "initialState program ~~ tr' \<leadsto>* S_fail"
         and "\<not> invariant_all S_fail"
      using \<open>(s, AInvcheck txns False) \<in> set trace\<close> invCheck_to_failing_state state_wellFormed_init steps by blast
    
    text {* No take the first state where the invariant fails *}
    from this
    obtain tr'_min S_fail_min
       where tr'_min_prefix: "isPrefix tr'_min trace"
         and S_fail_min_steps:"initialState program ~~ tr'_min \<leadsto>* S_fail_min"
         and S_fail_min_fail: "\<not> invariant_all S_fail_min"    
         and S_fail_min_min: "\<And>tr' S_fail. \<lbrakk>isPrefix tr' trace; initialState program ~~ tr' \<leadsto>* S_fail; \<not> invariant_all S_fail; tr' \<noteq> tr'_min\<rbrakk> \<Longrightarrow> \<not>isPrefix tr' tr'_min"
      using smallestPrefix_exists[where P="\<lambda>tr x. isPrefix tr trace \<and> (initialState program ~~ tr \<leadsto>* x) \<and> \<not> invariant_all x"]
      by metis
    
    text {* Next get the invocation start before the failure *}  
      
    find_theorems "(\<exists>x y. ?P x y) \<longleftrightarrow> (\<exists>y x. ?P x y)"
    
      
    obtain tr'_s S_fail_s s'
      where "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        and "\<exists>a. (a, False) \<in> set tr'_s"
    proof (atomize_elim)
      have "\<exists>tr'_s S_fail_s s'. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
      proof (rule convert_to_single_session_trace_invFail[OF `initialState program ~~ tr' \<leadsto>* S_fail`])
        show "state_wellFormed (initialState program)" by simp
        show "packed_trace tr'"
          using \<open>isPrefix tr' trace\<close> packed prefixes_are_packed by blast
        show "\<And>s'. (s', AFail) \<notin> set tr'"
          using `isPrefix tr' trace` noFail apply (auto simp add: isPrefix_def) (* IMPROVE extract lemma for isPrefix with \<in> or \<subseteq>*)
          by (metis in_set_takeD)
        show "invariant_all (initialState program)"
          using inv_init .
        show "\<not> invariant_all S_fail"
          by (simp add: \<open>\<not> invariant_all S_fail\<close>)
      qed
      thus "\<exists>s' tr'_s S_fail_s. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
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
        using `initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s` .
    qed    
    
    with not_correct
    show False ..
  qed
qed  
   
unused_thms


end
