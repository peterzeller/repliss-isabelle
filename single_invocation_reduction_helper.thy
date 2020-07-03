theory single_invocation_reduction_helper
  imports no_failing_invchecks packed_no_fails consistency
begin

definition contextSwitchInTransaction where
"contextSwitchInTransaction tr i_begin i_switch \<equiv> 
  \<exists>invoc tx txns.
    i_begin < i_switch
  \<and> i_switch < length tr 
  \<and> tr!i_begin = (invoc, ABeginAtomic tx txns)
  \<and> (\<forall>j. i_begin<j \<and> j<i_switch \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic) )
  \<and> allowed_context_switch (get_action (tr!i_switch))
"

definition contextSwitchesInTransaction :: "('proc, 'op, 'any) trace \<Rightarrow> bool" where
"contextSwitchesInTransaction tr \<equiv> \<exists>i_begin i_switch. contextSwitchInTransaction tr i_begin i_switch"


lemma contextSwitchesInTransaction_alt_def:
  "\<not>contextSwitchesInTransaction tr \<longleftrightarrow> (\<forall>i k invoc. 
    i < k \<and> k \<le> length tr 
   \<and> (\<exists>tx txns.  tr!i = (invoc, ABeginAtomic tx txns))
   \<and> (\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic) )
   \<longrightarrow> (\<forall>j. i < j \<and> j < k \<longrightarrow>  \<not> allowed_context_switch (get_action (tr!j))))" (is "?l \<longleftrightarrow> ?r")
proof 
  assume l: "?l"

  show "?r"
  proof (intro allI conjI impI)
    fix i k invoc j
    assume a0: "i < k \<and>         k \<le> length tr \<and>         (\<exists>tx txns. tr ! i = (invoc, ABeginAtomic tx txns)) \<and> (\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic))"
      and a1: "i < j \<and> j < k"

    have "\<not> contextSwitchInTransaction tr i j"
      using contextSwitchesInTransaction_def l by blast

    thus "\<not> allowed_context_switch (get_action (tr ! j))"
      using a0 a1
      by (auto simp add: contextSwitchInTransaction_def)
  qed
next
  assume r: ?r

  show "?l"
  proof (auto simp add:  contextSwitchesInTransaction_def)
    fix i j
    assume a0: "contextSwitchInTransaction tr i j"

    from r[rule_format, where i=i and j = j and k="Suc j"]
    show "False"
      using a0 less_antisym
      by (auto simp add: contextSwitchInTransaction_def, fastforce)
  qed
qed



lemma use_noContextSwitchesInTransaction:
  assumes a0: "\<not>contextSwitchesInTransaction tr"
    and a1: " tr!i = (invoc, ABeginAtomic tx txns)"
    and a2: "i < k" 
    and a3: "k \<le> length tr "
    and a4: "\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic)"
    and a5: "i < j"
    and a6: "j < k"
  shows "\<not>allowed_context_switch (get_action (tr!j))"
proof (simp add: allowed_context_switch_def; intro conjI allI)

  show "get_action (tr ! j) \<noteq> ABeginAtomic txId txns" for txId txns
    by (metis (full_types) a0 a1 a2 a3 a4 a5 a6 allowed_context_switch_simps(3) contextSwitchesInTransaction_alt_def)

  show " get_action (tr ! j) \<noteq> AInvoc p " for p 
    by (metis (full_types) a0 a1 a2 a3 a4 a5 a6 allowed_context_switch_simps(6) contextSwitchesInTransaction_alt_def)
qed



lemma prefixes_noContextSwitchesInTransaction:
  assumes "\<not>contextSwitchesInTransaction tr'" 
    and "isPrefix tr tr'"
  shows "\<not>contextSwitchesInTransaction tr"
proof (auto simp add: contextSwitchesInTransaction_alt_def)
fix i k j invoc tx txns
assume a0: "k \<le> length tr"
   and a1: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
   and a2: "tr ! i = (invoc, ABeginAtomic tx txns)"
   and a3: "i < j"
   and a4: "j < k"
   and a5: "allowed_context_switch (get_action (tr ! j))"


  have "\<not>allowed_context_switch (get_action (tr' ! j))"
  proof (rule use_noContextSwitchesInTransaction[OF \<open>\<not>contextSwitchesInTransaction tr'\<close>, where i=i and j=j and k=k])
    show "tr' ! i = (invoc, ABeginAtomic tx txns)"
      using a0 a2 a3 a4 assms(2) isPrefix_same by fastforce
    show "i < j " using a3 .
    show "j < k" using a4 .
    show "i < k"
      using a3 a4 less_trans by blast 
    show " k \<le> length tr'"
      by (meson a0 assms(2) isPrefix_len leD le_trans nat_le_linear)
    show " \<forall>j. i < j \<and> j < k \<longrightarrow> tr' ! j \<noteq> (invoc, AEndAtomic)"
      using a0 a1 assms(2) isPrefix_same by fastforce
  qed
  then show "False"
    using a0 a4 a5 assms(2) isPrefix_same by fastforce
qed

lemma packed_trace_prefix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace xs"
  using assms isPrefix_appendI prefixes_are_packed by blast

lemma packed_trace_postfix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace ys"
  using assms  proof (auto simp add: packed_trace_def )
  fix i
  assume a0: "\<forall>i>0. i < length xs + length ys \<longrightarrow>
                 get_invoc ((xs @ ys) ! (i - Suc 0)) \<noteq> get_invoc ((xs @ ys) ! i) \<longrightarrow>
                 allowed_context_switch (get_action ((xs @ ys) ! i))"
    and a1: "0 < i"
    and a2: "i < length ys"
    and a3: "get_invoc (ys ! (i - Suc 0)) \<noteq> get_invoc (ys ! i)"

  have "(i + length xs) < length xs + length ys "
    by (simp add: a2)

  moreover have "get_invoc ((xs @ ys) ! ((i + length xs) - Suc 0)) \<noteq> get_invoc ((xs @ ys) ! (i + length xs))"
    using a1 a3 by (auto simp add: nth_append)

  ultimately have 
    "allowed_context_switch (get_action ((xs @ ys) ! (i + length xs)))"
    using a0 a1 by simp

  from this
  show "allowed_context_switch (get_action (ys ! i))"
    by (auto simp add: nth_append)
qed

lemma packed_trace_take:
  assumes "packed_trace tr"
  shows "packed_trace (take i tr)"
  by (metis append_take_drop_id assms packed_trace_prefix)


lemma packed_trace_drop:
  assumes "packed_trace tr"
  shows "packed_trace (drop i tr)"
  by (metis append_take_drop_id assms packed_trace_postfix)






lemma noContextSwitchesInTransaction_when_packed_and_all_end:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "allTransactionsEnd tr"
    and "packed_trace tr"
    and noFail: "\<And>i. (i, ACrash) \<notin> set tr"
    and wf: "state_wellFormed S"
  shows "\<not>contextSwitchesInTransaction tr"
proof (auto simp add: contextSwitchesInTransaction_alt_def)
  fix i k j invoc tx txns
  assume a0: "k \<le> length tr"
    and a1: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and a3: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and a4: "i < j"
    and a5: "j < k"
    and a6: "allowed_context_switch (get_action (tr ! j))"


  obtain j_min 
    where a4_min: "i < j_min"
      and a5_min: "j_min < k"
      and a6_min: "allowed_context_switch (get_action(tr!j_min))"
      and j_min_min: "\<forall>j. i<j \<and> j<k \<and> allowed_context_switch (get_action (tr ! j)) \<longrightarrow> j_min \<le> j"
  proof (atomize_elim,
    rule exI[where x="Least (\<lambda>j. i<j \<and> j<k \<and> allowed_context_switch (get_action (tr ! j)))"],
    rule LeastI2_wellorder_ex, auto)
    show "\<exists>x>i. x < k \<and> allowed_context_switch (get_action (tr ! x))"
      using a4 a5 a6 by auto
  qed

  have tr_split: "tr = take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr"
    using a0 a5_min id_take_nth_drop less_le_trans by (auto, blast)
  with steps have tr_split_steps: "S ~~ take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr \<leadsto>* S'" by simp
  from this
  obtain S_j_min_pre S_j_min 
    where S_j_min_pre_steps: "S ~~ take j_min tr \<leadsto>* S_j_min_pre"
      and j_min_step: "S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min"
      and S_j_min_steps: "S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'"
    by (auto simp add: steps_append steps_appendFront  )


  have S_j_min_pre_wf: "state_wellFormed S_j_min_pre"
    by (meson S_j_min_pre_steps local.wf noFail rev_subsetD set_take_subset state_wellFormed_combine)

  then have "state_wellFormed S_j_min"
    using S_j_min_pre_steps j_min_step local.wf state_wellFormed_combine steps_step
    by (metis (no_types, lifting) append_assoc append_same_eq append_take_drop_id in_set_takeD noFail tr_split) 



  \<comment> \<open>we are still in a transaction:\<close>
  have currentTx: "currentTx S_j_min_pre invoc \<triangleq> tx"
    using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close>
      
  proof (rule currentTx[THEN iffD1])
    show "i < length (take j_min tr)"
      using a0 a4_min a5_min by auto

    show "take j_min tr ! i = (invoc, ABeginAtomic tx txns)"
      using \<open>i < length (take j_min tr)\<close> a1 by auto

    show " \<forall>j. i < j \<and> j < length (take j_min tr) \<longrightarrow>
        take j_min tr ! j \<noteq> (invoc, AEndAtomic) \<and> take j_min tr ! j \<noteq> (invoc, ACrash)"
      using a3 a5_min noFail nth_mem by fastforce
  qed

  then have ls: "localState S_j_min_pre invoc \<noteq> None"
    using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> inTransaction_localState local.wf state_wellFormed_combine
    using S_j_min_pre_wf by blast


  with \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close> 
    and \<open>allowed_context_switch (get_action(tr!j_min))\<close>
  have "get_invoc (tr!j_min) \<noteq> invoc"
    by (auto simp add: step.simps currentTx allowed_context_switch_simps)



  \<comment> \<open>there must be an endAtomic for the beginAtomic\<close>
  from \<open>allTransactionsEnd tr\<close> 
  obtain i_end 
    where "tr!i_end = (invoc, AEndAtomic)" and "i_end \<ge> k" and "i_end < length tr"
  proof (auto simp add: allTransactionsEnd_def, atomize_elim)
    assume a0: "\<forall>i j. j < length tr \<longrightarrow> (\<exists>tx txns. tr ! j = (i, ABeginAtomic tx txns)) \<longrightarrow> 
           (\<exists>k>j. k < length tr \<and> tr ! k = (i, AEndAtomic))"

    have "\<exists>k>i. k < length tr \<and> tr ! k = (invoc, AEndAtomic)"
    proof (rule a0[rule_format, where j=i and i=invoc])
      show "i < length tr"
        using a4_min not_le tr_split by fastforce
      show "\<exists>tx txns. tr ! i = (invoc, ABeginAtomic tx txns)"
        using a1 by auto
    qed

    thus "\<exists>i_end. tr ! i_end = (invoc, AEndAtomic) \<and> k \<le> i_end \<and> i_end < length tr"
      using a3 less_imp_le not_le by (auto, blast)
  qed


  \<comment> \<open>this means, we must go back to invoc. Take the first index where we go back to invoc\<close>
  from this
  obtain back_min 
    where "back_min > j_min"
      and "back_min \<le> length tr"
      and "get_invoc (tr!back_min) = invoc"
      and back_min_min: "\<forall>i. i > j_min \<and> i < length tr \<and> get_invoc (tr!i) = invoc \<longrightarrow> i\<ge> back_min"
  proof (atomize_elim, intro exI[where x="Least (\<lambda>i. i > j_min \<and> i < length tr \<and> get_invoc (tr!i) = invoc)"] conjI)
    assume a0: "tr ! i_end = (invoc, AEndAtomic)"
      and a1: "k \<le> i_end"
      and a2: "i_end < length tr"
      and a3: "tr ! i_end = (invoc, AEndAtomic)"
      and a4: "k \<le> i_end"
      and a5: "i_end < length tr"



    have "i_end>j_min"
      using a1 a5_min order.strict_trans2 by blast 

    moreover have "get_invoc (tr ! i_end) = invoc"
      by (simp add: a0)

    ultimately
    have eX: "\<exists>x>j_min. x < length tr \<and> get_invoc (tr ! x) = invoc"
      using a2 by auto

    show "j_min < (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc)"
      using eX by (rule LeastI2_wellorder_ex, auto)

    show "(LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc) \<le> length tr"
      using eX by (rule LeastI2_wellorder_ex, auto)

    show "get_invoc (tr ! (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc)) = invoc"
      using eX by (rule LeastI2_wellorder_ex, auto)



    show "\<forall>i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc \<longrightarrow> (LEAST i. j_min < i \<and> i < length tr \<and> get_invoc (tr ! i) = invoc) \<le> i"
    proof auto

      show "(LEAST ia. j_min < ia \<and> ia < length tr \<and> get_invoc (tr ! ia) = get_invoc (tr ! i)) \<le> i"
        if c0: "j_min < i"
          and c1: "i < length tr"
          and c2: "invoc = get_invoc (tr ! i)"
        for  i
        by (simp add: Least_le c0 c1)
    qed
  qed

  have "back_min < length tr"
    by (metis \<open>back_min \<le> length tr\<close> \<open>i_end < length tr\<close> \<open>k \<le> i_end\<close> \<open>tr ! i_end = (invoc, AEndAtomic)\<close> a5_min back_min_min fst_conv leD le_imp_less_or_eq less_le_trans)


  \<comment> \<open>this must be a valid context switch, since it is the first to change back\<close>
  from \<open>packed_trace tr\<close>
  have "allowed_context_switch (get_action (tr ! back_min))"
  proof (rule use_packed_trace)
    show "0 < back_min"
      using \<open>j_min < back_min\<close> gr_implies_not0 by blast

    show "back_min < length tr"
      by (simp add: \<open>back_min < length tr\<close>)
    have "get_invoc (tr ! (back_min - 1)) \<noteq> invoc"
      using back_min_min[rule_format, where i="back_min-1"]
       \<open>back_min < length tr\<close> \<open>get_invoc (tr ! j_min) \<noteq> invoc\<close> \<open>j_min < back_min\<close> not_less_less_Suc_eq by fastforce

    then show "get_invoc (tr ! (back_min - 1)) \<noteq> get_invoc (tr ! back_min)"
      by (auto simp add: \<open>get_invoc (tr!back_min) = invoc\<close>)
  qed

  \<comment> \<open>but since we are already in a transaction, that cannot work\<close>

  have "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ drop back_min tr"
    by (auto simp add: Suc_leI \<open>back_min \<le> length tr\<close> \<open>j_min < back_min\<close> min.absorb2 min_diff nth_append add.commute intro: nth_equalityI)
  then have "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr"
    using Cons_nth_drop_Suc \<open>back_min < length tr\<close> by fastforce

  with \<open>S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'\<close>
  have "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr \<leadsto>* S'"
    by force
  from this
  obtain S_back_min_pre S_back_min
    where S_back_min_pre_steps: "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre"
      and back_min_step: "S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min"
      and S_back_min_steps: "S_back_min ~~ drop (Suc back_min) tr \<leadsto>* S'"
    by  (auto simp add: steps_append steps_appendFront )


  from S_back_min_pre_steps \<open>state_wellFormed S_j_min\<close>
  have "state_wellFormed S_back_min_pre"
    by (meson state_wellFormed_combine in_set_dropD in_set_takeD noFail)

  from \<open>currentTx S_j_min_pre invoc \<triangleq> tx\<close>
  have "currentTx S_j_min invoc \<triangleq> tx"
    using \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close> 
    using \<open>get_invoc (tr ! j_min) \<noteq> invoc\<close> by (auto simp add: step.simps )


  from  \<open>S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre\<close>
  have "currentTx S_back_min_pre invoc \<triangleq> tx"
    
  proof (rule currentTx_unchangedInternalSteps4(1))
    show "currentTx S_j_min invoc \<triangleq> tx"
      by (simp add: \<open>currentTx S_j_min invoc \<triangleq> tx\<close>) 
    show "state_wellFormed S_j_min"
    proof (rule state_wellFormed_combine[OF wf])
      show " S ~~ take j_min tr @ [tr ! j_min] \<leadsto>* S_j_min"
        using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> \<open>S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min\<close>
        using steps_step by blast 
      show "\<And>i. (i, ACrash) \<notin> set (take j_min tr @ [tr ! j_min])"
        using noFail \<open>back_min < length tr\<close> \<open>j_min < back_min\<close> 
        by (auto, metis a6_min allowed_context_switch_simps(8) snd_conv, meson in_set_takeD)
    qed

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, AEndAtomic)"
      by (auto simp add: in_set_conv_nth,
       metis add.commute add_Suc back_min_min fst_conv less_add_Suc1 less_diff_conv linorder_not_le)

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, ACrash)"
      by (meson in_set_dropD in_set_takeD noFail)
  qed





  then have "localState S_back_min_pre invoc \<noteq> None"
    using \<open>state_wellFormed S_back_min_pre\<close>
    using inTransaction_localState by blast



  \<comment> \<open>a contradiction\<close>
  with \<open>S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min\<close>
    and \<open>allowed_context_switch (get_action (tr ! back_min))\<close>
    and \<open>get_invoc (tr ! back_min) = invoc\<close>
    and \<open>currentTx S_back_min_pre invoc \<triangleq> tx\<close>
    and \<open>localState S_back_min_pre invoc \<noteq> None\<close>
  show "False"
    by (auto simp add:step.simps allowed_context_switch_simps)

qed




lemma only_one_commmitted_transaction_h:
  assumes  steps: "S ~~ tr \<leadsto>* S'"
    and wf: "state_wellFormed S"
    and packed: "packed_trace tr"
    and status: "txStatus S' tx \<triangleq> Uncommitted"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noSwitch: "\<not>contextSwitchesInTransaction tr"
    and initial: "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
  shows "(currentTx S' (get_invoc (last tr)) \<triangleq> tx) 
      \<and> (\<exists>i txns. i<length tr \<and> tr!i = (get_invoc (last tr), ABeginAtomic tx txns)
           \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)))" 
  using steps packed status noFails noSwitch proof (induct arbitrary: tx  rule: steps_induct)
  case initial
  with \<open>txStatus S tx \<noteq> Some Uncommitted\<close> show ?case by blast
next
  case (step S' tr a S'' tx)

  from \<open>\<not>contextSwitchesInTransaction (tr @ [a])\<close>
  have noContextSwitch: "\<not>contextSwitchesInTransaction tr"
    using isPrefix_appendI prefixes_noContextSwitchesInTransaction by blast

  { 
    assume "txStatus S' tx \<triangleq> Uncommitted"
    with \<open> S ~~ tr \<leadsto>* S'\<close>
    have IH: "currentTx S' (get_invoc (last tr)) \<triangleq> tx 
          \<and> (\<exists>i txns. i<length tr \<and> tr!i = (get_invoc (last tr), ABeginAtomic tx txns)
                   \<and> (\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)))"
      using isPrefix_appendI prefixes_are_packed step.IH \<open>\<And>s. (s, ACrash) \<notin> set (tr @ [a])\<close> \<open>packed_trace (tr @ [a])\<close> noContextSwitch
      by (metis butlast_snoc in_set_butlastD) 



    obtain i' action where a_split[simp]: "a = (i',action)"
      by fastforce

    from IH
    have IH1: "currentTx S' (get_invoc (last tr)) \<triangleq> tx"
      by blast


    from IH
    obtain i txns
      where i1: "i<length tr"
        and i2: "tr!i = (get_invoc (last tr), ABeginAtomic tx txns)"
        and i3: "\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (get_invoc (last tr), AEndAtomic)"
      by fastforce

    then have "(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)"
      by (simp add: nth_append_first)

    have "a \<noteq> (get_invoc (last tr), AEndAtomic)" 
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open>txStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps IH1 split: if_splits )


    from \<open>\<not>contextSwitchesInTransaction (tr @ [a])\<close> \<open>(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)\<close>
    have "\<not>allowed_context_switch (get_action ((tr@[a])!length tr))" 
    proof (rule use_noContextSwitchesInTransaction)
      show "\<forall>j. i < j \<and> j < Suc (length tr) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last tr), AEndAtomic)"
        using \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close> i3 less_Suc_eq nth_append_first by fastforce
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

    then have i'_simps: "i' = get_invoc (last tr)"
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"]
      apply (auto simp add: nth_append)
      by (metis i1 One_nat_def gr_implies_not_zero last_conv_nth length_0_conv)




    from \<open>S' ~~ a \<leadsto> S''\<close> IH1
    have "currentTx S'' (get_invoc (last (tr@[a]))) \<triangleq> tx"
      using \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close>  \<open>\<And>s. (s, ACrash) \<notin> set (tr @ [a])\<close> by (auto simp add: step.simps  i'_simps)

    moreover have "(\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      apply (rule exI[where x=i])
      apply (rule exI[where x=txns])
      apply (auto simp add: )
      using i1 less_SucI apply blast
      using \<open>(tr @ [a]) ! i = (get_invoc (last tr), ABeginAtomic tx txns)\<close> a_split i'_simps apply blast
      by (metis \<open>a \<noteq> (get_invoc (last tr), AEndAtomic)\<close> a_split i'_simps i3 less_SucE nth_append_first nth_append_length)

    ultimately have "currentTx S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      by simp
  }
  moreover
  {
    assume "txStatus S' tx \<noteq> Some Uncommitted"
    then have  "currentTx S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
      using \<open>S' ~~ a \<leadsto> S''\<close> \<open> txStatus S'' tx \<triangleq> Uncommitted\<close>
      by (auto simp add: step.simps split: if_splits)
  }
  ultimately show "currentTx S'' (get_invoc (last (tr @ [a]))) \<triangleq> tx \<and>
           (\<exists>i txns. i < length (tr @ [a]) \<and>
                     (tr @ [a]) ! i = (get_invoc (last (tr @ [a])), ABeginAtomic tx txns) \<and>
                     (\<forall>j. i < j \<and> j < length (tr @ [a]) \<longrightarrow> (tr @ [a]) ! j \<noteq> (get_invoc (last (tr @ [a])), AEndAtomic)))"
    by auto
qed




lemma at_most_one_active_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommitted:  "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
    and noCtxtSwitchInTx: "\<not>contextSwitchesInTransaction tr"
  shows "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTx S' i = Some tx)
       \<and> (\<forall>i j. currentTx S' i \<noteq> None \<and> currentTx S' j \<noteq> None \<longrightarrow> i = j)"
  using steps  packed noFails noCtxtSwitchInTx proof (induct rule: steps_induct)
  case initial
  then show ?case 
    using wellFormed_currentTx_unique_h(2) noUncommitted S_wellformed open_transactions_empty by (auto simp add:  allowed_context_switch_simps)

next
  case (step S' tr a S'')

  have IH: "(\<forall>i tx. (i,tx) \<in> openTransactions tr \<longleftrightarrow> currentTx S' i = Some tx)
            \<and> (\<forall>i j. currentTx S' i \<noteq> None \<and> currentTx S' j \<noteq> None \<longrightarrow> i = j)"
  proof (rule step)
    show "packed_trace tr"
      using packed_trace_prefix step.prems(1) by auto
    show "\<And>s. (s, ACrash) \<notin> set tr"
      using step.prems(2) by auto
    show "\<not>contextSwitchesInTransaction tr"
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

      have "\<not> allowed_context_switch (get_action ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>\<not>contextSwitchesInTransaction (tr @ [a])\<close>])
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
    case (dbop s ls f Op  ls' t c res vis)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (invocation s proc initialState impl)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (return s ls f res)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  next
    case (crash s ls)
    then show ?thesis
      using step.prems(2) by auto 
  next
    case (invCheck res s)
    then show ?thesis using IH by (auto simp add: open_transactions_append_one)
  qed
qed


lemma at_most_one_current_tx:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and noCtxtSwitchInTx: "\<not>contextSwitchesInTransaction tr"
    and packed: "packed_trace tr"
    and wf: "state_wellFormed S"
    and noFails: "\<And>s. (s, ACrash) \<notin> set tr"
    and noUncommitted:  "\<And>tx. txStatus S tx \<noteq> Some Uncommitted"
  shows "\<forall>i. currentTx S' i \<noteq> None \<longrightarrow> i = get_invoc (last tr)"
  using steps noCtxtSwitchInTx packed  noFails
proof (induct rule: steps_induct)
  case initial
  then have "currentTx S i = None" for i
    using noUncommitted
    by (meson local.wf option.exhaust wellFormed_currentTxUncommitted) 
  then show ?case
    by simp
next
  case (step S' tr a S'')
  have noFail_tr: "(i, ACrash) \<notin> set tr" for i
    using  `\<And>s. (s, ACrash) \<notin> set (tr@[a])` by auto

  have IH: "\<forall>i. currentTx S' i \<noteq> None \<longrightarrow> i = get_invoc (last tr)"
  proof (rule step)
    show " \<not>contextSwitchesInTransaction tr"
      using isPrefix_appendI prefixes_noContextSwitchesInTransaction step.prems(1) by blast
    show "packed_trace tr"
      using packed_trace_prefix step.prems(2) by blast
    show "\<And>s. (s, ACrash) \<notin> set tr"
      using noFail_tr by auto
  qed

  

  have noFail_a: "get_action a \<noteq> ACrash"
    using  `\<And>s. (s, ACrash) \<notin> set (tr@[a])`
    by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 




  show ?case
  proof (cases tr)
    case Nil
    then have "currentTx S' i = None" for i
      using noUncommitted \<open>S ~~ tr \<leadsto>* S'\<close>
      apply (auto simp add: steps_empty)
      by (metis local.wf option.exhaust wellFormed_currentTx_unique_h(2))

    with \<open>S' ~~ a \<leadsto> S''\<close>
    show ?thesis 
      by (auto simp add: step.simps split: if_splits)

  next
    case (Cons x xs)
    then have tr_nonempty[simp]: "tr \<noteq> []" by simp

    have last_same: "get_invoc (last tr) = get_invoc a" if "\<not> allowed_context_switch (get_action a)" 
      using use_packed_trace[OF \<open>packed_trace (tr@[a])\<close>, where i="length tr"] that
      by (auto simp add: nth_append last_conv_nth)

    have no_tx_if_context_switch: "currentTx S' i = None" if "allowed_context_switch (get_action a)" for i
    proof (rule ccontr, clarsimp)
      fix tx
      assume tx: "currentTx S' i \<triangleq> tx"

      have "currentTx S i = None"
        by (meson local.wf noUncommitted option.exhaust wellFormed_currentTx_unique_h(2))


      from tx
      obtain ib txns
        where ib: "tr!ib = (i, ABeginAtomic tx txns)"
          and ib_len: "ib < length tr" 
          and ib_no_end: "\<forall>j. ib<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (i, AEndAtomic)"
        using \<open>currentTx S i = None\<close> \<open>S ~~ tr \<leadsto>* S'\<close> currentTx_exists_beginAtomic local.wf  noFail_tr by blast


      have "\<not> allowed_context_switch (get_action ((tr @ [a]) ! length tr))"
      proof (rule use_noContextSwitchesInTransaction[OF \<open>\<not>contextSwitchesInTransaction (tr @ [a])\<close>, where j="length tr"])
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
      using IH last_same no_tx_if_context_switch
      by (auto simp add: step.simps allowed_context_switch_simps split: if_splits)
  qed
qed



lemma chooseSnapshot_transactionConsistent_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> txStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and a3: "transactionConsistent (callOrigin S) (txStatus S) vis"
  shows "transactionConsistent (callOrigin S) (txStatus S) snapshot"
  using a1 a3 apply (auto simp add: chooseSnapshot_def downwardsClosure_def transactionConsistent_def callsInTransactionH_contains)
   apply (auto simp add: split: option.splits)
  apply (auto simp add: transactionConsistent_committed_def)[1]
  using all_committed apply blast
  using all_committed apply blast
  apply (auto simp add: transactionConsistent_atomic_def callsInTransactionH_contains split: option.splits)[1]
  using hb_callOrigin option.distinct(1) apply force
  by (metis (no_types, lifting) hb_tr option.distinct(1) option.sel)
  


lemma chooseSnapshot_consistentSnapshot_preserve:
  assumes a1: "chooseSnapshot snapshot vis S"
    and hb_tr: "\<And>x y z tx. \<lbrakk>(x,z)\<in>happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y,z)\<in>happensBefore S "
    and all_committed: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> txStatus S tx \<triangleq> Committed"
    and hb_callOrigin: "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb,ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
    and hb_trans: "trans (happensBefore S)"
    and callOrigin_ex: "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> \<exists>ci. calls S c \<triangleq> ci"
    and a3: "consistentSnapshot S vis"
  shows "consistentSnapshot S snapshot"
proof (auto simp add: consistentSnapshotH_def)
  show "causallyConsistent (happensBefore S) snapshot"
    using a1 a3 chooseSnapshot_causallyConsistent_preserve consistentSnapshotH_def hb_trans by blast
  from a1
  show "transactionConsistent (callOrigin S) (txStatus S) snapshot"
  proof (rule chooseSnapshot_transactionConsistent_preserve)
    show " \<And>x y z tx. \<lbrakk>(x, z) \<in> happensBefore S; callOrigin S x \<triangleq> tx; callOrigin S y \<triangleq> tx; callOrigin S z \<noteq> Some tx\<rbrakk> \<Longrightarrow> (y, z) \<in> happensBefore S"
      using hb_tr by blast
    show "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> txStatus S tx \<triangleq> Committed"
      by (simp add: all_committed)
    show "\<And>ca cb tx. \<lbrakk>callOrigin S ca \<triangleq> tx; (cb, ca) \<in> happensBefore S\<rbrakk> \<Longrightarrow> \<exists>tx. callOrigin S cb \<triangleq> tx"
      using hb_callOrigin by blast
    show "transactionConsistent (callOrigin S) (txStatus S) vis"
      using a3 consistentSnapshotH_def by blast
  qed
  show "\<And>x. x \<in> snapshot \<Longrightarrow> \<exists>y. calls S x \<triangleq> y"
    using a1 apply (auto simp add: chooseSnapshot_def)
    apply (meson a3 consistentSnapshotH_def in_dom)
    by (smt assms(6) callsInTransactionH_def downwardsClosure_in hb_callOrigin mem_Collect_eq)
qed









lemma wf_transactionConsistent_noTx:
  assumes wf: "state_wellFormed S"
and "visibleCalls S i \<triangleq> vis"
and "currentTx S i = None"
shows "transactionConsistent (callOrigin S) (txStatus S) vis"
proof (rule show_transactionConsistent)
  show "txStatus S tx \<triangleq> Committed" if "c \<in> vis" and "callOrigin S c \<triangleq> tx" for c tx
    using assms(2) assms(3) local.wf that(1) that(2) wellFormed_state_transaction_consistent(1) by fastforce

  show "\<And>c1 c2. \<lbrakk>c1 \<in> vis; callOrigin S c1 = callOrigin S c2\<rbrakk> \<Longrightarrow> c2 \<in> vis"
    using assms(2) local.wf wellFormed_state_transaction_consistent(2) by blast

qed

end