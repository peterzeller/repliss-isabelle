section "Packed Traces"
theory packed_traces
imports commutativity
begin


text "In this section we show that traces can be packed.
Intuitively a transaction is packed, if there are no steps from other invocations between a 
@{term ABeginAtomic} and @{term AEndAtomic} action.

The following definition defines that such a step exists at an index @{term k}.
"

definition indexInOtherTransaction :: "('proc, 'operation, 'any) trace \<Rightarrow> txid \<Rightarrow> nat \<Rightarrow> bool" where
  "indexInOtherTransaction tr tx k \<equiv> 
  \<exists>i s ntxns. 
      k<length tr 
    \<and> i<k 
    \<and> tr!i = (s, ABeginAtomic tx ntxns)  
    \<and> get_invoc (tr!k) \<noteq> s
    \<and> \<not>(\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

text "With this we can define that a trace is packed, if no such step exists:"

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
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> get_invoc (tr!j) = s) 
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
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> get_invoc (tr!j) = s) 
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
    and a4: "\<forall>j. ia \<le> j \<and> j < length tr \<longrightarrow> get_invoc (tr ! j) = sa"

  have [simp]: "ia = i"
    using a2 a0 a3 a1 by (rule uniqueTxs)



  then have [simp]: "sa = s"
    using a1 a3 by auto  
  then have a4': "\<And>j. i \<le> j \<Longrightarrow> j < length tr \<Longrightarrow> get_invoc (tr ! j) = s"  
    using a4 by auto

  show "transactionIsPacked tr tx"
    by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def,
     smt \<open>ia = i\<close> \<open>sa = s\<close> a2 a3 a4' le_eq_less_or_eq le_less_trans prod.inject uniqueTxs)
next
  fix i s ntxns
  assume a0: "i < length tr"
    and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
    and a2: "transactionIsPacked tr tx"

  from a2
  have a2': "get_invoc (tr ! k) = s \<or> (\<exists>j<k. i < j \<and> tr ! j = (s, AEndAtomic))" 
    if "k<length tr" "i<k"
    for k
    using a1 that by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)

  show "\<exists>i<length tr. \<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> get_invoc (tr ! j) = s))"  
  proof (rule exI[where x=i], (auto simp add: a0))
    show "\<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> get_invoc (tr ! j) = s))"
    proof (rule exI[where x=s], safe)
      show "\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)"
        by (simp add: a1) 
      define endPos where "endPos = (if \<exists>j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) then LEAST j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) else length tr)"
      show "\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> get_invoc (tr ! j) = s) "
      proof (rule exI[where x="endPos"], (auto simp add: endPos_def))
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) < length tr"
          by (smt less_trans neqE not_less_Least)
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> tr ! (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) = (s, AEndAtomic)"
          by (smt LeastI)
        show "\<And>j ja. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); i \<le> ja; ja < (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic))\<rbrakk> \<Longrightarrow> get_invoc (tr ! ja) = s"
          by (smt a1 a2' dual_order.strict_trans fst_conv neqE not_le not_less_Least)
        show "\<And>j. \<lbrakk>\<forall>j<length tr. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic); i \<le> j; j < length tr\<rbrakk> \<Longrightarrow> get_invoc (tr ! j) = s"
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
    and a4: "\<forall>j. ia \<le> j \<and> j < ende \<longrightarrow> get_invoc (tr ! j) = sa"
    and a5: "ende < length tr"
    and a6: "tr ! ende = (sa, AEndAtomic)"

  have a2: "ia < length tr"
    using a5 a7 less_trans by blast


  with uniqueTxs have [simp]: "ia = i"
    using a0 a1 a3 by blast

  then have [simp]: "sa = s"
    using a1 a3 by auto     

  have a4': "get_invoc (tr ! j) = s" if "i \<le> j" and "j < ende" for j
    by (auto simp add: that a4)  


  show "transactionIsPacked tr tx"
  proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
    fix k i' s' ntxns
    assume b0: "k < length tr"
      and b1: "i' < k"
      and b2: "tr ! i' = (s', ABeginAtomic tx ntxns)"
      and b3: "\<forall>j>i'. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
      and b4: "get_invoc (tr ! k) \<noteq> s'"

    have " i' < length tr"
      using b0 b1 order.strict_trans by blast 


    then have [simp]: "i' = i"
      using uniqueTxs b2 a1 a0 by blast 

    then have [simp]: "s' = s"
      using a1 b2 by auto

    have b3': "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic)"
      using b3 by simp      
    have "get_invoc (tr ! k) = s"
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
    and a1: "\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> get_invoc (tr ! i) = s"
  shows "transactionIsPacked tr tx"
proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
  fix k i s' ntxns
  assume b0: "k < length tr"
    and b1: "i < k"
    and b2: "tr ! i = (s', ABeginAtomic tx ntxns)"
    and b3: "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
    and b4: "get_invoc (tr ! k) \<noteq> s'"

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
    \<and> get_invoc (tr!k) \<noteq> s
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
    and "\<not>allowed_context_switch ACrash" 
    and "\<not>allowed_context_switch (AInvcheck invr)" by (auto simp add: allowed_context_switch_def)




lemma canSwap_when_allowed:
  assumes no_ctxt_switch: "\<not>allowed_context_switch b"
    and no_invcheck_a: "\<not>is_AInvcheck a"
    and no_invcheck_b: "\<not>is_AInvcheck b"  
    and no_fail_a: "a \<noteq> ACrash"
    and no_fail_b: "b \<noteq> ACrash"    
  shows "canSwap t a b"
  by (metis allowed_context_switch_def canSwap_cases no_ctxt_switch no_fail_a no_fail_b no_invcheck_a no_invcheck_b)




definition packed_trace :: "('proc, 'operation, 'any) trace \<Rightarrow> bool" where
  "packed_trace tr \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> get_invoc (tr!(i-1)) \<noteq> get_invoc (tr!i)
    \<longrightarrow> (allowed_context_switch (get_action (tr!i)))" 


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
  have "a' = get_action(tr!(1+length tr1))"
    using split_tr by (auto simp add: nth_append)

  moreover
  have "allowed_context_switch (get_action(tr!(1+length tr1)))"
    using packed proof (rule use_packed_trace)
    show "0 < 1 + length tr1" by simp
    show "1 + length tr1 < length tr" using split_tr by auto
    show "get_invoc (tr ! (1 + length tr1 - 1)) \<noteq> get_invoc (tr ! (1 + length tr1))" using split_tr \<open>s \<noteq> s'\<close> by (auto simp add: nth_append)
  qed
  ultimately
  show ?thesis by simp
qed  



definition packed_trace_i :: "('proc, 'operation, 'any) trace \<Rightarrow> invocId \<Rightarrow> bool" where
  "packed_trace_i tr invoc \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> get_invoc (tr!i) = invoc
    \<longrightarrow> get_invoc (tr!(i-1)) \<noteq> invoc
    \<longrightarrow> (allowed_context_switch (get_action (tr!i)))" 

lemma pack_trace_for_one_session:
  assumes steps: "initialState program ~~ tr1 \<leadsto>* C"
    and noFail: "\<And>s. (s, ACrash) \<notin> set tr1" (is "\<And>s. _ \<notin> set ?tr")
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr1 \<Longrightarrow> \<not>is_AInvcheck a "
  shows "\<exists>tr'. packed_trace_i tr' s
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. packed_trace_i tr1 s \<longrightarrow> packed_trace_i tr' s)
        \<and> (\<forall>s. (s, ACrash) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
  text \<open>By induction over the minimal index that is not packed.\<close>
proof -

  have "\<exists>tr'. 
      (\<forall>i<length tr1. \<not>(0 < i  
                      \<and>  get_invoc (tr'!(i-1)) \<noteq> s 
                      \<and> get_invoc (tr'!i) = s 
                      \<and> \<not>(allowed_context_switch (get_action(tr'!i))) )  )
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (length tr' = length tr1)
        \<and> (\<forall>s. packed_trace_i tr1 s \<longrightarrow> packed_trace_i tr' s)
        \<and> (\<forall>s. (s, ACrash) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)" (is "\<exists>tr'. ?P tr'")
  proof (rule fix_smallest_induct, auto simp add: assms disj_imp rewrite_and_implies, rename_tac tr i)

    show "\<exists>tr'. (\<forall>j\<le>i. 0 < j \<longrightarrow> get_invoc (tr' ! (j - Suc 0)) \<noteq> get_invoc (tr ! i) \<longrightarrow> get_invoc (tr' ! j) = get_invoc (tr ! i) \<longrightarrow> allowed_context_switch (get_action (tr' ! j))) \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> length tr' = length tr1 \<and> (\<forall>s. packed_trace_i tr1 s \<longrightarrow> packed_trace_i tr' s) \<and> (\<forall>s. (s, ACrash) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"
      if c0: "\<And>j. j < i \<Longrightarrow> 0 < j \<longrightarrow> get_invoc (tr ! (j - Suc 0)) \<noteq> get_invoc (tr ! i) \<longrightarrow> get_invoc (tr ! j) = get_invoc (tr ! i) \<longrightarrow> allowed_context_switch (get_action (tr ! j))"
        and c1: "i < length tr1"
        and c2: "initialState program ~~ tr \<leadsto>* C"
        and i1[simp]: "0 < i"
        and c4: "length tr = length tr1"
        and c5: "get_invoc (tr ! (i - Suc 0)) \<noteq> get_invoc (tr ! i)"
        and c6: "\<forall>s. packed_trace_i tr1 s \<longrightarrow> packed_trace_i tr s"
        and i5: "\<not> allowed_context_switch (get_action (tr ! i))"
        and c8: "s = get_invoc (tr ! i)"
        and c9: "\<forall>s. (s, ACrash) \<notin> set tr"
        and c10: "\<forall>s a. (s, a) \<in> set tr \<longrightarrow> \<not> is_AInvcheck a"
      for  tr i

    proof -

      have i2: "i<length tr"
        by (simp add: c1 c4)


      have i4: "get_invoc (tr!i) = s"
        by (simp add: c8)


      text \<open>There must be a previous action on the same invocId (at least the invocId should be there, since i is no invocId).\<close>
      obtain prev
        where prev1: "get_invoc(tr!prev) = s"
          and prev2: "prev < i"
          and prev3: "\<And>j. \<lbrakk>prev < j; j < i\<rbrakk> \<Longrightarrow> get_invoc(tr!j) \<noteq> s"
      proof (atomize_elim)
        from \<open>initialState program ~~ tr \<leadsto>* C\<close> \<open>i<length tr\<close> \<open>get_invoc (tr!i) = s\<close>
        have "\<exists>j<i. get_invoc (tr ! j) = s \<and> (\<exists>p. get_action (tr ! j) = AInvoc p)"
        proof (rule exists_invoc)
          show "\<And>p. get_action (tr ! i) \<noteq> AInvoc p"
            using allowed_context_switch_def[where action="get_action (tr ! i)"] i5 by auto 
          show "\<not> is_AInvcheck (get_action (tr ! i))"
            by (metis \<open>i < length tr\<close> c10 nth_mem prod.collapse)
        qed
        then have "\<exists>j<i. get_invoc (tr ! j) = s"
          by auto
        then have "\<exists>j. (j<i \<and> get_invoc (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> get_invoc (tr ! j') = s \<longrightarrow> j'\<le>j)"
        proof (rule exists_greatest')
          show "\<exists>bound. \<forall>j. j < i \<and> get_invoc (tr ! j) = s \<longrightarrow> j \<le> bound"
            using less_or_eq_imp_le by blast
        qed
        from this obtain j where "(j<i \<and> get_invoc (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> get_invoc (tr ! j') = s \<longrightarrow> j'\<le>j)"
          by blast
        then have "get_invoc (tr ! j) = s \<and> j < i \<and> (\<forall>j'>j. j' < i \<longrightarrow> get_invoc (tr ! j') \<noteq> s)"
          by auto

        then show "\<exists>prev. get_invoc (tr ! prev) = s \<and> prev < i \<and> (\<forall>j>prev. j < i \<longrightarrow> get_invoc (tr ! j) \<noteq> s)"  ..
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
          using i2 prev2 by auto
        show "tr ! ia = (take prev tr @ [tr ! prev] @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr) ! ia" if "ia<length tr"for ia
          using that by (auto simp add: nth_append nth_Cons'  Suc_leI less_diff_conv prev2)

      qed    


      text \<open>Because of the swap lemma we can change this to (one action from s) -- (action i form s) -- (many other actions)\<close>
      define tr' where "tr' = take prev tr @ [tr!prev, tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr"

      have tr'sameLength: "length tr' = length tr"
        using i2 prev2  by (auto simp add: tr'_def)


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
        using that prev2 antisym  prev1 c5 c8  by (auto simp add: tr'_def nth_append nth_Cons' Suc_diff_Suc numeral_2_eq_2, fastforce)
      moreover have tr'5: "tr'!x = tr!x" if "x > i" and "x < length tr" for x
        using that prev2 by (auto simp add: tr'_def nth_append nth_Cons')
      ultimately have tr'i_def: "tr'!x = (if x\<le>prev then tr!x else if x=Suc prev then tr!i else if x\<le>i then tr!(x-1) else tr!x)" if "x<length tr" for x
        by (metis antisym_conv2 not_le not_less_eq_eq that)  


      have "initialState program ~~ (take prev tr @ [tr!prev]) @ [tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr \<leadsto>* C"
      proof (rule swapMany_middle')
        show "initialState program ~~ (take prev tr @ [tr ! prev]) @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr \<leadsto>* C"
          using tr_split c2 by auto 

        show "\<And>x. x \<in> set (drop (Suc prev) (take i tr)) \<Longrightarrow> get_invoc x \<noteq> get_invoc (tr ! i)"
          using prev3 by (auto simp add: in_set_conv_nth,
              metis add.commute add_Suc_right fst_conv i4 less_add_Suc1 less_diff_conv) 

        from i5
        show "canSwap t (get_action x) (get_action (tr ! i))" if "x \<in> set (drop (Suc prev) (take i tr))" for x t
        proof (rule canSwap_when_allowed)
          from that obtain k 
            where k1: "x = tr!k" 
              and k2: "k<i" 
              and k3: "k>prev"
            by (auto simp add: in_set_conv_nth)

          then have k4: "x\<in>set tr"
            using dual_order.strict_trans i2 nth_mem by blast


          show "\<not> is_AInvcheck (get_action x)"
            by (metis c10 k4 prod.collapse)
          show "\<not> is_AInvcheck (get_action (tr ! i))"
            by (metis i2 c10 nth_mem snd_conv surj_pair)
          show "get_action x \<noteq> ACrash"
            by (metis c9 k4 prod.collapse)
          show "get_action (tr ! i) \<noteq> ACrash"
            by (metis c9 i2 nth_mem prod.collapse)
        qed  

        show "state_wellFormed (initialState program)"
          by (simp add: state_wellFormed_init)

        from noFail
        show "\<And>i. (i, ACrash) \<notin> set (take prev tr @ [tr ! prev])"
          by (metis Un_iff set_append c9 tr_split)
        from noFail
        show "\<And>ia. (ia, ACrash) \<notin> set (drop (Suc prev) (take i tr))"
          by (meson in_set_dropD in_set_takeD c9)
      qed    


      then have "initialState program ~~ tr' \<leadsto>* C"
        by (simp add: tr'_def)

      have tr'packed: "packed_trace_i tr' s" if "packed_trace_i tr s" for s
        using that Suc_leI prev2 
        by (auto simp add: packed_trace_i_def tr'i_def tr'sameLength i4 prev1,
            metis Suc_pred c8 diff_le_self le_less_Suc_eq le_zero_eq not_le_imp_less,
            metis Suc_pred c5 i2 i5 le_less_Suc_eq not_le_imp_less not_less0 not_less_iff_gr_or_eq)

      show "\<exists>tr'. (\<forall>j\<le>i. 0 < j \<longrightarrow>
                  get_invoc (tr' ! (j - Suc 0)) \<noteq> get_invoc (tr ! i) \<longrightarrow>
                  get_invoc (tr' ! j) = get_invoc (tr ! i) \<longrightarrow> allowed_context_switch (get_action (tr' ! j))) \<and>
          (initialState program ~~ tr' \<leadsto>* C) \<and>
          length tr' = length tr1 \<and>
          (\<forall>s. packed_trace_i tr1 s \<longrightarrow> packed_trace_i tr' s) \<and>
          (\<forall>s. (s, ACrash) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"
      proof (rule exI[where x=tr'], intro conjI impI allI)


        show "initialState program ~~ tr' \<leadsto>* C"
          by (simp add: \<open>initialState program ~~ tr' \<leadsto>* C\<close>)
        show "\<And>s. (s, ACrash) \<notin> set tr'"
          by (simp add: c9 tr'_sameSet)
        show "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
          using c10 tr'_sameSet by auto
        show "length tr' = length tr1"
          using c4 tr'sameLength by auto

        show "\<And>s. packed_trace_i tr1 s \<Longrightarrow> packed_trace_i tr' s"
          using c6 tr'packed by blast

        show "allowed_context_switch (get_action (tr' ! j))"
          if d0: "j \<le> i"
            and d1: "0 < j"
            and d2: "get_invoc (tr' ! (j - Suc 0)) \<noteq> get_invoc (tr ! i)"
            and d3: "get_invoc (tr' ! j) = get_invoc (tr ! i)"
          for  j
        proof (cases "j = i")
          case True
          then show ?thesis
            using c5 d3 tr'4  by (auto simp add: tr'_def nth_append nth_Cons' split: if_splits)
        next
          case False
          hence "j < i"
            using antisym_conv2 d0 by blast
          hence "allowed_context_switch (get_action (tr ! j))"
            by (smt Suc_pred c0 c1 c4 c8 d0 d1 d2 d3 diff_Suc_1 leD less_trans not_le_imp_less not_less_eq prev1 prev3 tr'i_def)

          thus "allowed_context_switch (get_action (tr' ! j))"
            using \<open>j < i\<close> c1 c4 c8 d2 d3 less_trans prev1 prev3 tr'i_def by auto
        qed
      qed
    qed
  qed

  thus ?thesis
    by (metis packed_trace_i_def)


qed


lemma packed_trace_iff_all_sessions_packed:
  "packed_trace tr \<longleftrightarrow> (\<forall>s. packed_trace_i tr s)"
  by (auto simp add: packed_trace_def packed_trace_i_def)

text \<open>Now we can just repeat fixing invocId by invocId, until all sessions are packed.\<close>
lemma pack_trace:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, ACrash) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr \<Longrightarrow> \<not>is_AInvcheck a "
  shows "\<exists>tr'. packed_trace tr'
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. (s, ACrash) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
proof -
  have "{s. \<not>packed_trace_i tr s } \<subseteq> set (map get_invoc tr)"
    by (auto simp add: packed_trace_i_def)

  then have "finite {s. \<not>packed_trace_i tr s }"
    using infinite_super by blast

  from this and assms
  show ?thesis
  proof (induct "{s. \<not>packed_trace_i tr s }" arbitrary: tr rule: finite_psubset_induct)
    case psubset

    show ?case 
    proof (cases "{s. \<not>packed_trace_i tr s } = {}")
      case True
      then have "packed_trace tr"
        by (auto simp add: packed_trace_iff_all_sessions_packed)
      then show ?thesis
        using psubset.prems by blast 
    next
      case False
      from this obtain s where "\<not> packed_trace_i tr s"
        by blast


      from \<open>initialState program ~~ tr \<leadsto>* C\<close> \<open>\<And>s. (s, ACrash) \<notin> set tr\<close> \<open>\<And>s a. (s, a) \<in> set tr \<Longrightarrow> \<not> is_AInvcheck a\<close>
      have "\<exists>tr'. packed_trace_i tr' s \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> (\<forall>s. packed_trace_i tr s \<longrightarrow> packed_trace_i tr' s) \<and> (\<forall>s. (s, ACrash) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"  
        by (rule pack_trace_for_one_session; force)

      from this
      obtain tr' 
        where tr'1: "packed_trace_i tr' s"
          and tr'2: "initialState program ~~ tr' \<leadsto>* C"
          and tr'3: "\<forall>s. packed_trace_i tr s \<longrightarrow> packed_trace_i tr' s"
          and tr'4: "\<And>s. (s, ACrash) \<notin> set tr'"
          and tr'5: "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
        by blast

      from tr'1 tr'3 \<open>\<not> packed_trace_i tr s\<close>
      have subset: "{s. \<not>packed_trace_i tr' s } \<subset> {s. \<not>packed_trace_i tr s }"
        by auto

      from subset tr'2 tr'4 tr'5
      show ?thesis 
        by (rule psubset; force)
    qed
  qed
qed




lemma pack_incorrect_trace:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, ACrash) \<notin> set tr"
    and notCorrect: "\<not>traceCorrect tr"
  shows "\<exists>tr' C'. packed_trace tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* C')
        \<and> (\<forall>s. (s, ACrash) \<notin> set tr')
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
  have "\<exists>tr'''. packed_trace tr''' \<and> (initialState program ~~ tr''' \<leadsto>* C') \<and> (\<forall>s. (s, ACrash) \<notin> set tr''') \<and> (\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a)"
  proof (rule pack_trace)
    show "\<And>s. (s, ACrash) \<notin> set tr''"
      using noFail by (auto simp add: tr'_def tr''_def dest: in_set_takeD)
    show "\<And>s a. (s, a) \<in> set tr'' \<Longrightarrow> \<not> is_AInvcheck a"
      by (auto simp add: tr''_def)
  qed    

  from this
  obtain tr'''
    where tr'''1: "packed_trace tr'''"
      and tr'''2: "initialState program ~~ tr''' \<leadsto>* C'"
      and tr'''3: "\<forall>s. (s, ACrash) \<notin> set tr'''"
      and tr'''4: "\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a"
    by blast

  define tr4 where "tr4 = tr''' @ [(get_invoc (last tr'''), AInvcheck False)]"

  from \<open>packed_trace tr'''\<close>
  have "packed_trace tr4"
    by (auto simp add: packed_trace_def tr4_def nth_append,
     metis One_nat_def gr_implies_not_zero last_conv_nth length_0_conv less_SucE)


  moreover have "initialState program ~~ tr4 \<leadsto>* C'"
    using C'_fails steps_append2 steps_single tr'''2 tr4_def by blast
  moreover have "\<forall>s. (s, ACrash) \<notin> set tr4"
    by (simp add: tr4_def tr'''3)
  moreover have "\<not> traceCorrect tr4"
    by (auto simp add: traceCorrect_def tr4_def)

  ultimately show ?thesis by blast
qed    





end
