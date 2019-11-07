theory commutativity2
imports commutativity
begin

lemma move_outside_transaction:
  assumes b_is_a_different_session[simp]: "sa \<noteq> sb"
    and wf[simp]: "state_wellFormed S"
    and no_end_atomic: "b \<noteq> AEndAtomic"
  shows "(S ~~ [(sa,ABeginAtomic t newTxns),(sb,b)] \<leadsto>* T)
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,ABeginAtomic t newTxns)] \<leadsto>* T)"
proof (rule useCommutativeS)
  show "commutativeS S (sa, ABeginAtomic t newTxns) (sb, b)"
    using assms by (rule commutative_beginAtomic_other)
qed

definition transactionIsPackedMeasure :: "'any trace \<Rightarrow> txid \<Rightarrow> nat" where
  "transactionIsPackedMeasure tr tx \<equiv>
  card {k . indexInOtherTransaction tr tx k}"  

lemma indexInOtherTransaction_finite: "finite {k. indexInOtherTransaction tr tx k}"
  by (auto simp add: indexInOtherTransaction_def)


lemma transactionIsPackedMeasure_zero_iff: 
  "transactionIsPackedMeasure tr tx = 0 \<longleftrightarrow>  transactionIsPacked tr tx" 
  by (auto simp add: transactionIsPackedMeasure_def transactionIsPacked_def indexInOtherTransaction_finite)

lemma if_cases2:
  "\<lbrakk>c \<Longrightarrow> X = t; \<not>c \<Longrightarrow> X = f\<rbrakk> \<Longrightarrow>  X = (if c then t else f)"
  by auto

lemma inTransactionEmpty: "\<not>inTransaction [] i s"
  by (auto simp add: inTransaction_def)

lemma sessionsInTransactionEmpty:
  "sessionsInTransaction [] i = {}"
  by (simp add: inTransactionEmpty sessionsInTransaction_def)

lemma sessionsInTransactionEmptySnoc:
  "sessionsInTransaction (tr@[a]) i = (
if i=length tr then
  if \<exists>t ts. snd a = ABeginAtomic t ts then
       sessionsInTransaction tr (length tr - 1) \<union> {fst a}
  else if snd a = AEndAtomic then
       sessionsInTransaction tr (length tr - 1) - {fst a}
  else 
       sessionsInTransaction tr (length tr - 1)
else if i > length tr then
  {}
else
  sessionsInTransaction tr i)"
proof (intro if_cases2; clarsimp?)
  fix t ts
  assume a0: "i = length tr"
    and a1: "snd a = ABeginAtomic t ts"

  then show "sessionsInTransaction (tr @ [a]) (length tr) = insert (fst a) (sessionsInTransaction tr (length tr - Suc 0))"
  proof (case_tac a, auto)
    show "\<And>aa x. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr; x \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr); x \<notin> sessionsInTransaction tr (length tr - Suc 0)\<rbrakk> \<Longrightarrow> x = aa"
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
      by (metis (full_types) Suc_leI Suc_le_mono Suc_pred gr_implies_not_zero less_imp_le_nat nat_neq_iff)
    show "\<And>aa. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr\<rbrakk> \<Longrightarrow> aa \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr)"
      by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
    show "\<And>aa x. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr; x \<in> sessionsInTransaction tr (length tr - Suc 0)\<rbrakk> \<Longrightarrow> x \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr)"
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
      by (metis Suc_diff_Suc le0 le_less_trans less_Suc_eq_le minus_nat.diff_0)
  qed
next
  assume a0: "i = length tr"
    and a1: "snd a = AEndAtomic"

  then show "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0) - {fst a}"
    apply (case_tac a, auto)
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
      apply (smt Suc_pred inc_induct less_Suc_eq less_imp_le_nat linorder_neqE_nat not_less_zero)
     apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def sndI split: if_splits)[1]
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    by (metis Suc_pred leD le_SucI length_greater_0_conv less_Suc_eq_le list.size(3) not_less_zero)
next
  assume a0: "i = length tr"
    and a1: "\<forall>t ts. snd a \<noteq> ABeginAtomic t ts"
    and a2: "snd a \<noteq> AEndAtomic"

  then show "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0)"
    apply (case_tac a, auto)
     apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)
     apply (smt Suc_diff_diff Suc_pred cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_is_0_eq' diff_zero le_trans n_not_Suc_n nat_le_linear not_gr_zero zero_less_diff)
    by (metis Suc_pred le0 le_less_trans less_not_refl3 less_trans_Suc not_le)

next 
  show "length tr < i \<Longrightarrow> sessionsInTransaction (tr @ [a]) i = {}"
    by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)


  show "sessionsInTransaction (tr @ [a]) i = sessionsInTransaction tr i"
    if c0: "i \<noteq> length tr"
      and c1: "\<not> length tr < i"
    using that by (simp add: less_linear sessionsInTransaction_append)

qed



lemma sessionsInTransaction_finite:
  "finite (sessionsInTransaction tr i)"
  apply (induct tr arbitrary: i rule: rev_induct)
   apply (auto simp add: sessionsInTransactionEmptySnoc sessionsInTransactionEmpty)
  done


lemma drop_nth:
"drop n xs ! i = (xs ! (min n (length xs) + i))"
proof (induct xs)
  case Nil
  then show ?case 
    by auto

next
  case (Cons a xs)
  then show ?case 
    apply auto
    by (metis (no_types, lifting) add_diff_cancel_left' append_take_drop_id length_Cons length_take min.commute not_add_less1 nth_append)
qed


lemma take_nth:
"take n xs ! i = (if i < n then xs ! i else []!(i - min n (length xs)))"
proof (induct xs arbitrary: n i)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc n')
    then show ?thesis 
      apply auto
       apply (case_tac i)
      apply auto
      by (metis Cons.hyps One_nat_def Suc_pred diff_Suc_eq_diff_pred less_Suc_eq_0_disj neq0_conv)
  qed
qed

lemma max_natset_Suc:
  assumes "max_natset S = Suc i"
    and "finite S"
  shows "i\<in>S"
    and "\<And>j. j\<in>S \<Longrightarrow> j\<le>i"
  using assms apply (auto simp add: max_natset_def  split: if_splits)
  using Max_in by blast




lemma packedTraces_stay_in_transaction:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "packed_trace tr"
    and "currentTransaction S invoc \<triangleq> tx"
    and "tr \<noteq> [] \<Longrightarrow> fst (hd tr) = invoc"
    and "(invoc, AEndAtomic) \<notin> set tr"
    and "\<And>i. (i, AFail) \<notin> set tr"
    and "\<And>a. a\<in>set tr \<Longrightarrow> \<not>allowed_context_switch (snd a)"
    and "j < length tr"
  shows "currentTransaction S' invoc \<triangleq> tx \<and> fst (tr ! j) = invoc"
  using assms proof (induct arbitrary: j rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'' j)

  show ?case
  proof (cases tr)
    case Nil
    with step
    show ?thesis 
      by (auto simp add: step.simps)
  next
    case (Cons x xs)

    have [simp]: "packed_trace tr"
      using packed_trace_prefix step.prems(1) by blast
    then have [simp]: "packed_trace (x#xs)"
      by (simp add: local.Cons)

    have [simp]: "currentTransaction S' (fst x) = Some tx"
      using local.Cons step.IH step.prems by force

    have "fst (last tr) = invoc"
      using last_conv_nth local.Cons step.IH step.prems by fastforce

    from Cons step
    have "currentTransaction S'' invoc \<triangleq> tx"
      by (auto simp add: step.simps split: if_splits)

    {
      assume j_def[simp]: "j = length (x # xs)"

      from use_packed_trace[OF \<open>packed_trace (tr @ [a])\<close>, where i="length tr"]
      have a_allowed_ctxt_switch: "fst a = invoc"
        by (metis \<open>fst (last tr) = invoc\<close> diff_less j_def last_conv_nth length_greater_0_conv less_numeral_extra(1) list.simps(3) local.Cons nth_append_first nth_append_length nth_mem step.prems(6) step.prems(7)) 

      have ?thesis
        by (simp add: \<open>currentTransaction S'' invoc \<triangleq> tx\<close> a_allowed_ctxt_switch local.Cons) 
    }
    moreover
    {
      assume "j < length (x # xs)"
      have ?thesis
        by (metis \<open>currentTransaction S'' invoc \<triangleq> tx\<close> \<open>j < length (x # xs)\<close> \<open>packed_trace tr\<close> append_is_Nil_conv butlast_snoc hd_append2 in_set_butlastD local.Cons nth_append_first step.IH step.prems(2) step.prems(3) step.prems(4) step.prems(5) step.prems(6))
    }
    ultimately show ?thesis
      using local.Cons step.prems(7) by fastforce
  qed
qed

lemmas packedTraces_stay_in_transaction1 = packedTraces_stay_in_transaction[THEN conjunct1]
lemmas packedTraces_stay_in_transaction2 = packedTraces_stay_in_transaction[THEN conjunct2]

lemma packedTraces_transactions_same_invocation:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and beginTx: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and noEndTx: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and noContextSwitch: "\<forall>j. i < j \<and> j < k \<longrightarrow> \<not>allowed_context_switch (snd (tr!j))"
    and [simp]: "i < j" 
    and [simp]: "j < k"
    and [simp]: "k \<le> length tr"
  shows "fst (tr ! j) = invoc"
proof -
  have "take (Suc i) tr @ drop (Suc i) (take k tr) @ drop k tr = tr"
    apply (auto simp add: drop_take append_eq_conv_conj min_def)
    using \<open>i < j\<close> \<open>j < k\<close> apply linarith
    by (metis add_Suc_right \<open>i < j\<close> \<open>j < k\<close> le_add_diff_inverse2 less_imp_le less_trans_Suc)

  from this
  obtain S1 S2
    where "S ~~ take (Suc i) tr \<leadsto>* S1"
      and "S1 ~~ drop (Suc i) (take k tr) \<leadsto>* S2"
      and "S2 ~~ drop k tr \<leadsto>* S'"
    by (smt steps steps_append)


  from \<open>S1 ~~ drop (Suc i) (take k tr) \<leadsto>* S2\<close>
  have "fst ( drop (Suc i) (take k tr) ! (j - Suc i)) = invoc"
  proof (rule packedTraces_stay_in_transaction2)
    show "packed_trace (drop (Suc i) (take k tr))"
      using \<open>packed_trace tr\<close> packed_trace_drop packed_trace_take by blast 
    from \<open>S ~~ take (Suc i) tr \<leadsto>* S1\<close>
    have "S ~~ take i tr @ [tr!i] \<leadsto>* S1"
      by (metis \<open>i < j\<close> \<open>j < k\<close> \<open>k \<le> length tr\<close> dual_order.strict_trans min.absorb2 min_less_iff_conj take_Suc_conv_app_nth)
    from this
    obtain S1_pre where "S1_pre ~~ tr!i \<leadsto> S1"
      using steps_appendBack by blast

    then show  "currentTransaction S1 invoc \<triangleq> tx"
      using beginTx by (auto simp add: step_simps)
      
    show  "drop (Suc i) (take k tr) \<noteq> [] \<Longrightarrow> fst (hd (drop (Suc i) (take k tr))) = invoc"
      using \<open>packed_trace tr\<close> by (smt One_nat_def \<open>take (Suc i) tr @ drop (Suc i) (take k tr) @ drop k tr = tr\<close> append_Cons append_eq_append_conv append_is_Nil_conv append_self_conv append_take_drop_id \<open>i < j\<close> \<open>j < k\<close> \<open>k \<le> length tr\<close> beginTx diff_Suc_Suc diff_zero fst_conv hd_Cons_tl lessI less_trans_Suc noContextSwitch not_le_imp_less nth_via_drop packed_trace_def take_all zero_less_Suc)
      
    show  "(invoc, AEndAtomic) \<notin> set (drop (Suc i) (take k tr))"
      by (auto simp add: in_set_conv_nth take_nth drop_nth noEndTx)

    show  "\<And>ia. (ia, AFail) \<notin> set (drop (Suc i) (take k tr))"
      using noFail by (meson in_set_dropD in_set_takeD )

    show  "\<And>a. a \<in> set (drop (Suc i) (take k tr)) \<Longrightarrow> \<not> allowed_context_switch (snd a)"
      using noContextSwitch  apply (auto simp add: in_set_conv_nth take_nth drop_nth min_def  split: if_splits)
         apply (metis less_add_Suc1 snd_conv)
      apply (metis add.commute add_Suc assms(9) le_antisym less_add_Suc1 less_diff_conv snd_conv)
      apply (metis less_add_Suc1 snd_conv)
      by (metis add_Suc le_add_diff_inverse less_add_Suc1 nat_add_left_cancel_less snd_conv)

    show  "j - Suc i < length (drop (Suc i) (take k tr))"
      by (simp add: Suc_leI diff_less_mono min.absorb2)
      
  qed
  then show "fst (tr ! j) = invoc "
    using assms(7) assms(8) assms(9) by auto
qed



end