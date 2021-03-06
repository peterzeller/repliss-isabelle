section "No Invariant Checks"
theory no_failing_invchecks
imports packed_traces ignore_fails
begin


text "In this section we show that we can remove invariant checks from a trace 
without changing the behaviour of the system."


definition openTransactions :: "('proc, 'op, 'any) trace \<Rightarrow> (invocId \<times> txId) set" where
"openTransactions tr \<equiv> {(i, tx) | i j tx txns. j<length tr \<and> tr!j = (i, ABeginAtomic tx txns) \<and> (\<forall>k. k>j \<and> k<length tr \<longrightarrow> tr!k \<noteq> (i, AEndAtomic))}"


lemma open_transactions_empty:
  shows "openTransactions [] = {}"
  by (auto simp add: openTransactions_def)

lemma open_transactions_append_one: 
  shows "openTransactions (tr@[a]) =
(case a of
    (i, AEndAtomic) \<Rightarrow> openTransactions tr - ({i} \<times> UNIV)
  | (i, ABeginAtomic tx txns) \<Rightarrow> openTransactions tr \<union> {(i, tx)}
  | _ \<Rightarrow> openTransactions tr
)"
proof -
  obtain invoc action where a_def[simp]: "a = (invoc, action)"
    using prod.exhaust_sel by blast
  show ?thesis
  proof (cases action)
    case ALocal
    then show ?thesis 
      by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (ANewId x2)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis 
      by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits,
          blast, blast, fastforce)
  next
    case AEndAtomic
    then show ?thesis
      by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast+)
  next
    case (ADbOp )
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AInvoc )
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AReturn x7)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case ACrash
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AInvcheck r)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  qed
qed





text \<open>
If only the local states in invocId i differ,
we can transfer an execution to the different state,
when the execution trace contains no action in i.
\<close>



lemma show_state_transfer:
  assumes steps: "S_start ~~ tr \<leadsto>* S_end"
    and step_simulate: "\<And>a tr' S S'. \<lbrakk>a\<in>set tr; S ~~ a \<leadsto> S'; P tr' S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
    and step_preserves: "\<And>a tr' S S'. \<lbrakk>a\<in>set tr; S ~~ a \<leadsto> S'; P tr' S\<rbrakk> \<Longrightarrow> P (tr'@[a]) S'"
    and prop_initial: "P [] S_start"
  shows "(T S_start ~~ tr \<leadsto>* T S_end) \<and> P tr S_end"
  using steps step_simulate step_preserves prop_initial proof (induct rule: steps_induct)
  case initial
  show "(T S_start ~~ [] \<leadsto>* T S_start) \<and> P [] S_start"
    using \<open>P [] S_start\<close> 
    by (auto simp add: steps_empty)
next
  case (step S' tr a S'')
  show "(T S_start ~~ tr @ [a] \<leadsto>* T S'') \<and> P (tr @ [a]) S''" 
  proof (intro conjI)
    show "P (tr @ [a]) S''"
      by (metis append_is_Nil_conv butlast_snoc in_set_butlastD last_in_set last_snoc list.simps(3) prop_initial step.IH step.prems(1) step.prems(2) step.step)
    show " T S_start ~~ tr @ [a] \<leadsto>* T S''"
      by (metis UnI2 butlast_snoc in_set_butlastD list.set_intros(1) prop_initial set_append step.IH step.prems(1) step.prems(2) step.step steps_step)
  qed
qed

lemma show_state_transfer2_noP:
  assumes steps: "S_start ~~ tr \<leadsto>* S_end"
    and step_simulate: "\<And>i a S S'. \<lbrakk>(i,a)\<in>set tr; S ~~ (i,a) \<leadsto> S'\<rbrakk> \<Longrightarrow> T S ~~ (i,a) \<leadsto> T S'"
  shows "T S_start ~~ tr \<leadsto>* T S_end"
proof -
  from steps
  have "(T S_start ~~ tr \<leadsto>* T S_end) \<and> True"
    by (rule show_state_transfer; auto simp add: assms)
  then show ?thesis by simp
qed



lemma remove_local_step: 
  fixes S_start S_end :: "('proc::valueType, 'ls, 'op, 'any::valueType) state" 
  assumes step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ALocal ok)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and S_end'_def: "S_end' = S_end\<lparr>localState := (localState S_end)(i := localState S_start i)\<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('proc::valueType, 'ls, 'op, 'any::valueType) state. S\<lparr>localState := (localState S)(i := localState S_start i)\<rparr>"

  have "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  from steps_tr
  have "T S_mid ~~ tr \<leadsto>* T S_end"
  proof (rule show_state_transfer2_noP)
    show "T S ~~ (i',a) \<leadsto> T S'" if "(i',a) \<in> set tr" and  "S ~~ (i',a) \<leadsto> S'" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using \<open>(i',a) \<in> set tr\<close> no_i by force 
      then have [simp]: "i \<noteq> i'" by blast 

      from \<open>S ~~ (i',a) \<leadsto> S'\<close> 
      show "T S ~~ (i',a) \<leadsto> T S'"
        by (induct rule: step.cases, auto simp add: step_simps T_def state_ext elim: chooseSnapshot_unchanged_precise)
    qed
  qed

  then show "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by auto
qed



lemma remove_newId_step: 
  fixes S_start S_end :: "('proc::valueType, 'ls, 'op, 'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ANewId uid)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and S_end'_def: "S_end' = S_end\<lparr>generatedIds := (generatedIds S_end)(to_nat uid := None), localState := (localState S_end)(i := localState S_start i)\<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('proc, 'ls, 'op, 'any) state. S\<lparr>generatedIds := (generatedIds S)(to_nat uid := None), localState := (localState S)(i := localState S_start i)\<rparr>"

  have "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  have uid_fresh: "generatedIds S_start (to_nat uid) = None"
    using step_a a_def by (auto simp add: step_simps)

  obtain uid_i where "generatedIds S_mid (to_nat uid) \<triangleq> uid_i"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  from \<open>S_mid ~~ tr \<leadsto>* S_end\<close> \<open>generatedIds S_mid (to_nat uid) \<triangleq> uid_i\<close>
  have uid_not_used: "(i, ANewId uid) \<notin> set tr" for i
    by (rule uid_used_only_once)

  from steps_tr
  have "T S_mid ~~ tr \<leadsto>* T S_end"
  proof (rule show_state_transfer2_noP)
    show "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  "S ~~ (i',a) \<leadsto> S'" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using \<open>(i',a) \<in> set tr\<close> no_i by force 
      then have [simp]: "i \<noteq> i'" by blast 

      from \<open>S ~~ (i',a) \<leadsto> S'\<close> 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace uid_not_used by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
        then show ?case by (auto simp add: step_simps T_def state_ext elim: chooseSnapshot_unchanged_precise)
      next
        case (endAtomic C s ls f ls' t)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (dbop C s ls f Op  ls' t c res vis)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invocation C s proc initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (crash C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      qed
    qed
  qed

  then show "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed





lemma remove_beginAtomic_step: 
  fixes S_start S_end :: "('proc::valueType, 'ls, 'op, 'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ABeginAtomic t txns)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and newCalls_def: "newCalls = callsInTransaction C newTxns \<down> happensBefore C"
    and snapshot_def: "snapshot = vis \<union> newCalls"
    and S_end'_def: "S_end' = S_end\<lparr>
                localState := (localState S_end)(i := localState S_start i), 
                currentTx := (currentTx S_end)(i := None),
                txStatus := (txStatus S_end)(t := None),
                txOrigin := (txOrigin S_end)(t := None),
                visibleCalls := (visibleCalls S_end)(i := visibleCalls S_start i)
      \<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('proc, 'ls, 'op, 'any) state. S\<lparr>
                localState := (localState S)(i := localState S_start i), 
                currentTx := (currentTx S)(i := None),
                txStatus := (txStatus S)(t := None),
                txOrigin := (txOrigin S)(t := None),
                visibleCalls := (visibleCalls S)(i := visibleCalls S_start i) \<rparr>"



  have noOrig: "txOrigin S_start t = None"
    using step_a local.wf wf_transaction_status_iff_origin by (auto simp add: a_def step_simps)


  then have "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  define P where
    p_def: "P \<equiv> \<lambda>S::('proc, 'ls, 'op, 'any) state. t \<notin> committedTransactions S \<and> (\<forall>i'. i' \<noteq> i \<longrightarrow>  currentTx S i' \<noteq> Some t)"

  have "currentTx S_start i \<noteq> Some t" for i
    by (metis local.wf noOrig option.simps(3) wellFormed_currentTxUncommitted wf_transaction_status_iff_origin)

  then have "P S_mid"
    using step_a
    by (auto simp add: p_def step.simps  a_def  split: if_splits)




  from \<open>S_mid ~~ tr \<leadsto>* S_end\<close> 
  have t_not_used1: "(i, ABeginAtomic t txns) \<notin> set tr" for i txns
    using a_def no_i steps transactionIdsUnique2 by fastforce


  from steps_tr
  have "(T S_mid ~~ tr \<leadsto>* T S_end) \<and> P S_end"
  proof (rule show_state_transfer)

    show "P S_mid"
      using \<open>P S_mid\<close> .

    show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> P S'"
      using no_i by (auto simp add: step.simps p_def t_not_used1  split: if_splits)

    have "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  a_step: "S ~~ (i',a) \<leadsto> S'" and P_S: "P S" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using \<open>(i',a) \<in> set tr\<close> no_i by force 
      then have [simp]: "i \<noteq> i'" by blast 

      from \<open>S ~~ (i',a) \<leadsto> S'\<close> 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace t_not_used1 by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
        then show ?case 
          using in_trace t_not_used1 p_def \<open>P S\<close> by (auto simp add: step_simps T_def state_ext elim!: chooseSnapshot_unchanged_precise)
      next
        case (endAtomic C s ls f ls' t)
        then show ?case 
          using t_not_used1 \<open>P S\<close>
          by (auto simp add: step_simps T_def state_ext p_def, fastforce)
      next
        case (dbop C s ls f Op ls' t c res vis)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invocation C s proc initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (crash C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        have  "invContextH (callOrigin C) ((txOrigin C)(t := None)) ((txStatus C)(t := None)) (happensBefore C) (calls C) (knownIds C) (invocOp C)
               (invocRes C) 
          = invContext C "
          using P_S \<open>S = C\<close>
          by (auto simp add: invContextH_def restrict_map_def p_def committedCallsH_def  isCommittedH_def restrict_relation_def intro!: ext split: if_splits)


        with invCheck
        show ?case 
          using t_not_used1 P_S p_def by (auto simp add: step_simps T_def )
      qed
    qed
    then show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
      by force
  qed

  then show "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed



lemma remove_DBOp_step: 
  fixes S_start S_end :: "('proc::valueType, 'ls, 'op, 'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ADbOp cId operation res)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and S_end'_def: "S_end' = S_end\<lparr>
                localState := (localState S_end)(i := localState S_start i), 
                calls := (calls S_end)(cId := None),
                callOrigin := (callOrigin S_end)(cId := None),
                visibleCalls := (visibleCalls S_end)(i := visibleCalls S_start i),
                happensBefore := happensBefore S_end - {cId} \<times> UNIV - UNIV \<times> {cId}
      \<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -

  obtain start_txn where "currentTx S_start i \<triangleq> start_txn"
    using step_a a_def by (auto simp add: step_simps)

  have calls_S_start_cId: "calls S_start cId = None"
    using a_def callIds_unique(1) steps by fastforce

  

  with wellFormed_visibleCallsSubsetCalls_h(1)[OF wf]
  have hb1: "(c, cId) \<notin> happensBefore S_start" for c
    by blast

  from calls_S_start_cId wellFormed_visibleCallsSubsetCalls_h(1)[OF wf]
  have hb2: "(cId, c) \<notin> happensBefore S_start" for c
    by blast

  from calls_S_start_cId
  have callOrigin_S_start_cId: "callOrigin S_start cId = None"
    using local.wf wellFormed_callOrigin_dom3 by blast



  define T where 
    "T \<equiv> \<lambda>S::('proc, 'ls, 'op, 'any) state. S\<lparr>
                localState := (localState S)(i := localState S_start i), 
                calls := (calls S)(cId := None),
                callOrigin := (callOrigin S)(cId := None),
                visibleCalls := (visibleCalls S)(i := visibleCalls S_start i),
                happensBefore := happensBefore S - {cId} \<times> UNIV - UNIV \<times> {cId}
    \<rparr>"




  then have "T S_mid = S_start"
    using step_a  by (auto simp add: a_def step_simps T_def,
        subst state_ext,
        intro conjI,
        insert hb1 hb2 callOrigin_S_start_cId,
        auto)



  define P where
    p_def: "P \<equiv> \<lambda>S::('proc, 'ls, 'op, 'any) state. 
                     callOrigin S cId \<triangleq> start_txn 
                   \<and> txStatus S start_txn \<triangleq> Uncommitted
                   \<and> (\<forall>i'. i\<noteq>i' \<longrightarrow> currentTx S i' \<noteq> Some start_txn)
                   \<and> (\<forall>x. (cId, x) \<notin> happensBefore S)
                   \<and> (\<forall>i' vis. i\<noteq>i' \<and> visibleCalls S i' \<triangleq> vis \<longrightarrow> cId \<notin> vis)"


  have cId_not_used_again: "(s, ADbOp cId Op res) \<notin> set tr" for s Op res
    using callIds_unique2[OF steps, where i=0] by (simp add: a_def,
        metis One_nat_def Suc_mono diff_Suc_1 in_set_conv_nth zero_less_Suc)



  from steps_tr
  have "(T S_mid ~~ tr \<leadsto>* T S_end) \<and> P S_end"
  proof (rule show_state_transfer)

    from step_a
    show "P S_mid"
      using \<open>currentTx S_start i \<triangleq> start_txn\<close> local.wf wellFormed_currentTxUncommitted 
      by (auto simp add: p_def step_simps a_def,
          (insert wellFormed_currentTx_unique_h hb2 wellFormed_visibleCallsSubsetCalls2, blast)+)


    have cId_not_in_calls: "cId \<notin> callsInTransaction S newTxns \<down> happensBefore S" if "newTxns \<subseteq> committedTransactions S" and "P S" for S newTxns
      using that  by (auto simp add: p_def callsInTransactionH_contains downwardsClosure_in)


    show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> P S'"
      using no_i cId_not_used_again 
      by (auto simp add: step.simps p_def cId_not_in_calls chooseSnapshot_committed  split: if_splits, fastforce+)

    have "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  a_step: "S ~~ (i',a) \<leadsto> S'" and P_S: "P S" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using \<open>(i',a) \<in> set tr\<close> no_i by force 
      then have [simp]: "i \<noteq> i'" by blast 

      from \<open>S ~~ (i',a) \<leadsto> S'\<close> 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace  by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
        define C' where "C' \<equiv> C\<lparr>
            calls := (calls C)(cId := None), 
            happensBefore := happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId},
            localState := (localState C)(i := localState S_start i),
            visibleCalls := (visibleCalls C)(i := visibleCalls S_start i),
            callOrigin := (callOrigin C)(cId := None)\<rparr>"

        from beginAtomic show ?case 
        proof (auto simp add: step.simps T_def state_ext intro!: ext,
            auto simp add: intro!: exI[where x=C'],
            auto simp add: C'_def )

          show "chooseSnapshot_h snapshot vis (txStatus C) ((callOrigin C)(cId := None)) (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId})"
            if c0: "i' = s"
              and c1: "a = ABeginAtomic t snapshot"
              and c2: "S = C"
              and c3: "S' = C \<lparr>localState := localState C(s \<mapsto> ls'), currentTx := currentTx C(s \<mapsto> t), txStatus := txStatus C(t \<mapsto> Uncommitted), txOrigin := txOrigin C(t \<mapsto> s), visibleCalls := visibleCalls C(s \<mapsto> snapshot)\<rparr>"
              and c4: "localState C s \<triangleq> ls"
              and c5: "currentProc C s \<triangleq> f"
              and c6: "f ls = BeginAtomic ls'"
              and c7: "currentTx C s = None"
              and c8: "txStatus C t = None"
              and c9: "visibleCalls C s \<triangleq> vis"
              and c10: "chooseSnapshot snapshot vis C"
              and c11: "s \<noteq> i"
            using `chooseSnapshot snapshot vis C`
            by (rule chooseSnapshot_unchanged_precise, insert P_S   c2 p_def, auto)
        qed


      next
        case (endAtomic C s ls f ls' t)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (dbop C s ls f Op ls' t c res vis)

        have [simp]: "cId \<notin> vis "
          using P_S \<open>i' \<noteq> i\<close> dbop.hyps(1) dbop.hyps(10) dbop.hyps(2) p_def by fastforce


        have sameContext:
             "(getContextH (calls C) (happensBefore C) (Some vis)) 
            = (getContextH ((calls C)(cId := None)) (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId}) (Some vis))"
          by (auto simp add: getContextH_def restrict_map_def restrict_relation_def)
        
        from dbop
        show ?case using cId_not_used_again in_trace by (auto simp add: step_simps T_def state_ext sameContext)

      next
        case (invocation C s procName initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (crash C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        have [simp]: "\<not>isCommitted C cId"
          using P_S committedCalls_uncommittedNotIn invCheck.hyps(1) p_def
          by (simp add: isCommittedH_def) 
        have [simp]: "cId \<notin> committedCalls C"
          using P_S committedCalls_uncommittedNotIn invCheck.hyps(1) p_def by blast

        have [simp]: "isCommittedH ((callOrigin C)(cId := None)) (txStatus C) x
                  \<longleftrightarrow> isCommittedH (callOrigin C) (txStatus C) x"  for x
          by (auto simp add: isCommittedH_def,
           meson \<open>\<not> isCommitted C cId\<close> isCommittedH_def)


        have  "(invContextH ((callOrigin C)(cId := None)) (txOrigin C) (txStatus C) (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId}) ((calls C)(cId := None))
           (knownIds C) (invocOp C) (invocRes C)
           )
          = invContext C"
          using P_S \<open>S = C\<close>
          by (auto simp add: p_def invContextH_def restrict_map_def committedCallsH_def restrict_relation_def downwardsClosure_def callsInTransactionH_def intro!: ext)


        with invCheck
        show ?case 
          using P_S p_def by (auto simp add: step_simps T_def )
      qed
    qed
    then show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
      by force
  qed

  then show "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed



lemma transfer_execution_local_difference:
  assumes steps: "S1 ~~ tr \<leadsto>* S1'"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and S2_def: "S2 = S1\<lparr>localState := (localState S1)(i := ls),
      currentTx := (currentTx S1)(i := tx)\<rparr>"
    and S2'_def: "S2' = S1'\<lparr>localState := (localState S1')(i := ls),
      currentTx := (currentTx S1')(i := tx)\<rparr>"
  shows "S2 ~~ tr \<leadsto>* S2'"
  using steps no_i S2'_def proof (induct arbitrary: S2' rule: steps_induct)
  case initial
  then show ?case
    using steps_refl S2_def by blast 
next
  case (step S' tr a S'')

  define S_mid where "S_mid \<equiv> S'\<lparr>localState := (localState S')(i := ls), currentTx := (currentTx S')(i := tx)\<rparr>"

  have "S2 ~~ tr \<leadsto>* S_mid"
  proof (rule step.IH)
    show "\<And>a. a \<in> set tr \<Longrightarrow> get_invoc a \<noteq> i"
      using step.prems(1) by auto
    show " S_mid = S'\<lparr>localState := (localState S')(i := ls), currentTx := (currentTx S')(i := tx)\<rparr>"
      by (simp add: S_mid_def)
  qed

  have [simp]: "get_invoc a \<noteq> i" 
    by (auto simp add: step.prems(1))
  then have [simp]: "i\<noteq>get_invoc a"
    by blast


  from \<open>S' ~~ a \<leadsto> S''\<close>
  have "S_mid ~~ a \<leadsto> S2'"
  proof (induct rule: step.cases)
    case (local C s ls f ls')
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (newId C s ls f ls' uid)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (beginAtomic C s ls f ls' t vis snapshot)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> 
      by (auto simp add: step step_simps S_mid_def intro!: stateEqI elim: chooseSnapshot_unchanged)
  next
    case (endAtomic C s ls f ls' t)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (dbop C s ls f Op ls' t c res vis)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (invocation C s procName initialState impl)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (return C s ls f res)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (crash C s ls)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  next
    case (invCheck C res s)
    then show ?case 
      using \<open>get_invoc a \<noteq> i\<close> by (auto simp add: step step_simps S_mid_def intro!: stateEqI)
  qed
  then show "S2 ~~ tr @ [a] \<leadsto>* S2'"
    using \<open>S2 ~~ tr \<leadsto>* S_mid\<close> steps_step by blast

qed


lemma transfer_execution_local_difference':
  assumes steps: "S1 ~~ tr \<leadsto>* S1'"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> get_invoc a \<noteq> i"
    and S2_def: "\<exists>ls tx. S2 = S1\<lparr>localState := (localState S1)(i := ls),
      currentTx := (currentTx S1)(i := tx)\<rparr>"
  shows "\<exists>S2'. S2 ~~ tr \<leadsto>* S2'"
  using transfer_execution_local_difference[OF steps no_i]
  using S2_def by blast


definition no_invariant_checks_in_transaction where
"no_invariant_checks_in_transaction tr \<equiv> \<forall>ib i s c tx txns. 
    tr!ib = (s, ABeginAtomic tx txns)
  \<and> ib < i
  \<and> i < length tr 
  \<and> (\<forall>j. ib<j \<and> j<i \<longrightarrow> tr!j \<noteq> (s, AEndAtomic))
  \<longrightarrow> tr!i \<noteq> (s, AInvcheck c) "

lemma show_no_invariant_checks_in_transaction[case_names hasEndatomic[invcheck beginatomic beginBefore lessLength]]:
  assumes "\<And>i s tx txns c ib. \<lbrakk>tr!i = (s, AInvcheck c); tr!ib = (s, ABeginAtomic tx txns); ib < i; i<length tr\<rbrakk>
            \<Longrightarrow> \<exists>j. ib<j \<and> j<i \<and> tr!j = (s, AEndAtomic)"
  shows "no_invariant_checks_in_transaction tr"
  using assms by (auto simp add: no_invariant_checks_in_transaction_def, blast)

lemma use_no_invariant_checks_in_transaction:
  assumes "no_invariant_checks_in_transaction tr"
    and "tr!i = (s, AInvcheck c)"
    and "tr!ib = (s, ABeginAtomic tx txns)"
    and "ib < i"
    and "i < length tr"
  shows "\<exists>j. ib<j \<and> j<i \<and> tr!j = (s, AEndAtomic)"
  using assms by (auto simp add: no_invariant_checks_in_transaction_def, blast)



lemma maintain_no_invariant_checks_in_transaction:
  assumes "no_invariant_checks_in_transaction tr"
    and "get_action (tr!pos) \<noteq> AEndAtomic"
    and "pos < length tr"
  shows "no_invariant_checks_in_transaction (take pos tr @ drop (Suc pos) tr)"
proof (rule show_no_invariant_checks_in_transaction)
  fix i s tx txns c ib
  assume a1: "(take pos tr @ drop (Suc pos) tr) ! i = (s, AInvcheck c)"
    and  a2: "(take pos tr @ drop (Suc pos) tr) ! ib = (s, ABeginAtomic tx txns)"
    and a3: "ib < i"
    and a4: "i < length (take pos tr @ drop (Suc pos) tr)"

  define i' where "i' \<equiv> if i < pos then i else Suc i"
  define ib' where "ib' \<equiv> if ib < pos then ib else Suc ib"

  have a1': "tr!i' = (s, AInvcheck c)" 
    using a1 i'_def \<open>pos < length tr\<close> a4 by (auto simp add: nth_append min_def split: if_splits)

  have a2': "tr!ib' = (s, ABeginAtomic tx txns)" 
    using a2 ib'_def \<open>pos < length tr\<close> a3 a4 by (auto simp add: nth_append min_def split: if_splits)
  have a3':"ib'<i'"
    using a3 i'_def ib'_def by auto
  have a4':"i'<length tr"
    using a4 i'_def by auto

  with use_no_invariant_checks_in_transaction[OF \<open>no_invariant_checks_in_transaction tr\<close> a1' a2' a3' a4']
  obtain j where "j>ib'" and "j < i'" and  "tr ! j = (s, AEndAtomic)"
    by auto

  have h1: "ib < j"  by (metis Suc_lessD \<open>ib' < j\<close> ib'_def)
  have h2: "j < i" if "j < pos"
    using \<open>j < i'\<close> i'_def less_antisym that by fastforce

  then show  "\<exists>j>ib. j < i \<and> (take pos tr @ drop (Suc pos) tr) ! j = (s, AEndAtomic)"
  proof (cases "j < pos")
    case True
    show ?thesis 
      by (rule exI[where x=j], auto simp add: True \<open>tr ! j = (s, AEndAtomic)\<close> assms(3) h1 h2 less_imp_le min.absorb2 nth_append_first)
  next
    case False
    show ?thesis 
    proof (rule exI[where x="j - 1"], auto)
      from  \<open>j>ib'\<close> \<open>j < i'\<close> False
      have  
         "j \<le> i" and cases:"(ib < pos \<and> j \<ge> pos) \<or> ( ib \<ge> pos \<and> Suc ib < j )"
        by (auto simp add: ib'_def i'_def split: if_splits)
        
      have h3: "Suc ib < j"
        if c0: "ib < pos"
          and c1: "pos \<le> j"
          and c2: "j > 0"
        using Suc_lessI \<open>tr ! j = (s, AEndAtomic)\<close> assms(2) local.cases by fastforce
        

(*
        by (metis \<open>tr ! j = (s, AEndAtomic)\<close> assms(2) c0 c1 c2 h1 le_SucE less_antisym not_less snd_conv)
*)


      show "ib < j - Suc 0"
        using cases h3 by auto
      show "j - Suc 0 < i"
        using \<open>ib < j - Suc 0\<close> \<open>j \<le> i\<close> by linarith

      have "pos \<noteq> j"
        using \<open>tr ! j = (s, AEndAtomic)\<close> assms(2) by auto



      show " (take pos tr @ drop (Suc pos) tr) ! (j - Suc 0) = (s, AEndAtomic)"
        using \<open>tr ! j = (s, AEndAtomic)\<close>  False \<open>pos \<noteq> j\<close> \<open>j < i'\<close> a4' less_imp_diff_less less_trans
        by (auto simp add: nth_append nth_drop_if Suc_lessI min.absorb2)
    qed
  qed
qed


lemma maintain_no_invariant_checks_in_transaction2a:
  assumes "no_invariant_checks_in_transaction tr"
    and "pos < length tr"
    and "0 < pos"
    and pos_no_endAtomic: 
    "\<And>i invoc tx txns. \<lbrakk>
        i<pos; 
        tr!i = (invoc, ABeginAtomic tx txns); 
      \<And>j. \<lbrakk>i<j; j<pos\<rbrakk> \<Longrightarrow> tr!j \<noteq> (invoc, AEndAtomic)
      \<rbrakk> \<Longrightarrow> tr!pos \<noteq> (invoc, AEndAtomic)"
  shows "no_invariant_checks_in_transaction (take pos tr @ drop (Suc pos) tr)"
proof (rule show_no_invariant_checks_in_transaction)
  fix i s tx txns c ib
  assume a0: "(take pos tr @ drop (Suc pos) tr) ! i = (s, AInvcheck c)"
    and a1: "(take pos tr @ drop (Suc pos) tr) ! ib = (s, ABeginAtomic tx txns)"
    and a2: "ib < i"
    and a3: "i < length (take pos tr @ drop (Suc pos) tr)"

  text "Function f converts position to position in original trace tr."
  define f where "f  \<equiv> \<lambda>i. if i < pos then i else Suc i"

  have [simp]: " min (length tr) pos = pos"
    using assms(2) by auto 
  have [simp]: "pos + (length tr - Suc pos) = length tr - 1"
    by (simp add: Suc_leI assms(2))
  have [simp]: "Suc pos \<le> length tr"
    using assms(2) by auto


  have "i < length tr - 1"
    using a3 by auto


  have h1: "tr ! f i = (s, AInvcheck c)"
    using a0 by (auto simp add: f_def nth_append  split: if_splits)

  have h2: "tr ! f ib = (s, ABeginAtomic tx txns)"
    using a1 by (auto simp add: f_def nth_append  split: if_splits)

  from `no_invariant_checks_in_transaction tr`
  have "\<exists>j>f ib. j < f i \<and> tr ! j = (s, AEndAtomic)"
    using h1 h2
  proof (rule use_no_invariant_checks_in_transaction)
    show "f ib < f i"
      using a2 f_def by auto
    show "f i < length tr"
      using \<open>i < length tr - 1\<close> dual_order.strict_trans f_def by auto
  qed
  from this
  obtain j where "j > f ib" and " j < f i" and "tr!j = (s, AEndAtomic)"
    by blast

  show "\<exists>j>ib. j < i \<and> (take pos tr @ drop (Suc pos) tr) ! j = (s, AEndAtomic)"
  proof (rule classical)
    assume neg: "\<not> (\<exists>j>ib. j < i \<and> (take pos tr @ drop (Suc pos) tr) ! j = (s, AEndAtomic))"

    have "tr ! pos \<noteq> (s, AEndAtomic)" if "f ib < pos"
    proof (rule pos_no_endAtomic)
      show "tr ! f ib = (s, ABeginAtomic tx txns)"
        using h2 by auto
      show "f ib < pos" using that .
      show " \<And>j. \<lbrakk>f ib < j; j < pos\<rbrakk> \<Longrightarrow> tr ! j \<noteq> (s, AEndAtomic)"
        using neg apply (auto simp add: nth_append split: if_splits)
        apply (drule_tac x=j in spec)
        apply auto
         apply (metis dual_order.asym f_def not_less_eq)
        by (smt Suc_lessI \<open>f ib < j\<close> \<open>j < f i\<close> \<open>min (length tr) pos = pos\<close> \<open>tr ! j = (s, AEndAtomic)\<close> dual_order.strict_trans f_def isPrefix_appendI isPrefix_same length_take neg not_less_eq nth_take)
    qed

    hence  "j \<noteq> pos" if "f ib < pos"
      using \<open>tr ! j = (s, AEndAtomic)\<close> that by blast
    hence "j \<noteq> pos"
      using \<open>f ib < j\<close> by blast


(*
    thm pos_no_endAtomic
    have "j \<noteq> pos"
      using \<open>f ib < j\<close> \<open>tr ! j = (s, AEndAtomic)\<close> pos_no_endAtomic h2 by blast
*)

    show "\<exists>j>ib. j < i \<and> (take pos tr @ drop (Suc pos) tr) ! j = (s, AEndAtomic)"
    proof (intro exI conjI)
      show "ib < (if j \<le> pos then j else j - 1)"
        using \<open>f ib < j\<close> by (auto simp add: f_def split: if_splits)
      show "(if j \<le> pos then j else j - 1) < i"
        using \<open>j < f i\<close> \<open>j \<noteq> pos\<close> by (auto simp add: f_def split: if_splits)
      show "(take pos tr @ drop (Suc pos) tr) ! (if j \<le> pos then j else j - 1) = (s, AEndAtomic)"
        using \<open>tr ! j = (s, AEndAtomic)\<close>  \<open>j \<noteq> pos\<close> by (auto simp add: nth_append)
    qed
  qed
qed

lemma no_invariant_checks_in_transaction_tail:
  assumes "no_invariant_checks_in_transaction tr"
  shows "no_invariant_checks_in_transaction (drop 1 tr)"
proof (rule show_no_invariant_checks_in_transaction)

fix i s tx txns c ib
assume a0: "drop 1 tr ! i = (s, AInvcheck c)"
   and a1: "drop 1 tr ! ib = (s, ABeginAtomic tx txns)"
   and a2: "ib < i"
   and a3: "i < length (drop 1 tr)"


  from  `no_invariant_checks_in_transaction tr`
  have "\<exists>j>Suc ib. j < Suc i \<and> tr ! j = (s, AEndAtomic)"
  proof (rule  use_no_invariant_checks_in_transaction)
    show "tr ! Suc i = (s, AInvcheck c)"
      using a0 a3 by auto
    show "tr ! Suc ib = (s, ABeginAtomic tx txns)"
      using a1 a3 by auto
    show "Suc ib < Suc i"
      by (simp add: a2)
    show "Suc i < length tr"
      using a3 by auto
  qed
  then

  show "\<exists>j>ib. j < i \<and> drop 1 tr ! j = (s, AEndAtomic)"
    using Suc_less_eq2 a3 by auto
qed


lemma maintain_no_invariant_checks_in_transaction2:
  assumes "no_invariant_checks_in_transaction tr"
    and "pos < length tr"
    and pos_no_endAtomic: 
    "\<And>i invoc tx txns. \<lbrakk>
        i<pos; 
        tr!i = (invoc, ABeginAtomic tx txns); 
      \<And>j. \<lbrakk>i<j; j<pos\<rbrakk> \<Longrightarrow> tr!j \<noteq> (invoc, AEndAtomic)
      \<rbrakk> \<Longrightarrow> tr!pos \<noteq> (invoc, AEndAtomic)"
  shows "no_invariant_checks_in_transaction (take pos tr @ drop (Suc pos) tr)"
proof (cases "0 < pos")
  case True
  then show ?thesis
    using assms maintain_no_invariant_checks_in_transaction2a pos_no_endAtomic by blast
next
  case False
  hence [simp]: "pos = 0"
    by simp

  then show ?thesis
    using assms(1) no_invariant_checks_in_transaction_tail by auto 
qed

definition
"isNoInvCheck a \<equiv> case a of (s, AInvcheck txns) \<Rightarrow> False | _ \<Rightarrow> True"

definition 
"removeInvChecks \<equiv> filter isNoInvCheck"


lemma removeInvChecks_same:
  assumes "S ~~ trace \<leadsto>* S'"
shows "S ~~ removeInvChecks trace \<leadsto>* S'"
using assms proof (induct rule: steps_induct)
  case initial
  then show ?case  by (auto simp add: removeInvChecks_def steps_empty)
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: removeInvChecks_def isNoInvCheck_def steps_append step_simps steps_empty steps_single split: action.splits)

qed


lemma removeInvChecks_no_invcheck:
  assumes "ia < length (removeInvChecks trace)"
  shows "removeInvChecks trace ! ia \<noteq> (s, AInvcheck c)"
proof 
  assume "removeInvChecks trace ! ia = (s, AInvcheck c)"
  then have " (s, AInvcheck c) \<in> set (removeInvChecks trace)"
    using assms
    using nth_mem by force 
  then show False
    by (auto simp add: removeInvChecks_def  isNoInvCheck_def)
qed


end