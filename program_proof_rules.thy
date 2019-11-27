theory program_proof_rules
  imports 
    invariant_simps 
    unique_ids
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language
    topological_sort
begin


definition execution_s_check where
  "execution_s_check 
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  generatedLocal
  vis
  localCalls
  tx
  ls
 \<equiv>  (\<forall>trace S1 S'. 
           (S1 ~~ (i, trace) \<leadsto>\<^sub>S* S')
       \<longrightarrow> (\<forall>p t. (AInvoc p, t) \<notin> set trace)
       \<longrightarrow> state_wellFormed S1
       \<longrightarrow> calls S1 = s_calls
       \<longrightarrow> happensBefore S1 = updateHb s_happensBefore vis localCalls
       \<longrightarrow> callOrigin S1 = map_update_all s_callOrigin localCalls (the tx)
       \<longrightarrow> transactionOrigin S1 = s_transactionOrigin
       \<longrightarrow> knownIds S1 = s_knownIds
       \<longrightarrow> invocationOp S1 = s_invocationOp
       \<longrightarrow> invocationRes S1 = s_invocationRes
       \<longrightarrow> prog S1 = progr
       \<longrightarrow> generatedLocal = {x. generatedIds S1 x \<triangleq> i}
       \<longrightarrow> localState S1 i \<triangleq> ls
       \<longrightarrow> currentProc S1 i \<triangleq> toImpl
       \<longrightarrow> visibleCalls S1 i \<triangleq>  (vis \<union> set localCalls)
       \<longrightarrow> currentTransaction S1 i = tx
       \<longrightarrow> (\<forall>tx'. tx \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted)
       \<longrightarrow> (case tx of Some tx' \<Rightarrow> set localCalls =  {c. callOrigin S1 c \<triangleq> tx'} | None \<Rightarrow> localCalls = [])
       \<longrightarrow> (sorted_by (happensBefore S1) localCalls)
       \<longrightarrow> (vis \<inter> set localCalls = {})
       \<longrightarrow> (dom s_callOrigin \<inter> set localCalls = {})
       \<longrightarrow> (Field s_happensBefore \<inter> set localCalls = {})
       \<longrightarrow> distinct localCalls
       \<longrightarrow> traceCorrect_s  trace)"

lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, rotated]

lemma beforeInvoc_execution_s_check: 
  assumes "s_invocationOp i = None"
  shows "
execution_s_check   progr   i  s_calls   s_happensBefore   s_callOrigin   s_transactionOrigin   s_knownIds   s_invocationOp  s_invocationRes  generatedLocal  vis localCalls  tx  ls
"
  using assms 
  by (auto simp add: execution_s_check_def steps_s_cons_simp Let_def wf_localState_to_invocationOp)





text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"



lemma execution_s_check_sound:
  assumes  "localState S i \<triangleq> ls"
    and "visibleCalls S i \<triangleq> vis"
    and "prog S = progr"
    and "currentProc S i \<triangleq> toImpl"
    and "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    and no_currentTxn: "currentTransaction S i = None"
    and c: "execution_s_check 
  progr 
  i
  (calls S)
  (happensBefore S)
  (callOrigin S)
  (transactionOrigin S)
  (knownIds S)
  (invocationOp S)
  (invocationRes S)
  generatedLocal
  vis
  []
  (currentTransaction S i)
  ls"
  shows "execution_s_correct progr S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume a0: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"


  thm c[simplified execution_s_check_def]

  from a0
  show "traceCorrect_s  trace"
  proof (rule c[simplified execution_s_check_def, rule_format]; force?)
    show "state_wellFormed S"
      by (simp add: assms)

    show "\<And>p t. (AInvoc p, t) \<notin> set trace"
      using a0 assms no_more_invoc by blast


    show "prog S = progr"
      by (simp add: assms)

    show " generatedLocal = {x. generatedIds S x \<triangleq> i}"
      by (auto simp add: assms)

    show "localState S i \<triangleq> ls"
      by (simp add: assms(1))

    show "currentProc S i \<triangleq> toImpl"
      by (simp add: assms)

    show "currentTransaction S i \<noteq> Some tx' \<Longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted" for tx'
      by (simp add: assms)

    show "visibleCalls S i \<triangleq> (vis \<union> set [])"
      by (simp add: assms)

    show "case currentTransaction S i of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S c \<triangleq> tx'}"
      by (simp add: no_currentTxn)

    show "sorted_by (happensBefore S) []"
      by (simp add: sorted_by_empty)


  qed
qed


lemma execution_s_check_sound2:
  assumes a1: "localState S i \<triangleq> ls"
    and a2: "S \<in> initialStates progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
  execution_s_check 
  progr 
  i
  s_calls
  s_happensBefore
  s_callOrigin
  s_transactionOrigin
  s_knownIds
  s_invocationOp
  s_invocationRes
  {}
  {}
  []
  None
  ls"
  shows "execution_s_correct progr S i"
  using a1
proof (rule execution_s_check_sound)


  show "visibleCalls S i \<triangleq> {}"
    using a2 by (auto simp add: initialStates_def)

  show "prog S = progr"
    using a2 by (auto simp add: initialStates_def)

  show "currentProc S i \<triangleq> toImpl"
    using a3 by simp

  show wf: "state_wellFormed S"
    using a2 initialStates_wellFormed by blast

  show "{} = {x. generatedIds S x \<triangleq> i}"
    using a2 wf_generated_ids_invocation_exists by (auto simp add: initialStates_def, blast)

  show currentTx: "currentTransaction S i = None"
    using a2 initialState_noTxns2 by blast


  show "execution_s_check progr i (calls S) (happensBefore S) (callOrigin S) (transactionOrigin S) (knownIds S) (invocationOp S)
     (invocationRes S) {} {} [] (currentTransaction S i) ls "
    unfolding currentTx
    by (rule c)

  show "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    using a2 initialState_noTxns1 by blast

qed


lemma traceCorrect_s_empty: "traceCorrect_s  [] "
  by (simp add: traceCorrect_s_def) 

lemma case_trace_not_empty:
  assumes  "\<And>a trace'. trace = a#trace' \<Longrightarrow> traceCorrect_s  (a#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty2:
  assumes  "\<And>action Inv trace'. trace = (action, Inv)#trace' \<Longrightarrow> traceCorrect_s  ((action, Inv)#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty3:
  assumes "S ~~ (i,trace) \<leadsto>\<^sub>S* S''"
    and "\<And>action S' Inv trace'. \<lbrakk>
      trace = (action, Inv)#trace'; 
      S ~~ (i,action,Inv) \<leadsto>\<^sub>S S'; 
      S' ~~ (i,trace') \<leadsto>\<^sub>S* S''\<rbrakk> \<Longrightarrow> Inv \<and> traceCorrect_s (trace')"
  shows "traceCorrect_s  trace"
  by (metis assms(1) assms(2) case_trace_not_empty2 sndI steps_s_cons_simp traceCorrect_s_split)


lemma sorted_by_updateHb:
  assumes "set cs \<inter> vis = {}"
    and "set cs \<inter> Field hb = {}"
    and "distinct cs"
  shows "sorted_by (updateHb hb vis cs) cs"
  using assms proof (induct cs arbitrary: hb vis)
case Nil
  then show ?case 
    by (simp add: sorted_by_empty)

next
  case (Cons x xs)

  have "distinct xs"
    using Cons.prems(3) by auto


  from this
  have IH: "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) xs"
  proof (fuzzy_rule Cons)

    show " set xs \<inter> insert x vis = {}"
      using Cons by auto
    show " set xs \<inter> Field (hb \<union> vis \<times> {x}) = {}"
      using Cons by (auto simp add: Field_def)
  qed

  show ?case 
  proof (auto simp add: updateHb.simps)
    show "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) (x # xs)"
      apply (auto simp add: sorted_by_cons_iff IH)
      using Cons.prems(1) Cons.prems(2) Cons.prems(3) FieldI1 updateHb_simp2 by fastforce
  qed
qed

definition 
  "new_unique_not_in_invocationOp iop uidv \<equiv>
\<forall>i op. iop i \<triangleq> op \<longrightarrow> to_nat uidv \<notin> uniqueIds op "


definition 
  "new_unique_not_in_calls iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> to_nat uidv \<notin> uniqueIds op "

definition 
  "new_unique_not_in_calls_result iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> to_nat uidv \<notin> uniqueIds r "

definition
"new_unique_not_in_invocationRes ires uidv \<equiv> 
\<forall>i r. ires i \<triangleq> r \<longrightarrow> to_nat uidv \<notin> uniqueIds r "

lemma no_ainvoc:
  assumes "\<forall>p t. (AInvoc p, t) \<notin> set trace"
    and "trace = (action, Inv) # trace'"
and "\<lbrakk>\<forall>p t. (AInvoc p, t) \<notin> set trace; \<And>proc. action \<noteq> AInvoc proc\<rbrakk> \<Longrightarrow> P"
shows "P"
  using assms by auto

method show_proof_rule = 
  (subst  execution_s_check_def, intro allI impI, erule case_trace_not_empty3, erule(1) no_ainvoc, goal_cases Step)

inductive_cases step_s_NewId: "S ~~ (i, ANewId uidv, Inv) \<leadsto>\<^sub>S S'"

lemma execution_s_check_newId:
  assumes "infinite (Collect P)"
    and "program_wellFormed progr"
    and cont: "\<And>v. \<lbrakk>P v; 
 new_unique_not_in_calls s_calls v;
new_unique_not_in_calls_result s_calls v;
new_unique_not_in_invocationOp s_invocationOp v;
new_unique_not_in_invocationRes s_invocationRes v;
to_nat v \<notin> s_knownIds;
to_nat v \<notin> localGenerated;
uniqueIds v = {to_nat v}
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  (localGenerated \<union> {to_nat v})
  vis
  localCalls
  tx
  (cont v)"

shows"execution_s_check
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  localCalls
  tx
  (newId P \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S' action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (newId P \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  obtain uidv
    where c0: "localState S1 i \<triangleq> (newId P \<bind> cont)"
      and c1: "currentProc S1 i \<triangleq> toImpl"
      and c2: "action = ANewId uidv"
      and c3: "Inv"
      and S'a_def: "S'a = S1\<lparr>localState := localState S1(i \<mapsto> cont uidv), generatedIds := generatedIds S1(to_nat uidv \<mapsto> i)\<rparr>"
      and c5: "generatedIds S1 (to_nat uidv) = None"
      and c6: "uniqueIds uidv = {to_nat uidv}"
      and c7: "P uidv"
    by (auto simp add: step_s.simps split:if_splits)

  show "Inv \<and> traceCorrect_s trace'"
  proof (intro conjI)
    show "Inv" using `Inv` .

    from `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S'`
    show "traceCorrect_s trace'"
    proof (rule use_execution_s_check)


      show "execution_s_check
            progr 
            i
            s_calls 
            s_happensBefore 
            s_callOrigin 
            s_transactionOrigin 
            s_knownIds 
            s_invocationOp
            s_invocationRes
            (localGenerated \<union> {to_nat uidv})
            vis
            localCalls
            tx
            (cont uidv)"
      proof (rule cont)
        show "P uidv"
          by (simp add: c7)

        show "new_unique_not_in_calls s_calls uidv"
          using Step(1) Step(2) Step(9) assms(2) c5 new_unique_not_in_calls_def wf_onlyGeneratedIdsInCalls by blast


        show "new_unique_not_in_calls_result s_calls uidv"
          using Step(1) Step(2) Step(9) assms(2) c5 new_unique_not_in_calls_result_def wf_onlyGeneratedIdsInCallResults by blast

        show "new_unique_not_in_invocationOp s_invocationOp uidv"
          using Step(1) Step(7) Step(9) assms(2) c5 new_unique_not_in_invocationOp_def wf_onlyGeneratedIdsInInvocationOps by blast

        show "new_unique_not_in_invocationRes s_invocationRes uidv"
          using Step(1) Step(8) Step(9) assms(2) c5 new_unique_not_in_invocationRes_def wf_onlyGeneratedIdsInInvocationRes by blast

        show "to_nat uidv \<notin> s_knownIds"
          using Step(1) Step(6) Step(9) assms(2) c5 wf_onlyGeneratedIdsInKnownIds by blast

        show "to_nat uidv \<notin> localGenerated"
          by (simp add: Step(10) c5)

        show "uniqueIds uidv = {to_nat uidv}"
          by (simp add: c6)

      qed


      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        using Step(16) by (auto simp add: S'a_def  split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step by (auto simp add:S'a_def )

    qed (auto simp add: S'a_def Step)
  qed
qed



lemma restrict_map_noop: "dom m \<subseteq> S \<Longrightarrow> m |` S = m"
   using domIff by (auto simp add: restrict_map_def intro!: ext, force)


lemma restrict_map_noop2[simp]: "m |` dom m = m"
  by (simp add: restrict_map_noop)

lemma restrict_relation_noop: "Field r \<subseteq> S \<Longrightarrow> r |r S = r"
  by (auto simp add: restrict_relation_def FieldI1 FieldI2 subset_h1)


lemma execution_s_check_beginAtomic:
  assumes "program_wellFormed progr"
    and cont: "\<And>tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis'
 s_invocationOp' s_invocationRes'.
\<lbrakk>invariant progr
     \<lparr>calls = s_calls', 
      happensBefore = s_happensBefore',
      callOrigin = s_callOrigin',
      transactionOrigin = s_transactionOrigin', 
      knownIds = s_knownIds',
      invocationOp = s_invocationOp', 
      invocationRes = s_invocationRes'\<rparr>;
s_transactionOrigin' tx = None
\<comment> \<open>
TODO: 
- no calls in new transaction
- state-growing predicates
- vis growing
- valid snapshot (causally + transactionally + session guarantees)
- nothing happens on invocation i
\<close>

\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls' 
  s_happensBefore' 
  s_callOrigin' 
  (s_transactionOrigin'(tx \<mapsto> i))
  s_knownIds' 
  s_invocationOp'
  s_invocationRes'
  localGenerated
  vis'
  []
  (Some tx)
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  []
  None
  (beginAtomic \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (beginAtomic \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  obtain t txns S' vis' vis''
    where c0: "localState S1 i \<triangleq> (beginAtomic \<bind> cont)"
      and c1: "currentProc S1 i \<triangleq> toImpl"
      and c2: "action = ABeginAtomic t txns"
      and c3: "Inv"
      and c4: "currentTransaction S1 i = None"
      and c5: "transactionStatus S1 t = None"
      and c6: "prog S' = prog S1"
      and growth: "state_monotonicGrowth i S1 S'"
      and c8: "\<forall>x. transactionOrigin S1 x \<triangleq> i = transactionOrigin S' x \<triangleq> i"
      and inv: "invariant (prog S1) (invContext S')"
      and c10: "\<forall>x. transactionStatus S' x \<noteq> Some Uncommitted"
      and wf_S': "state_wellFormed S'"
      and c12: "state_wellFormed (S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> cont ()), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>)"
      and c13: "localState S' i \<triangleq> (beginAtomic \<bind> cont)"
      and c14: "currentProc S' i \<triangleq> toImpl"
      and c15: "currentTransaction S' i = None"
      and c16: "visibleCalls S1 i \<triangleq> vis'"
      and c17: "visibleCalls S' i \<triangleq> vis'"
      and c18: "chooseSnapshot vis'' vis' S'"
      and c19: "consistentSnapshot S' vis''"
      and c20: "transactionStatus S' t = None"
      and c21: "\<forall>x. callOrigin S' x \<noteq> Some t"
      and c22: "transactionOrigin S' t = None"
      and S'a_def: "S'a = S' \<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> cont ()), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof (intro conjI)
    show "Inv" using `Inv` .

    from `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    show "traceCorrect_s trace'"
    proof (rule use_execution_s_check)

      show "happensBefore S'a = updateHb (happensBefore S'a) vis'' []"
        by simp

      show "callOrigin S'a = map_update_all (callOrigin S'a) [] (the (Some t))"
        by simp

      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto


      show " state_wellFormed S'a"
        using S'a_def c12 by blast

      show "currentProc S'a i \<triangleq> toImpl"
        by (simp add: S'a_def c14)

      show "localState S'a i \<triangleq> cont ()"
        by (simp add: S'a_def)

      show "visibleCalls S'a i \<triangleq> (vis'' \<union> set [])"
        by (simp add: S'a_def)

      show "currentTransaction S'a i \<triangleq> t"
        by (simp add: S'a_def)

      show " \<And>tx'. Some t \<noteq> Some tx' \<Longrightarrow> transactionStatus S'a tx' \<noteq> Some Uncommitted"
        by (simp add: S'a_def c10)
      show "case Some t of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S'a c \<triangleq> tx'}"
        by (simp add: S'a_def c21)
      show "sorted_by (happensBefore S'a) []"
        by (simp add: S'a_def sorted_by_empty)
      show "vis'' \<inter> set [] = {}"
        by simp
      show "dom (callOrigin S'a) \<inter> set [] = {}"
        by simp
      show "Field (happensBefore S'a) \<inter> set [] = {}"
        by simp
      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a) (transactionOrigin S'a) (knownIds S'a)
     (invocationOp S'a) (invocationRes S'a) {x. generatedIds S'a x \<triangleq> i} vis'' [] (Some t) (cont ())"
      proof (fuzzy_rule cont)

        show "localGenerated = {x. generatedIds S'a x \<triangleq> i}"
          using `localGenerated = {x. generatedIds S1 x \<triangleq> i}` growth state_monotonicGrowth_generatedIds_same1 by (auto simp add: S'a_def)

        show "progr = prog S'a"
          by (simp add: S'a_def `prog S1 = progr` c6)

        show "transactionOrigin S'(t \<mapsto> i) = transactionOrigin S'a"
          by (simp add: S'a_def)

        show "transactionOrigin S' t = None"
          by (simp add: c22)


        show " invariant progr
     \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
        transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = invocationOp S'a,
        invocationRes = invocationRes S'a\<rparr>"
        proof (fuzzy_rule inv)
          show "prog S1 = progr"
            by (simp add: Step)

          have cCalls: "committedCalls S' = dom (calls S')"
            by (simp add: c10 wf_S' committedCalls_allCommitted)

          have allTransactionsCommitted: "committedTransactions S' = dom (transactionOrigin S')"
            apply (auto simp add: dom_def)
             apply (metis wf_S' domD domIff option.simps(3) wf_transaction_status_iff_origin)
            by (metis c10 not_None_eq not_uncommitted_cases wf_S' wf_transaction_status_iff_origin)



          show "invContext S' =
           \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
            transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = invocationOp S'a,
           invocationRes = invocationRes S'a\<rparr>"
          proof (auto simp add: invContextH_def S'a_def cCalls allTransactionsCommitted)
            show "\<And>a b. (a, b) \<in> happensBefore S' |r dom (calls S') \<Longrightarrow> (a, b) \<in> happensBefore S'"
              by (simp add: restrict_relation_def)
            show "\<And>a b. (a, b) \<in> happensBefore S' \<Longrightarrow> (a, b) \<in> happensBefore S' |r dom (calls S')"
              by (simp add: wf_S' happensBefore_in_calls_left happensBefore_in_calls_right restrict_relation_def)
            show " callOrigin S' |` dom (calls S') = callOrigin S'"
              by (metis wf_S' restrict_map_noop2 wellFormed_callOrigin_dom)
          qed
        qed
      qed


    qed (auto simp add: S'a_def Step)
  qed
qed



lemma execution_s_check_endAtomic:
  assumes "program_wellFormed progr"
    and "s_transactionOrigin tx = None"
and assert_inv: "
\<lbrakk>invocation_happensBeforeH 
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore 
 \<union> {i' | i' c'. i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and> c' \<in> vis} \<times> {i}
\<rbrakk>
 \<Longrightarrow> invariant progr
     \<lparr>calls = s_calls, 
      happensBefore = updateHb s_happensBefore vis localCalls,
      callOrigin = map_update_all s_callOrigin localCalls tx,
      transactionOrigin = s_transactionOrigin(tx \<mapsto> i), 
      knownIds = s_knownIds,
      invocationOp = s_invocationOp, 
      invocationRes = s_invocationRes\<rparr>"
    and cont: "
\<comment> \<open>

\<close>
\<lbrakk>
invocation_happensBeforeH 
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore 
 \<union> {i' | i' c'. i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and> c' \<in> vis} \<times> {i};
invariant progr 
     \<lparr>calls = s_calls, 
      happensBefore = updateHb s_happensBefore vis localCalls,
      callOrigin = map_update_all s_callOrigin localCalls tx,
      transactionOrigin = s_transactionOrigin(tx \<mapsto> i), 
      knownIds = s_knownIds,
      invocationOp = s_invocationOp, 
      invocationRes = s_invocationRes\<rparr>
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls 
  (updateHb s_happensBefore vis localCalls) 
  (map_update_all s_callOrigin localCalls tx) 
  (s_transactionOrigin(tx \<mapsto> i))
  s_knownIds 
  s_invocationOp
  s_invocationRes
  localGenerated
  (vis \<union> set localCalls)
  []
  None
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  (s_transactionOrigin(tx \<mapsto> i)) 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  localCalls
  (Some tx)
  (endAtomic \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (endAtomic \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
    `currentTransaction S1 i \<triangleq> tx`
  have action_def: "action = AEndAtomic"
    and S'a_def: "S'a = S1
     \<lparr>localState := localState S1(i \<mapsto> cont ()), currentTransaction := (currentTransaction S1)(i := None),
        transactionStatus := transactionStatus S1(tx \<mapsto> Committed)\<rparr>"
    and S'a_wf: "state_wellFormed S'a"
    and Inv_def: "Inv \<longleftrightarrow> 
     invariant (prog S1)
      (invContextH (callOrigin S1) (transactionOrigin S1) (transactionStatus S1(tx \<mapsto> Committed)) (happensBefore S1)
        (calls S1) (knownIds S1) (invocationOp S1) (invocationRes S1))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    have allCommitted1: 
      "transactionStatus S1 tx' \<triangleq> Committed" if "tx' \<noteq> tx" and "callOrigin S1 c \<triangleq> tx'" for c tx'
      using that
      by (metis (no_types, lifting) Step(1) Step(15) option.exhaust_sel option.inject transactionStatus.exhaust wf_no_transactionStatus_origin_for_nothing) 

    have tx_uncommitted: "transactionStatus S1 tx \<triangleq> Uncommitted"
      using Step(1) Step(14) not_uncommitted_cases wellFormed_currentTransaction_unique_h(2) by blast

    have allCommitted2: "transactionStatus S1 t \<triangleq> Committed \<longleftrightarrow> t \<noteq> tx \<and> transactionStatus S1 t \<noteq> None" for t
      apply (cases "transactionStatus S1 t", auto simp add: tx_uncommitted)
      using Step(15) transactionStatus.exhaust by force



    have committedCallsH_simp: "committedCallsH (callOrigin S1) (transactionStatus S1(tx \<mapsto> Committed))
      = dom (calls S1)"
      using  wellFormed_callOrigin_dom[OF `state_wellFormed S1`]
 wf_callOrigin_and_calls[OF `state_wellFormed S1`]
      apply (auto simp add: committedCallsH_def isCommittedH_def exists_cases1 allCommitted2 )
      by (metis (mono_tags, lifting) allCommitted1 allCommitted2 domExists_simp)
      
    have h1: "s_calls = calls S1"
        by (simp add: Step)

      have h2: "updateHb s_happensBefore vis localCalls = happensBefore S1 |r dom (calls S1)"
apply (simp add: Step)
        apply (subst restrict_relation_noop, auto simp add: Field_def)
        using Step(1) Step(2) Step(3) happensBefore_in_calls_left happensBefore_in_calls_right by fastforce+
      

      have h3: "map_update_all s_callOrigin localCalls tx = callOrigin S1 |` dom (calls S1)"
        apply (simp add: Step)
        apply (subst restrict_map_noop)
         apply auto
        using Step(1) Step(2) Step(4) wellFormed_callOrigin_dom by fastforce+



      have h4: "s_transactionOrigin(tx\<mapsto>i) =
        transactionOrigin S1 |` {t. t \<noteq> tx \<longrightarrow> transactionStatus S1 t \<triangleq> Committed}"
        apply (simp add: Step )
        apply (subst restrict_map_noop)
        by (auto simp add: `s_transactionOrigin tx = None` Step(1) Step(5) allCommitted2 wf_transaction_status_iff_origin)



      have  invocation_hb_simp:
          "invocation_happensBeforeH 
          (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
          (updateHb s_happensBefore vis localCalls)
      = invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore 
       \<union> {i' | i' c'. i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and> c' \<in> vis} \<times> {i}"
        sorry

    show "Inv"
      unfolding Inv_def 
      using invocation_hb_simp  `prog S1 = progr`[symmetric]  
    proof (fuzzy_rule assert_inv)
    qed (auto simp add:  invContextH_def committedCallsH_simp h1 h2 h3 h4  del: equalityI; auto simp add: Step)



    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      thm use_execution_s_check
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "currentTransaction S'a i = None"
        by (simp add: S'a_def)

      show "state_wellFormed S'a"
        using S'a_wf by auto

      show "happensBefore S'a = updateHb (happensBefore S'a) (vis\<union>set localCalls)  []"
        by simp

      show "callOrigin S'a = map_update_all (callOrigin S'a) [] (the None)"
        by simp

      show " localState S'a i \<triangleq> cont ()"
        by (simp add: S'a_def Step)
      
      show "currentProc S'a i \<triangleq> toImpl"
        by (simp add: S'a_def Step)

      show "visibleCalls S'a i \<triangleq> (vis \<union> set localCalls \<union> set [])"
        by (simp add: S'a_def Step)

      show "\<And>tx'. None \<noteq> Some tx' \<Longrightarrow> transactionStatus S'a tx' \<noteq> Some Uncommitted"
        by (simp add: S'a_def Step)

      show "sorted_by (happensBefore S'a) []"
        by (simp add: sorted_by_empty)

      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a)
       (transactionOrigin S'a) (knownIds S'a) (invocationOp S'a) (invocationRes S'a)
       {x. generatedIds S'a x \<triangleq> i} (vis \<union> set localCalls) [] None (cont ())"
      using invocation_hb_simp proof (fuzzy_rule cont; (simp add: S'a_def Step)?)
        show "invariant progr
     \<lparr>calls = s_calls, happensBefore = updateHb s_happensBefore vis localCalls,
        callOrigin =  map_update_all s_callOrigin localCalls tx,
        transactionOrigin = s_transactionOrigin(tx \<mapsto> i), knownIds = s_knownIds,
        invocationOp = s_invocationOp, invocationRes = s_invocationRes\<rparr>"
          using invocation_hb_simp  by (rule assert_inv)
      qed
    qed (simp add: S'a_def Step)+
  qed
qed




lemma execution_s_check_pause:
  assumes cont: "
\<comment> \<open>

\<close>
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  localCalls
  tx
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  localCalls
  tx
  (pause \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (pause \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  have "action = ALocal"
    and  Inv
    and S'a_def: "S'a = S1\<lparr>localState := localState S1(i \<mapsto> cont ())\<rparr>"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof

    show "Inv" using `Inv` .

    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      thm use_execution_s_check
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      from `case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S1 c \<triangleq> tx'}`
      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        by (auto simp add: S'a_def split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step(17) Step(3) by (simp add: S'a_def )


      show " execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
     s_invocationOp s_invocationRes {x. generatedIds S1 x \<triangleq> i} vis localCalls tx (cont ())"
      proof (fuzzy_rule cont)
        show "localGenerated = {x. generatedIds S1 x \<triangleq> i}"
          by (simp add: Step(10))
      qed

    qed (simp add: S'a_def Step)+
  qed
qed


lemma updateHb_restrict:
 " updateHb hb vis cs |r S =
   updateHb (hb |r S) (vis \<inter> S) (filter (\<lambda>x. x \<in> S) cs)"
  by (induct cs arbitrary: vis hb,
   auto simp add: restrict_relation_def updateHb.simps,
  (metis (no_types, lifting) Int_iff Un_iff mem_Sigma_iff singletonD updateHb_cases)+)



lemma execution_s_check_dbop:
  assumes progr_wf: "program_wellFormed progr"
    (* might add this to ensure progress:  
     and query_res_exists: "True"*)
and cont: "\<And>c res. \<lbrakk>
querySpec progr op \<lparr>
      calls = s_calls |` (vis \<union> set localCalls), 
      happensBefore=updateHb (s_happensBefore |r vis) vis localCalls\<rparr> res
\<comment> \<open>

\<close>
\<rbrakk> \<Longrightarrow> 
 execution_s_check
  progr 
  i
  (s_calls(c \<mapsto> Call op res))
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  (localCalls @ [c])
  (Some tx)
  (cont res)"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  localCalls
  (Some tx)
  (call op \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (call op \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
    ` currentTransaction S1 i \<triangleq> tx`
`visibleCalls S1 i \<triangleq> (vis \<union> set localCalls)`
  obtain c res
    where c0: "localState S1 i \<triangleq> (call op \<bind> cont)"
   and c1: "currentProc S1 i \<triangleq> toImpl"
   and c2: "currentTransaction S1 i \<triangleq> tx"
   and c3: "visibleCalls S1 i \<triangleq> (vis \<union> set localCalls)"
   and c4: "action = ADbOp c op res"
   and c5: "Inv"
   and S'a_def: "S'a = S1 \<lparr>localState := localState S1(i \<mapsto> cont res), calls := calls S1(c \<mapsto> Call op res), callOrigin := callOrigin S1(c \<mapsto> tx), visibleCalls := visibleCalls S1(i \<mapsto> insert c (vis \<union> set localCalls)), happensBefore := happensBefore S1 \<union> (vis \<union> set localCalls) \<times> {c}\<rparr>"
   and fresh_c: "calls S1 c = None"
   and qry: "querySpec (prog S1) op (getContextH (calls S1) (happensBefore S1) (Some (vis \<union> set localCalls))) res"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof

    show "Inv" using `Inv` .

    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      thm use_execution_s_check
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      show "calls S'a = s_calls(c \<mapsto> Call op res)"
        by (simp add: S'a_def Step)

      show "happensBefore S'a = updateHb s_happensBefore vis (localCalls@[c])"
        by (auto simp add: S'a_def Step
          updateHb_chain[symmetric, where vis'="set localCalls \<union> vis"]
          updateHb_single)

      have s: "map_of (map (\<lambda>c. (c, tx)) localCalls) c = Some t
        \<longleftrightarrow> (c\<in>set localCalls \<and> t = tx) " for c t
        by (auto simp add:  map_of_Some comp_def Step)


      show "callOrigin S'a =  map_update_all s_callOrigin (localCalls@[c]) (the (Some tx))"
        by (auto simp add: map_update_all_get  S'a_def Step map_add_def intro!: ext dest!: map_of_SomeD split: option.splits)

      show "case Some tx of None \<Rightarrow> localCalls @ [c] = []
            | Some tx' \<Rightarrow> set (localCalls @ [c]) = {c. callOrigin S'a c \<triangleq> tx'}"
        using Step(16) Step(4)  by (auto simp add: s S'a_def Step map_add_def map_of_None split: option.splits del: )

      have "c \<notin> set localCalls"
        by (meson Step(1) UnCI c3 fresh_c wellFormed_visibleCallsSubsetCalls2)

      have "c \<notin> vis"
        by (meson Step(1) UnCI c3 fresh_c wellFormed_visibleCallsSubsetCalls2)


      have "callOrigin S1 c = None"
        using wellFormed_callOrigin_dom[OF `state_wellFormed S1`] fresh_c by blast

      hence "s_callOrigin c = None"
        using `callOrigin S1 = map_update_all s_callOrigin localCalls (the (Some tx))`
        by (auto simp add: map_update_all_get split: if_splits)


      show "sorted_by (happensBefore S'a) (localCalls @ [c])"
      proof (auto simp add: sorted_by_append_iff sorted_by_single)
        from `sorted_by (happensBefore S1) localCalls`
        show "sorted_by (happensBefore S'a) localCalls"
          apply (auto simp add: S'a_def)
          apply (auto simp add: sorted_by_def)
          by (metis (mono_tags, lifting) Step(1) Step(16) fresh_c less_trans mem_Collect_eq nth_mem option.distinct(1) option.simps(5) wellFormed_callOrigin_dom2)

        show "\<And>x. \<lbrakk>x \<in> set localCalls; (c, x) \<in> happensBefore S'a\<rbrakk> \<Longrightarrow> False"
          apply (auto simp add: S'a_def Step)
          using Step(1) Step(3) fresh_c wellFormed_happensBefore_calls_l apply blast
          using Step(18) apply auto[1]
          using \<open>c \<notin> set localCalls\<close> by auto
      qed

      from `vis \<inter> set (localCalls) = {}`
      show "vis \<inter> set (localCalls @ [c]) = {}"
        by (auto simp add: `c \<notin> vis`)


      show "dom s_callOrigin \<inter> set (localCalls @ [c]) = {}"
        apply (auto simp add: `s_callOrigin c = None`)
        using Step(19) by blast

      have "c \<notin> Field s_happensBefore"
        by (smt DomainE FieldI2 Field_def RangeE Step(1) Step(20) Step(3) Un_iff disjoint_iff_not_equal fresh_c updateHb_simp2 wellFormed_happensBefore_calls_l wellFormed_happensBefore_calls_r)

      from this and `Field s_happensBefore \<inter> set localCalls = {}`
      show "Field s_happensBefore \<inter> set (localCalls @ [c]) = {}"
        by auto

      from `distinct localCalls` and `c\<notin>set localCalls`
      show "distinct (localCalls @ [c])"
        by auto

      show " execution_s_check progr i (s_calls(c \<mapsto> Call op res)) s_happensBefore s_callOrigin
       s_transactionOrigin s_knownIds s_invocationOp s_invocationRes {x. generatedIds S1 x \<triangleq> i} vis
       (localCalls @ [c]) (Some tx) (cont res)"
      proof (fuzzy_rule cont)
        show "querySpec progr op
             \<lparr>calls = s_calls |` (vis \<union> set localCalls),
              happensBefore = updateHb (s_happensBefore |r vis) vis localCalls\<rparr>
             res"
        proof (fuzzy_rule qry; auto simp add: Step getContextH_def del: equalityI)
          have [simp]: "s_happensBefore |r (vis \<union> set localCalls) = (s_happensBefore |r vis)"
            using `Field s_happensBefore \<inter> set localCalls = {}`
            by (auto simp add: restrict_relation_def Field_def)


          show " updateHb s_happensBefore vis localCalls |r (vis \<union> set localCalls) =
            updateHb (s_happensBefore |r vis) vis localCalls"
            by (auto simp add: updateHb_restrict)
        qed

        from `localGenerated = {x. generatedIds S1 x \<triangleq> i}`
        show "localGenerated = {x. generatedIds S1 x \<triangleq> i}" .
      qed


    qed (simp add: S'a_def Step; fail)+
  qed
qed




lemma execution_s_check_return:
  assumes progr_wf: "program_wellFormed progr"
    and query_res_exists: "True"
and inv: "invariant progr
  \<lparr>
        calls = s_calls, 
        happensBefore = s_happensBefore , 
        callOrigin  = s_callOrigin,
        transactionOrigin = s_transactionOrigin,
        knownIds = s_knownIds  \<union> uniqueIds res,
        invocationOp = s_invocationOp,
        invocationRes = s_invocationRes(i \<mapsto> res)
      \<rparr>"
shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
  []
  None
  (return res)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (return res)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  have c2: "action = AReturn res"
   and c3: "currentTransaction S1 i = None"
   and S'a_def: "S'a = S1 \<lparr>localState := (localState S1)(i := None), currentProc := (currentProc S1)(i := None), visibleCalls := (visibleCalls S1)(i := None), invocationRes := invocationRes S1(i \<mapsto> res), knownIds := knownIds S1 \<union> uniqueIds res\<rparr>"
   and Inv_def: "Inv \<longleftrightarrow> invariant (prog S1) (invContextH (callOrigin S1) (transactionOrigin S1) (transactionStatus S1) (happensBefore S1) (calls S1) (knownIds S1 \<union> uniqueIds res) (invocationOp S1) (invocationRes S1(i \<mapsto> res)))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus1: "transactionStatus S1 tx' \<noteq> Some Uncommitted" for tx'
      by auto

    have txStatus2: "transactionStatus S1 tx \<triangleq> y
      \<longleftrightarrow> (transactionStatus S1 tx \<triangleq> Committed \<and> y = Committed)" for tx y
      apply auto
      using transactionStatus.exhaust txStatus1 by auto



    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus3: "transactionStatus S1 tx \<triangleq> Committed
      \<longleftrightarrow>transactionStatus S1 tx \<noteq> None" for tx
      using transactionStatus.exhaust by (auto, blast)


    have commmitted: "committedTransactions S1 = dom s_transactionOrigin"
      apply (auto simp add: `transactionOrigin S1 = s_transactionOrigin`[symmetric] txStatus1)
      apply (simp add: Step(1) txStatus3 wf_transaction_status_iff_origin)
      by (simp add: Step(1) state_wellFormed_transactionStatus_transactionOrigin txStatus3)

    have committed2: "committedCalls S1 = dom (calls S1)"
      using Step(1) committedCalls_allCommitted txStatus1 by blast 

    hence committed3: "committedCallsH s_callOrigin (transactionStatus S1) =  dom s_calls"
      by (simp add: Step)


    show "Inv" 
      unfolding Inv_def invContextH_def
    proof (fuzzy_rule inv; (simp add: Step commmitted committed3))

      show "s_callOrigin = s_callOrigin |` dom s_calls"
      proof (rule restrict_map_noop[symmetric])
        show "dom s_callOrigin \<subseteq> dom s_calls"
          using Step(1) Step(2) Step(4) wellFormed_callOrigin_dom by fastforce
      qed

      show "s_happensBefore = s_happensBefore |r dom s_calls"
      proof (rule restrict_relation_noop[symmetric])
        show "Field s_happensBefore \<subseteq> dom s_calls"
          apply (auto simp add: Field_def)
          using Step(1) Step(2) Step(3) happensBefore_in_calls_left happensBefore_in_calls_right by fastforce+
      qed
    qed


    show "traceCorrect_s trace'"
    proof (cases trace')
      case Nil
      then show ?thesis
        using traceCorrect_s_empty by auto 
    next
      case (Cons a list)

      obtain action' Inv' where a_def: "a = (action', Inv')"
        by force

      have no_invoc: "\<And>proc. action' \<noteq> AInvoc proc"
        using Step(22) Step(25) a_def local.Cons by auto



      from Cons `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
      obtain S'' where "S'a ~~ (i, (action', Inv')) \<leadsto>\<^sub>S S''"
        using steps_s_cons_simp a_def by blast 
      hence False
        using S'a_def no_invoc
        by (auto simp add: step_s.simps)
      thus "traceCorrect_s trace'" ..
    qed
  qed
qed

lemmas repliss_proof_rules = 
  execution_s_check_newId
  execution_s_check_beginAtomic
  execution_s_check_endAtomic
  execution_s_check_pause
  execution_s_check_dbop
  execution_s_check_return

method repliss_vcg_step = (rule repliss_proof_rules; simp?;  repliss_vcg_step?)

method repliss_vcg uses impl = (simp add: atomic_def impl, repliss_vcg_step)

(* TODO maybe start new file *)

lemma i_callOriginI_h_update_simp:
  assumes "\<And>c. co c \<noteq> Some tx"
shows "(i_callOriginI_h (map_update_all co cs tx) (to(tx \<mapsto> i)))
       = map_update_all (i_callOriginI_h co to) cs i"
  using assms  by (auto simp add: i_callOriginI_h_def map_update_all_get  split: option.splits if_splits)

(* TODO utils *)
lemma map_update_all_None:
"map_update_all m xs y x = None \<longleftrightarrow> (x\<notin>set xs \<and> m x = None)"
  by (induct xs, auto simp add: map_update_all_def)

lemma map_update_all_Some_same:
"map_update_all m xs y x \<triangleq> y \<longleftrightarrow> (x\<in>set xs \<or> m x \<triangleq> y)"
  by (induct xs, auto simp add: map_update_all_def)

lemma map_update_all_Some_other:
  assumes "y' \<noteq> y"
  shows "map_update_all m xs y x \<triangleq> y' \<longleftrightarrow> (x\<notin>set xs \<and> m x \<triangleq> y')"
  using assms  by (induct xs, auto simp add: map_update_all_def)

find_consts name:downw

lemma invocation_happensBeforeH_update_simp:
  assumes a1: "\<And>c. co c \<noteq> Some tx"
    and a2: "\<And>c c'. \<lbrakk>c\<in>set cs; c'\<notin>set cs\<rbrakk> \<Longrightarrow> (c,c')\<notin>hb"
    and a5: "vis \<inter> dom co = {}"
    and a6: "dom co \<inter> set cs = {}"
    and a7: "Field hb \<inter> set cs = {}"
    and a9: "cs \<noteq> []"
    and a11: "\<And>c. i_callOriginI_h co to c \<triangleq> i \<Longrightarrow> c \<in> vis"
  shows "invocation_happensBeforeH
            (i_callOriginI_h (map_update_all co cs tx)
              (to(tx \<mapsto> i)))
            (updateHb hb vis cs)
= (let prevI = {i' | i' c'. i_callOriginI_h co to c' \<triangleq> i' \<and> c' \<in> vis} in
   let afterI_old = {i'. (i,i') \<notin> invocation_happensBeforeH (i_callOriginI_h co to) hb}
   in 
  (invocation_happensBeforeH (i_callOriginI_h co to) hb 
   \<union> (prevI - afterI_old) \<times> {i})
    - {i} \<times> (prevI \<inter> afterI_old))" (is "?left = ?right")
  text \<open>In this lemma, prevI is the set of invocations that happened before i in the state after the transaction and 
  afterI_old is the set of invocations that happened after i in the state before this transaction.
  Now, this relation can change: If the newly executed transaction uses calls from afterI_old, then
  the two invocations are now considered to be concurrent.
  Note that this can only occur if there are multiple transactions in invocation i.\<close>

proof -

  text "Some simplifications:"

  define left where "left \<equiv> ?left"
  define right where "right \<equiv> ?right"

  have i_callOriginI_h_simp:
    "(i_callOriginI_h (map_update_all co cs tx) (to(tx \<mapsto> i)) c \<triangleq> i1)
        \<longleftrightarrow> (if i1 = i then c\<in>set cs \<or> i_callOriginI_h co to c \<triangleq> i 
             else i_callOriginI_h co to c \<triangleq> i1)" for c i1
    using a6 by (auto simp add: a1 i_callOriginI_h_def map_update_all_None map_update_all_Some_same map_update_all_Some_other split: option.splits)



  
  { text "We first prove the case for two invocations that are not i:"
    fix i1 i2
    assume b1: "i1\<noteq>i" and b2: "i2\<noteq>i" and b3: "i1 \<noteq> i2"
  
    have "(i1,i2)\<in> left
    \<longleftrightarrow> ((\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
         (\<exists>c. i_callOriginI_h co to c \<triangleq> i2) \<and>
         (\<forall>cx cy. i_callOriginI_h co to cx \<triangleq> i1 \<and> i_callOriginI_h co to cy \<triangleq> i2 \<longrightarrow> (cx, cy) \<in> updateHb hb vis cs))"
      by (simp add: left_def invocation_happensBeforeH_def b1 b2 b3 i_callOriginI_h_simp)

    moreover
    have "(i1,i2)\<in> right
    \<longleftrightarrow> ((\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
         (\<exists>c. i_callOriginI_h co to c \<triangleq> i2) \<and>
         (\<forall>cx cy. i_callOriginI_h co to cx \<triangleq> i1 \<and> i_callOriginI_h co to cy \<triangleq> i2 \<longrightarrow> (cx, cy) \<in> updateHb hb vis cs))"
      apply (simp add: right_def invocation_happensBeforeH_def b1 b2 b3 i_callOriginI_h_simp Let_def )
      by (metis b2 local.i_callOriginI_h_simp option.inject updateHb_simp2)

    ultimately have "(i1,i2) \<in> left \<longleftrightarrow> (i1,i2) \<in> right"
      by simp
  }
  moreover
  {
    text "Next we consider an invocation that is before i"
    fix i1 
    assume b1: "i1 \<noteq> i"

    have "(i1,i)\<in> left \<longleftrightarrow> 
      ((\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
       (\<exists>c. c \<in> set cs \<or> i_callOriginI_h co to c \<triangleq> i) \<and>
       (\<forall>cx cy.
           i_callOriginI_h co to cx \<triangleq> i1 \<and> (cy \<in> set cs \<or> i_callOriginI_h co to cy \<triangleq> i) \<longrightarrow>
           (cx, cy) \<in> updateHb hb vis cs))"
      by (simp add: left_def invocation_happensBeforeH_def b1 i_callOriginI_h_simp)

    moreover have "(i1,i)\<in> right \<longleftrightarrow> 
      ((\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
       (\<exists>c. c \<in> set cs \<or> i_callOriginI_h co to c \<triangleq> i) \<and>
       (\<forall>cx cy.
           i_callOriginI_h co to cx \<triangleq> i1 \<and> (cy \<in> set cs \<or> i_callOriginI_h co to cy \<triangleq> i) \<longrightarrow>
           (cx, cy) \<in> updateHb hb vis cs))"
      apply (auto simp add: right_def invocation_happensBeforeH_def b1 i_callOriginI_h_simp Let_def)
                 apply (auto simp add: updateHb_cases)
    proof goal_cases
      case (1 c ca cx cy)
      then show ?case
        by (metis a11 a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def)
    next
      case (2 c' c ca cx cy)
      then show ?case 
        by (metis (no_types, lifting) a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def local.i_callOriginI_h_simp) 
    next
      case (3 c' c ca cx cy)
      then show ?case 
        by (smt a5 a6 a9 disjoint_iff_not_equal domIff i_callOriginI_h_def inf.idem local.i_callOriginI_h_simp set_empty) 
    next
      case (4 c' c ca cx cy)
      then show ?case
        by (metis a11 a5 disjoint_iff_not_equal domIff i_callOriginI_h_def)  
    next
      case (5 c ca)
      then show ?case
        by (metis FieldI2 a7 disjoint_iff_not_equal local.i_callOriginI_h_simp updateHb_cases updateHb_simp1) 
    next
      case (6 c ca cx cy)
      then show ?case 
        by (metis a6 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def in_sequence_in1 in_sequence_in2 option.inject) 
    next
      case (7 c ca)
      hence "(c, ca) \<in> hb \<or> c \<in> vis \<or> in_sequence cs c ca"
        by blast
      thus False
      proof (elim disjE)
        show "(c, ca) \<in> hb \<Longrightarrow> False"
          using "7"(3) FieldI2 a7 by fastforce
        show "c \<in> vis \<Longrightarrow> False"
          by (metis "7"(1) "7"(3) "7"(4) a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def local.i_callOriginI_h_simp)
        show "in_sequence cs c ca \<Longrightarrow> False"
          by (metis "7"(1) "7"(4) in_sequence_in1 local.i_callOriginI_h_simp)
      qed
    next
      case (8 c ca cx cy)
      then show ?case 
        using b1 by blast 
    next
      case (9 c ca cx cy cxa cya)
      then show ?case 
        by (metis a5 a6 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def in_sequence_in1 option.inject updateHb_cases updateHb_simp2) 
    next
      case (10 c ca cx cy)
      then show ?case 
        by (metis a6 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def in_sequence_in1 in_sequence_in2 option.inject) 
    next
      case (11 c ca cx cy)
      then show ?case 
        using b1 by blast 
    next
      case (12 c ca cx cy cxa cya)
      then show ?case 
        by (metis a5 a6 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def in_sequence_in1 option.inject updateHb_cases updateHb_simp2) 
    qed

    ultimately have "(i1,i) \<in> left \<longleftrightarrow> (i1,i) \<in> right"
      by simp
  }
  moreover 
  { text "Now we consider an invocation that is after i"
    fix i1 
    assume b1: "i1 \<noteq> i"

    have "(i,i1)\<in> left \<longleftrightarrow> 
      ((\<exists>c. c \<in> set cs \<or> i_callOriginI_h co to c \<triangleq> i) \<and>
       (\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
       (\<forall>cx cy.
           (cx \<in> set cs \<or> i_callOriginI_h co to cx \<triangleq> i) \<and> i_callOriginI_h co to cy \<triangleq> i1 \<longrightarrow>
           (cx, cy) \<in> updateHb hb vis cs))"
      by (simp add: left_def invocation_happensBeforeH_def b1 b1[symmetric] i_callOriginI_h_simp)

    moreover 
    have "(i,i1)\<in> right \<longleftrightarrow> 
      ((\<exists>c. c \<in> set cs \<or> i_callOriginI_h co to c \<triangleq> i) \<and>
       (\<exists>c. i_callOriginI_h co to c \<triangleq> i1) \<and>
       (\<forall>cx cy.
           (cx \<in> set cs \<or> i_callOriginI_h co to cx \<triangleq> i) \<and> i_callOriginI_h co to cy \<triangleq> i1 \<longrightarrow>
           (cx, cy) \<in> updateHb hb vis cs))"
      apply (auto simp add: right_def invocation_happensBeforeH_def b1 b1[symmetric] i_callOriginI_h_simp Let_def updateHb_simp_distinct2)

    proof goal_cases
      case (1 c ca cx cy)
      then show ?case
        by (metis a11 a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def) 
    next
      case (2 c ca cx cy)
      then show ?case 
        by (metis a11 a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def)
    next
      case (3 c ca cb cc cx cy)
      then show ?case 
        by (metis a11 a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def) 
    next
      case (4 c ca cb cc cx cy)
      then show ?case 
        by (metis a11 a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def) 
    next
      case (5 c ca)
      then show ?case
        by (metis a2 before_in_list_contains_r local.i_callOriginI_h_simp) 
    next
      case (6 c ca cx cy)
      then show ?case 
        by (metis a11 a5 a6 b1 before_in_list_contains_r disjoint_iff_not_equal domIff i_callOriginI_h_def option.inject)
    next
      case (7 c ca c')
      then show ?case
        by (metis a5 a6 disjoint_iff_not_equal domIff i_callOriginI_h_def local.i_callOriginI_h_simp)
    next
      case (8 c ca c' cx cy)
      then show ?case 
        by (metis a11 a5 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def option.inject) 
    next
      case (9 c ca cx cy)
      then show ?case 
        by (metis a11 a5 a6 b1 before_in_list_contains_r disjoint_iff_not_equal domIff i_callOriginI_h_def option.inject)
    next
      case (10 c ca c' cx cy)
      then show ?case
        by (metis a11 a5 b1 disjoint_iff_not_equal domIff i_callOriginI_h_def option.inject) 
    qed
    ultimately have "(i,i1)\<in> left \<longleftrightarrow> (i,i1)\<in> right"
      by simp

  }
  moreover
  {
    fix i1
    have "(i1,i1)\<in> left \<longleftrightarrow> (i1,i1)\<in>right"
      by (auto simp add: left_def right_def invocation_happensBeforeH_def i_callOriginI_h_simp Let_def)
  }

  ultimately have "(i1,i2)\<in> left \<longleftrightarrow> (i1,i2) \<in> right" for i1 i2
    by metis
  thus "?left = ?right"
    by (auto simp add: left_def right_def)
qed  





end