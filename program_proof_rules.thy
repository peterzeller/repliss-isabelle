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

thm execution_s_correct_def
  (*
 execution_s_correct ?progr ?S ?i \<equiv> \<forall>trace S'. ?S ~~ (?i, trace) \<leadsto>\<^sub>S* S' \<longrightarrow> traceCorrect_s ?progr trace
*)

(* TODO utils*)
(* List is sorted wrt. a partial order *)


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
       \<longrightarrow> callOrigin S1 = s_callOrigin ++ (Map.map_of (map (\<lambda>c. (c, the tx)) localCalls))
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
        using Step(21) Step(24) by auto

      show "state_wellFormed S'a"
        using Step(1) Step(22) state_wellFormed_combine_s1 by blast

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
      invocationRes = s_invocationRes'\<rparr>
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

      show "callOrigin S'a = (callOrigin S'a) ++ map_of (map (\<lambda>c. (c, the (Some t))) [])"
        by simp

      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step(21) Step(24) by auto


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

 (* TODO move to utils *) 
lemma exists_cases1: 
  shows "(\<exists>x. (x = A \<longrightarrow> P x) \<and> (x \<noteq> A \<longrightarrow> Q x)) 
    \<longleftrightarrow>  (P A) \<or> (\<exists>x. x \<noteq> A \<and> Q x)"
  by auto

lemma exists_cases2: 
  shows "(\<exists>x. (x \<noteq> A \<longrightarrow> Q x) \<and> (x = A \<longrightarrow> P x)) 
    \<longleftrightarrow>  (P A) \<or> (\<exists>x. x \<noteq> A \<and> Q x)"
  by auto

lemma execution_s_check_endAtomic:
  assumes "program_wellFormed progr"
and assert_inv: "invariant progr 
     \<lparr>calls = s_calls, 
      happensBefore = updateHb s_happensBefore vis localCalls,
      callOrigin = s_callOrigin ++ (Map.map_of (map (\<lambda>c. (c, tx)) localCalls)),
      transactionOrigin = s_transactionOrigin, 
      knownIds = s_knownIds,
      invocationOp = s_invocationOp, 
      invocationRes = s_invocationRes\<rparr>"
    and cont: "
\<comment> \<open>

\<close>
\<lbrakk>True
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls 
  (updateHb s_happensBefore vis localCalls) 
  (s_callOrigin ++ (Map.map_of (map (\<lambda>c. (c, tx)) localCalls))) 
  s_transactionOrigin
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
  s_transactionOrigin 
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
      

      have h3: "s_callOrigin ++ map_of (map (\<lambda>c. (c, tx)) localCalls) = callOrigin S1 |` dom (calls S1)"
        apply (simp add: Step)
        apply (subst restrict_map_noop)
         apply auto
        using Step(1) Step(2) Step(4) wellFormed_callOrigin_dom by fastforce+


      have h4: "s_transactionOrigin =
        transactionOrigin S1 |` {t. t \<noteq> tx \<longrightarrow> transactionStatus S1 t \<triangleq> Committed}"
        apply (simp add: Step )
        apply (subst restrict_map_noop)
         apply auto
        by (simp add: Step(1) Step(5) allCommitted2 wf_transaction_status_iff_origin)




    show "Inv"
      unfolding Inv_def 
      by (fuzzy_rule assert_inv, auto simp add: invContextH_def committedCallsH_simp h1 h2 h3 h4  del: equalityI; auto simp add: Step)

    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      thm use_execution_s_check
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step(21) Step(24) by auto

      show "currentTransaction S'a i = None"
        by (simp add: S'a_def)

      show "state_wellFormed S'a"
        using S'a_wf by auto

      show "happensBefore S'a = updateHb (happensBefore S'a) (vis\<union>set localCalls)  []"
        by simp

      show "callOrigin S'a = callOrigin S'a ++ map_of (map (\<lambda>c. (c, the None)) [])"
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
        by (fuzzy_rule cont; (simp add: S'a_def Step))

    qed (simp add: S'a_def Step)+
  qed
qed

                   apply_end (rule refl)+
               apply_end (simp add: S'a_def Step)
              apply_end (simp add: S'a_def Step)
      apply_end (simp add: S'a_def Step)
      apply_end (simp add: S'a_def Step)
      apply_end (simp add: S'a_def Step)
      apply_end (simp add: S'a_def Step)


    proof (fuzzy_rule cont)


proof (rule  execution_s_check_single_step, auto simp add: step_s.simps split: if_splits, goal_cases "inv" "goal")
  case (inv S1 y t)

  have [simp]: "prog S1 = progr" using inv by simp

  have all_committed: "transactionStatus S1 tx \<triangleq> Committed"
    if "tx \<noteq> t" 
      and "callOrigin S1 x \<triangleq> tx"
    for tx x
    apply (case_tac "transactionStatus S1 tx")
     apply auto
    using inv(5) that(2) wf_no_transactionStatus_origin_for_nothing apply blast
    using inv(6) that(1) transactionStatus.exhaust by force

  have committedCalls_simp: "committedCallsH (callOrigin S1) (transactionStatus S1(t \<mapsto> Committed)) = dom s_calls"
    apply (auto simp add: committedCallsH_def isCommittedH_def all_committed)
    using inv(5) inv(7) wellFormed_callOrigin_dom apply fastforce
      apply (simp add: inv(5) inv(7) wellFormed_callOrigin_dom2)
    using inv(17) inv(5) not_uncommitted_cases wellFormed_currentTransaction_unique_h(2) apply blast
    by (metis all_committed inv(5) inv(7) option.exhaust option.simps(3) wf_callOrigin_and_calls)

  show ?case
  proof (simp add: invContextH_def, rule back_subst[where P="invariant progr", OF assert_inv], auto simp add: inv committedCalls_simp)
    show "\<And>a b. (a, b) \<in> happensBefore S1 \<Longrightarrow> (a, b) \<in> happensBefore S1 |r dom (calls S1)"
      by (simp add: happensBefore_in_calls_left happensBefore_in_calls_right inv(5) restrict_relation_def)
    show "\<And>a b. (a, b) \<in> happensBefore S1 |r dom (calls S1) \<Longrightarrow> (a, b) \<in> happensBefore S1"
      by (simp add: happensBefore_in_calls_left happensBefore_in_calls_right inv(5) restrict_relation_def)

    show "callOrigin S1 = callOrigin S1 |` dom (calls S1)"
      by (metis inv(5) restrict_map_noop2 wellFormed_callOrigin_dom)

    show "transactionOrigin S1 = transactionOrigin S1 |` {ta. ta \<noteq> t \<longrightarrow> transactionStatus S1 ta \<triangleq> Committed}"
      apply (subst restrict_map_noop, auto)
      by (metis  inv(5) inv(6) not_uncommitted_cases option.exhaust option.simps(3) wf_transactionOrigin_and_status)
  qed
next
  case (goal S1 y t)
  show ?case 
  proof (rule back_subst13[where P=execution_s_check], rule cont; (simp add: goal)?)
  qed
qed






(*
lemma proof_rule_soundness:

  assumes "\<And>x v. \<lbrakk>P x v\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  (s_calls' x)
  (s_happensBefore' x)
  (s_callOrigin' x)
  (s_transactionOrigin' x)
  (s_knownIds' x)
  (s_invocationOp' x)
  (s_invocationRes' x)
  (vis' x)
  (tx' x)
  (cont v)"

shows"execution_s_check
  progr 
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  vis
  tx
  (A \<bind> cont)
"
*)
lemma execution_s_check_single_step:
  assumes H: "\<And>S1 action Inv S' localCalls'. \<lbrakk>
  S1 ~~ (i,action,Inv) \<leadsto>\<^sub>S S';
  invocationOp S1 i \<noteq> None;
  calls S1 = s_calls;
  happensBefore S1 = updateHb s_happensBefore vis localCalls;
  callOrigin S1 = s_callOrigin ++ (Map.map_of (map (\<lambda>c. (c,the tx)) localCalls));
  transactionOrigin S1 = s_transactionOrigin;
  knownIds S1 = s_knownIds;
  invocationOp S1 = s_invocationOp;
  invocationRes S1 = s_invocationRes;
  prog S1 = progr;
  generatedLocal = {x. generatedIds S1 x \<triangleq> i};
  localState S1 i \<triangleq> ls;
  currentProc S1 i \<triangleq> toImpl;
  visibleCalls S1 i \<triangleq>  (vis \<union> set localCalls);
  currentTransaction S1 i = tx;
  state_wellFormed S1;
  vis \<inter> set localCalls = {};
  dom s_callOrigin \<inter> set localCalls = {};
  Field s_happensBefore \<inter> set localCalls = {};
  sorted_by (updateHb s_happensBefore vis localCalls) localCalls;
  (case currentTransaction S1 i of Some tx' \<Rightarrow> set localCalls =  {c. callOrigin S1 c \<triangleq> tx'} | None \<Rightarrow> localCalls = []);
  \<And>tx'. tx \<noteq> Some tx' \<Longrightarrow>  transactionStatus S1 tx' \<noteq> Some Uncommitted;
  localCalls' \<noteq> localCalls \<Longrightarrow> sorted_by (updateHb s_happensBefore vis localCalls') localCalls'
    \<and> (case currentTransaction S' i of Some tx' \<Rightarrow> set localCalls' =  {c. callOrigin S' c \<triangleq> tx'} | None \<Rightarrow> localCalls' = [])
\<rbrakk> \<Longrightarrow> 
  Inv
\<and> (case localState S' i of
    None \<Rightarrow> True
  | Some LS' \<Rightarrow>
    execution_s_check
    progr 
    i
    (calls S')
    (happensBefore S' |r (dom (calls S') - set localCalls')) 
    (callOrigin S' |` (dom (calls S') - set localCalls')) 
    (transactionOrigin S')
    (knownIds S')
    (invocationOp S')
    (invocationRes S')
    {x. generatedIds S' x \<triangleq> i}
    (case visibleCalls S' i of Some vis \<Rightarrow> vis - set localCalls' | None \<Rightarrow> {})
    localCalls'
    (currentTransaction S' i)
    LS')
"
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
  generatedLocal
  vis
  localCalls
  tx
  ls
"
proof (cases "s_invocationOp i")
  case None
  then show ?thesis
    by (simp add: beforeInvoc_execution_s_check) 
next
  case (Some action)

  show ?thesis
  proof (auto simp add: execution_s_check_def, goal_cases "A")
    case (A trace S1 S')
    (*fix trace S1 S'
    assume a0: "S1 ~~ (i, trace) \<leadsto>\<^sub>S* S'"
      and a1: "\<forall>p t. (AInvoc p, t) \<notin> set trace"
      and a2: "state_wellFormed S1"
      and a3: "s_calls = calls S1"
      and a4: "s_happensBefore = happensBefore S1"
      and a5: "s_callOrigin = callOrigin S1"
      and a6: "s_transactionOrigin = transactionOrigin S1"
      and a7: "s_knownIds = knownIds S1"
      and a8: "s_invocationOp = invocationOp S1"
      and a9: "s_invocationRes = invocationRes S1"
      and a10: "progr = prog S1"
      and a11: "generatedLocal = {x. generatedIds S1 x \<triangleq> i}"
      and a12: "localState S1 i \<triangleq> ls"
      and a13: "currentProc S1 i \<triangleq> toImpl"
      and a14: "visibleCalls S1 i \<triangleq> vis"
      and a15: "tx = currentTransaction S1 i"*)


    show "traceCorrect_s  trace"
    proof (cases trace)
      case Nil
      then show ?thesis
        by (simp add: traceCorrect_s_empty) 

    next
      case (Cons a trace')
      obtain action Inv where a_def[simp]: "a = (action, Inv)" by force

      from `S1 ~~ (i, trace) \<leadsto>\<^sub>S* S'`
      obtain S1'
        where step: "S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S1'" 
          and steps: "S1' ~~ (i, trace') \<leadsto>\<^sub>S* S'"
          and trace_split: "trace = (action,Inv)#trace'"
        using a_def local.Cons steps_s_cons_simp by blast


      have gI: "\<forall>x\<in>generatedLocal. generatedIds S1 x \<triangleq> i"
        using A by blast

      have hasInvoc: "invocationOp S1 i \<noteq> None"
        using Some A by auto

      have wf: "state_wellFormed S1"
        using A by auto

      have wf': "state_wellFormed S1'"
        using local.step local.wf state_wellFormed_combine_s1 by blast

      have "trans (happensBefore S1')"
        by (simp add: happensBefore_transitive wf')

      have "irrefl (happensBefore S1')"
        by (simp add: happensBefore_irrefl wf')

      have "finite {c. callOrigin S1' c \<triangleq> a}" for a
      proof (rule finite_subset)
        show "{c. callOrigin S1' c \<triangleq> a} \<subseteq> dom (callOrigin S1')" 
          by auto
        show "finite (dom (callOrigin S1'))"
          by (simp add: wellFormed_callOrigin_dom wf' wf_finite_calls)
      qed



      obtain localCalls'
        where localCalls'_def: "case currentTransaction S1' i of None \<Rightarrow> localCalls' = [] | Some tx' \<Rightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> tx'} "
          and localCalls'_sorted: "sorted_by (happensBefore S1') localCalls'"
        apply atomize_elim
        apply (cases "currentTransaction S1' i")
         apply (auto simp add: sorted_by_empty)
        using `\<And>a. finite {c. callOrigin S1' c \<triangleq> a}`  `trans (happensBefore S1')` `irrefl (happensBefore S1')` 
        by (rule exists_sorted_by_irrefl)

      have localCalls'_empty:
        "localCalls' = [] \<longleftrightarrow> (case currentTransaction S1' i of  None \<Rightarrow> True | Some tx \<Rightarrow> \<nexists>c. callOrigin S1' c \<triangleq> tx)"
        using localCalls'_def by (auto split: option.splits)

      have localCalls'_set:
        "set localCalls' = S \<longleftrightarrow> (case currentTransaction S1' i of  None \<Rightarrow> S = {}  | Some tx \<Rightarrow> \<forall>c. callOrigin S1' c \<triangleq> tx \<longleftrightarrow> c\<in>S)" for S
        using localCalls'_def by (auto split: option.splits)

      from step
      have appliedH1: "Inv \<and>
    (case localState S1' i of None \<Rightarrow> True
     | Some LS' \<Rightarrow>
         execution_s_check progr i 
              (calls S1') 
              (happensBefore S1' |r (dom (calls S1') - set localCalls')) 
              (callOrigin S1' |` (dom (calls S1') - set localCalls')) 
              (transactionOrigin S1') 
              (knownIds S1') 
              (invocationOp S1')
              (invocationRes S1') 
              {x. generatedIds S1' x \<triangleq> i} 
              (case visibleCalls S1' i of None \<Rightarrow> {} | Some vis \<Rightarrow> vis - set localCalls')
              localCalls' 
              (currentTransaction S1' i) 
              LS')"
      proof (rule H[where localCalls'=localCalls']; (simp add: A hasInvoc wf localCalls'_def)?)



        show "sorted_by (updateHb s_happensBefore vis localCalls') localCalls'"
          if c0: "localCalls' \<noteq> localCalls"
            and c1: "S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S1'"
        proof (rule sorted_by_updateHb)
          show "set localCalls' \<inter> vis = {}"

            using localCalls'_def
            apply (auto simp add: split: option.splits)

            sorry
          show "set localCalls' \<inter> Field s_happensBefore = {}"



      hence Inv
        by simp

      

      show ?thesis
        unfolding trace_split 
      proof (rule traceCorrect_s_split; (simp add: `Inv`)?)

        show "traceCorrect_s trace'"

        proof (cases "localState S1' i")
          case None

          with steps have "trace' = []"
            using local_state_None_no_more_steps
            by (metis A insert_iff list.simps(15) local.Cons no_more_invoc option.simps(3)) 


          then show ?thesis
            using traceCorrect_s_empty by blast


        next
          case (Some LS')


          from step
          have appliedH: "Inv \<and>
            (case localState S1' i of None \<Rightarrow> True
             | Some LS' \<Rightarrow>
                 execution_s_check progr i 
                    (calls S1') 
                    (happensBefore S1' |r (dom (calls S1') - set localCalls')) 
                    (callOrigin S1' |` (dom (calls S1') - set localCalls')) 
                    (transactionOrigin S1') 
                    (knownIds S1') 
                    (invocationOp S1')
                    (invocationRes S1') 
                    {x. generatedIds S1' x \<triangleq> i} 
                    (case visibleCalls S1' i of None \<Rightarrow> {} | Some vis \<Rightarrow> vis - set localCalls')
                    localCalls' 
                    (currentTransaction S1' i) 
                    LS')"
          proof (fuzzy_rule H; (simp add: A; fail)?)
            show "invocationOp S1 i \<noteq> None"
              by (simp add: hasInvoc)

            show "localCalls' = localCalls \<Longrightarrow>
              sorted_by (updateHb s_happensBefore vis localCalls) localCalls' \<and>
              (case tx of None \<Rightarrow> localCalls' = [] | Some tx' \<Rightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> tx'})"
            proof (auto simp add: split: option.splits)
              show "\<lbrakk>localCalls' = localCalls; tx = None\<rbrakk> \<Longrightarrow> sorted_by (updateHb s_happensBefore vis localCalls) localCalls"
                by (simp add: A(19))
              show "\<lbrakk>localCalls' = localCalls; tx = None\<rbrakk> \<Longrightarrow> localCalls = []"
                using A(16) A(18) by auto

              show "sorted_by (updateHb s_happensBefore vis localCalls) localCalls"
                if c0: "localCalls' = localCalls"
                  and c1: "tx \<triangleq> x2"
                for  x2
                by (simp add: A(19))


              show "callOrigin S1' x \<triangleq> x2"
                if c0: "localCalls' = localCalls"
                  and c1: "tx \<triangleq> x2"
                  and c2: "x \<in> set localCalls"
                for  x2 x
                using A(16) c0 c1 c2 localCalls'_def by force


              show "x \<in> set localCalls"
                if c0: "localCalls' = localCalls"
                  and c1: "tx \<triangleq> x2"
                  and c2: "callOrigin S1' x \<triangleq> x2"
                for  x2 x
                using A(16) c0 c1 c2 localCalls'_def by force
            qed
          qed

          have transactionOrigin_unchanged:
              "transactionOrigin S1' tx \<triangleq> i"
            if "transactionOrigin S1 tx \<triangleq> i"
            for tx i
            using step  that
            apply (auto simp add: hasInvoc step_s.simps local.wf state_wellFormed_transactionStatus_transactionOrigin)
            using state_monotonicGrowth_transactionOrigin by blast



          from Some and appliedH 
          have "execution_s_check progr i (calls S1') (happensBefore S1' |r (dom (calls S1') - set localCalls'))
              (callOrigin S1' |` (dom (calls S1') - set localCalls')) (transactionOrigin S1') (knownIds S1') (invocationOp S1') (invocationRes S1')
              {x. generatedIds S1' x \<triangleq> i} (case visibleCalls S1' i of None \<Rightarrow> {} | Some vis \<Rightarrow> vis - set localCalls') localCalls'
              (currentTransaction S1' i) LS'"
            by auto

          with steps
          show ?thesis
          proof (fuzzy_rule execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]; (simp; fail)?)
            find_theorems "S1'"

            show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
              using Some local.step local.wf no_more_invoc state_wellFormed_combine_s1 steps by fastforce
            show "state_wellFormed S1'"
              using A local.step state_wellFormed_combine_s1 by blast
            show "prog S1' = progr"
              by (metis A(1) A(11) steps unchangedProg)
            show "localState S1' i \<triangleq> LS'"
              by (simp add: Some)

            show "happensBefore S1' =
                updateHb (happensBefore S1' |r (dom (calls S1') - set localCalls'))
                 (case visibleCalls S1' i of None \<Rightarrow> {} | Some vis \<Rightarrow> vis - set localCalls') localCalls'"
              sorry

            show "callOrigin S1' =
    callOrigin S1' |` (dom (calls S1') - set localCalls') ++ map_of (map (\<lambda>c. (c, the (currentTransaction S1' i))) localCalls')"
              sorry

            show "currentProc S1' i \<triangleq> toImpl"
              using step Some by (auto simp add: step_s.simps A wf_localState_to_invocationOp)

            show " visibleCalls S1' i \<triangleq> ((case visibleCalls S1' i of None \<Rightarrow> {} | Some vis \<Rightarrow> vis - set localCalls') \<union> set localCalls')"
            proof (cases "visibleCalls S1' i")
              case None
              then show ?thesis
                by (metis Some option.simps(3) state_wellFormed_ls_visibleCalls wf') 
            next
              case (Some vis)
              then show ?thesis
                apply auto
                using localCalls'_def apply (auto simp add:  split: option.splits)
                using local.wf state_wellFormed_current_transaction_origin state_wellFormed_ls_visibleCalls_callOrigin transactionOrigin_unchanged wf' by blast

            qed

            show " \<And>tx'. currentTransaction S1' i \<noteq> Some tx' \<Longrightarrow> transactionStatus S1' tx' \<noteq> Some Uncommitted"
              using step  Some  by (auto simp add: step_s.simps A wf_localState_to_invocationOp localCalls'_def split: option.splits if_splits)

            show "sorted_by (happensBefore S1') localCalls'"
              by (simp add: localCalls'_sorted)

            have same_tx: "\<lbrakk>currentTransaction S1 i \<triangleq> tx; currentTransaction S1' i \<triangleq> tx'\<rbrakk> \<Longrightarrow> tx = tx'" for tx tx'
              using step hasInvoc by (auto simp add: step_s.simps)


            show "case currentTransaction S1' i of None \<Rightarrow> localCalls' = [] | Some tx' \<Rightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> tx'}"
            proof (case_tac " currentTransaction S1 i"; case_tac " currentTransaction S1' i"; simp add: localCalls'_empty localCalls'_set)
              show "\<And>a. \<lbrakk>currentTransaction S1 i = None; currentTransaction S1' i \<triangleq> a\<rbrakk> \<Longrightarrow> \<forall>x. callOrigin S1' x \<noteq> Some a"
                using step hasInvoc by (auto simp add: step_s.simps)
              show "\<And>a. \<lbrakk>currentTransaction S1 i \<triangleq> a; currentTransaction S1' i = None\<rbrakk> \<Longrightarrow> \<forall>c. callOrigin S1' c \<noteq> Some a"


              show "\<And>a. \<lbrakk>currentTransaction S1 i = None; currentTransaction S1' i \<triangleq> a\<rbrakk> \<Longrightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> a}"
                using localCalls'_def apply (simp add: localCalls_empty)


              show " \<lbrakk>currentTransaction S1 i = None; currentTransaction S1' i = None\<rbrakk> \<Longrightarrow> localCalls' = []"
                using localCalls'_def by simp
              show " \<And>a. \<lbrakk>currentTransaction S1 i = None; currentTransaction S1' i \<triangleq> a\<rbrakk> \<Longrightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> a}"
                using localCalls'_def  step hasInvoc by (auto simp add: step_s.simps)
              show "\<And>a. \<lbrakk>currentTransaction S1 i \<triangleq> a; currentTransaction S1' i = None\<rbrakk> \<Longrightarrow> localCalls' = []"
                using localCalls'_def  step hasInvoc apply (auto simp add: step_s.simps)

                sorry
              show "\<And>a aa. \<lbrakk>currentTransaction S1 i \<triangleq> a; currentTransaction S1' i \<triangleq> aa\<rbrakk> \<Longrightarrow> set localCalls' = {c. callOrigin S1' c \<triangleq> aa}"
                using localCalls'_def same_tx by fastforce


            show "case currentTransaction S1' i of None \<Rightarrow> localCalls' = [] | Some tx' \<Rightarrow> set localCalls' = {c. callOrigin S' c \<triangleq> tx'}"
              using localCalls'_def 
              sorry

            show "visibleCalls S1' i \<triangleq> (visibleCalls S1' i orElse {} \<union> set localCalls')"
              using step  Some  apply (auto simp add: step_s.simps A wf_localState_to_invocationOp localCalls'_def split: option.splits)

              sledgehammer
              apply (metis A(17) not_uncommitted_cases option.sel)
              sorry
            show "\<And>tx'. currentTransaction S1' i \<noteq> Some tx' \<Longrightarrow> transactionStatus S1' tx' \<noteq> Some Uncommitted"
              using step Some  by (auto simp add: step_s.simps A wf_localState_to_invocationOp split: option.splits if_splits)



          qed auto
        qed
      qed
    qed
  qed
qed


end