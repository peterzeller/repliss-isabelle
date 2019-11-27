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
  firstTx
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
       \<longrightarrow> (firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed ))
       \<longrightarrow> traceCorrect_s  trace)"

lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, rotated]

lemma beforeInvoc_execution_s_check: 
  assumes "s_invocationOp i = None"
  shows "
execution_s_check   progr   i  s_calls   s_happensBefore   s_callOrigin   s_transactionOrigin   s_knownIds   s_invocationOp  s_invocationRes  generatedLocal  vis localCalls  tx firstTx ls
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
    and firstTx_def: "(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed ))"
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
  firstTx
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
    show "firstTx = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed)"
      using firstTx_def by auto

  qed
qed


lemma execution_s_check_sound2:
  assumes a1: "localState S i \<triangleq> ls"
    and a2: "S \<in> initialStates progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
\<lbrakk>
s_invocationOp i = invocationOp S i;
s_invocationRes i = None
\<rbrakk> \<Longrightarrow>
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
  True
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
     (invocationRes S) {} {} [] (currentTransaction S i) True ls "
    unfolding currentTx
  proof (rule c)
    show "invocationOp S i = invocationOp S i" by simp
    show "invocationRes S i = None"
      by (simp add: a1 local.wf state_wellFormed_no_result_when_running)
  qed

  show "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    using a2 initialState_noTxns1 by blast

  show "True = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed)"
    by (meson \<open>visibleCalls S i \<triangleq> {}\<close> empty_iff local.wf state_wellFormed_ls_visibleCalls_callOrigin)

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
  firstTx
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
  firstTx
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
            firstTx
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
s_transactionOrigin' tx = None;
\<And>i op. s_invocationOp i \<triangleq> op \<Longrightarrow> s_invocationOp' i \<triangleq> op

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
  firstTx
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
  firstTx
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
     (invocationOp S'a) (invocationRes S'a) {x. generatedIds S'a x \<triangleq> i} vis'' [] (Some t) firstTx (cont ())"
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

        show "\<And>i op. s_invocationOp i \<triangleq> op \<Longrightarrow> invocationOp S'a i \<triangleq> op"
          apply(simp add: S'a_def)
          using Step(7) growth state_monotonicGrowth_invocationOp by blast



      qed
      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        apply (auto simp add: S'a_def)
        apply (smt Step(1) c15 c16 c17 c4 c8 consistentSnapshotH_def growth in_dom state_monotonicGrowth_callOrigin state_wellFormed_ls_visibleCalls_callOrigin wellFormed_callOrigin_dom wellFormed_currentTransaction_unique_h(2) wellFormed_state_consistent_snapshot wellFormed_state_transaction_consistent(1) wf_S')
        by (metis Step(1) c5 growth state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin state_monotonicGrowth_transactionStatus2 wf_callOrigin_implies_transactionStatus_defined)


    qed (auto simp add: S'a_def Step)
  qed
qed



lemma execution_s_check_endAtomic:
  assumes "program_wellFormed progr"
    and "s_transactionOrigin tx = None"
    and tx_nonempty: "localCalls \<noteq> []"
and assert_inv: "
\<lbrakk>
invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore })
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
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore });
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
  False
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
  firstTx
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

      have "localCalls \<noteq> []"
        by (simp add: tx_nonempty)
      have "distinct localCalls"
        by (simp add: Step(21))
      have  co_tx_none: "\<forall>c\<in>set localCalls. s_callOrigin c = None"
        using Step(19) by blast
      have to_tx_none: " s_transactionOrigin tx = None"
        by (simp add: assms(2))
      have co_not_tx: "\<And>c. s_callOrigin c \<noteq> Some tx"
        using Step(16) Step(4) co_tx_none map_update_all_Some_same by fastforce

      have hb_wf_l:"\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c \<triangleq> t"
        find_theorems s_happensBefore happensBefore
        sorry (* TODO wf property should be maintained *)
      have hb_wf_r: "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c' \<triangleq> t"
        sorry (* TODO wf property should be maintained *)

      have  invocation_hb_simp:
        "invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore })"
      proof (rule if_cases)
        assume firstTx


        show "invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)))
           (updateHb s_happensBefore vis localCalls) =
          invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore \<union>
          {i' |  i' c'.
              c' \<in> vis \<and>
              i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and>
              (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis)} \<times>
          {i}"
          using `localCalls \<noteq> []` 
            `distinct localCalls` co_tx_none to_tx_none co_not_tx hb_wf_l hb_wf_r
        proof (fuzzy_rule invocation_happensBeforeH_one_transaction_simp2)
          
          show "\<And>t. s_transactionOrigin t \<noteq> Some i"
            using `firstTx`
            sorry (* TODO there could be empty transactions? *)
          
  

        qed auto
      next
        assume "\<not> firstTx"
        from this obtain old_c old_t 
          where "s_callOrigin old_c \<triangleq> old_t"
            and "s_transactionOrigin old_t \<triangleq> i"
            and "transactionStatus S1 old_t \<triangleq> Committed"
          using Step(22) Step(4) Step(5) allCommitted2 map_update_all_Some_other by fastforce


        show " invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)))
     (updateHb s_happensBefore vis localCalls) =
    invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore -
    {i} \<times> {i'. (i, i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore}"
          using tx_nonempty `s_transactionOrigin old_t \<triangleq> i` co_tx_none `s_callOrigin old_c \<triangleq> old_t`
                hb_wf_l co_not_tx
        proof (fuzzy_rule invocation_happensBeforeH_more_transactions_simp2)

          show "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> (c, c') \<in> s_happensBefore"
            by simp

          show "Field s_happensBefore \<inter> set localCalls = {}"
            by (simp add: Step(20))

          show "\<And>c. i_callOriginI_h s_callOrigin s_transactionOrigin c \<triangleq> i \<Longrightarrow> c \<in> vis"
            sorry (* TODO wf *)

          show "\<And>c c'. \<lbrakk>c' \<in> vis; (c, c') \<in> s_happensBefore\<rbrakk> \<Longrightarrow> c \<in> vis"
          proof -
            fix c :: callId and c' :: callId
            assume a1: "c' \<in> vis"
            assume a2: "(c, c') \<in> s_happensBefore"
            have f3: "\<forall>c. c \<notin> Field s_happensBefore \<or> (\<forall>ca. ca \<notin> set localCalls \<or> c \<noteq> ca)"
              using Step(20) by auto
            have f4: "c' \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI2)
            have "c \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI1)
            then show "c \<in> vis"
              using f4 f3 a2 a1 by (metis (no_types) Step(1) Step(13) Step(3) UnCI UnE updateHb_simp2 wf_vis_downwards_closed2)
          qed



        qed
      qed


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
       {x. generatedIds S'a x \<triangleq> i} (vis \<union> set localCalls) [] None False (cont ())"
      using invocation_hb_simp proof (fuzzy_rule cont; (simp add: S'a_def Step)?)
        show "invariant progr
     \<lparr>calls = s_calls, happensBefore = updateHb s_happensBefore vis localCalls,
        callOrigin =  map_update_all s_callOrigin localCalls tx,
        transactionOrigin = s_transactionOrigin(tx \<mapsto> i), knownIds = s_knownIds,
        invocationOp = s_invocationOp, invocationRes = s_invocationRes\<rparr>"
          using invocation_hb_simp  by (rule assert_inv)
      qed

      obtain c where "c\<in>set localCalls"
        using `localCalls \<noteq> []` by fastforce



      show "False = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        using  \<open>c \<in> set localCalls\<close>  by (auto simp add: S'a_def intro!: exI[where x=c] exI[where x=tx]
            Step(1) Step(14) state_wellFormed_current_transaction_origin
            Step(4) map_update_all_Some_same, simp add: Step(4) map_update_all_Some_same) 



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
  firstTx
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
  firstTx
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
     s_invocationOp s_invocationRes {x. generatedIds S1 x \<triangleq> i} vis localCalls tx firstTx (cont ())"
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
  firstTx
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
  firstTx
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
       (localCalls @ [c]) (Some tx) firstTx (cont res)"
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

      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        apply auto
         apply (auto simp add: S'a_def split: if_splits)
        using Step(1) c2 not_uncommitted_cases wellFormed_currentTransaction_unique_h(2) apply blast
        using \<open>callOrigin S1 c = None\<close> by force


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
  firstTx
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
        using `trace = (action, Inv) # trace'` `\<forall>p t. (AInvoc p, t) \<notin> set trace` a_def local.Cons by auto



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





end