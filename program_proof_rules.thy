section "Program Proof Rules"

theory program_proof_rules
  imports 
    invariant_simps 
    unique_ids2
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language
    topological_sort
    program_verification_tactics
begin

text "We define some proof rules for our implementation languages, so that 
we can automate the generation of verification conditions.

The proof rules can simulate symbolic execution of a procedure.
We add some additional state compared to the system state in the semantics, so that we can derive
additional assumptions for the verification conditions."

definition execution_s_check where
  "execution_s_check 
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_txOrigin 
  s_knownIds 
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
       \<longrightarrow> txOrigin S1 = s_txOrigin
       \<longrightarrow> knownIds S1 = s_knownIds
       \<longrightarrow> invocOp S1 = s_invocOp
       \<longrightarrow> invocRes S1 = s_invocRes
       \<longrightarrow> prog S1 = progr
       \<longrightarrow> generatedLocal = {x. generatedIds S1 x \<triangleq> i}
       \<longrightarrow> localState S1 i \<triangleq> ls
       \<longrightarrow> currentProc S1 i \<triangleq> toImpl
       \<longrightarrow> visibleCalls S1 i \<triangleq>  (vis \<union> set localCalls)
       \<longrightarrow> currentTx S1 i = tx
       \<longrightarrow> (\<forall>tx'. tx \<noteq> Some tx' \<longrightarrow> txStatus S1 tx' \<noteq> Some Uncommitted)
       \<longrightarrow> (case tx of Some tx' \<Rightarrow> set localCalls =  {c. callOrigin S1 c \<triangleq> tx'} | None \<Rightarrow> localCalls = [])
       \<longrightarrow> (sorted_by (happensBefore S1) localCalls)
       \<longrightarrow> (vis \<inter> set localCalls = {})
       \<longrightarrow> (dom s_callOrigin \<inter> set localCalls = {})
       \<longrightarrow> (Field s_happensBefore \<inter> set localCalls = {})
       \<longrightarrow> distinct localCalls
       \<longrightarrow> (firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S1 c \<triangleq> tx \<and> txOrigin S1 tx \<triangleq> i \<and> txStatus S1 tx \<triangleq> Committed ))
       \<longrightarrow> (\<forall>c. i_callOriginI_h s_callOrigin s_txOrigin c \<triangleq> i \<longrightarrow> c \<in> vis)
       \<longrightarrow> (generatedLocalPrivate \<subseteq> generatedLocal)
       \<longrightarrow> (\<forall>v\<in>generatedLocalPrivate. uid_is_private i S1 v)
       \<longrightarrow> traceCorrect_s  trace)"

lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, rotated]

lemma beforeInvoc_execution_s_check: 
  assumes "s_invocOp i = None"
  shows "
execution_s_check   progr   i  s_calls   s_happensBefore   s_callOrigin   s_txOrigin   s_knownIds   s_invocOp  s_invocRes  generatedLocal generatedLocalPrivate  vis localCalls  tx firstTx ls
"
  using assms 
  by (auto simp add: execution_s_check_def steps_s_cons_simp Let_def wf_localState_to_invocOp)





text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"



lemma execution_s_check_sound:
  assumes ls_def: "localState S i \<triangleq> ls"
    and vis_def: "visibleCalls S i \<triangleq> vis"
    and progr_def: "prog S = progr"
    and toImpl: "currentProc S i \<triangleq> toImpl"
    and generatedLocal: "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and generatedLocalPrivate1: "generatedLocalPrivate \<subseteq> generatedLocal"
    and generatedLocalPrivate2: "\<forall>v\<in>generatedLocalPrivate. uid_is_private i S v"
    and S_wf: "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTx S i \<noteq> Some tx' \<longrightarrow> txStatus S tx' \<noteq> Some Uncommitted"
    and no_currentTxn: "currentTx S i = None"
    and firstTx_def: "(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S c \<triangleq> tx \<and> txOrigin S tx \<triangleq> i \<and> txStatus S tx \<triangleq> Committed ))"
    and c: "execution_s_check 
  progr 
  i
  (calls S)
  (happensBefore S)
  (callOrigin S)
  (txOrigin S)
  (knownIds S)
  (invocOp S)
  (invocRes S)
  generatedLocal
  generatedLocalPrivate
  vis
  []
  (currentTx S i)
  firstTx
  ls"
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume a0: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"


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

    show "currentTx S i \<noteq> Some tx' \<Longrightarrow> txStatus S tx' \<noteq> Some Uncommitted" for tx'
      by (simp add: assms)

    show "visibleCalls S i \<triangleq> (vis \<union> set [])"
      by (simp add: assms)

    show "case currentTx S i of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S c \<triangleq> tx'}"
      by (simp add: no_currentTxn)

    show "sorted_by (happensBefore S) []"
      by (simp add: sorted_by_empty)
    show "firstTx = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> txOrigin S tx \<triangleq> i \<and> txStatus S tx \<triangleq> Committed)"
      using firstTx_def by auto

    show "\<And>c. i_callOriginI S c \<triangleq> i \<Longrightarrow> c \<in> vis"
      apply (auto simp add: i_callOriginI_h_def split: option.splits)
      using S_wf state_wellFormed_ls_visibleCalls_callOrigin vis_def by blast

    show "generatedLocalPrivate \<subseteq> generatedLocal"
      by (simp add: generatedLocalPrivate1)

    show "\<And>x. x \<in> generatedLocalPrivate \<Longrightarrow>
         uid_is_private i S x"
      by (simp add: generatedLocalPrivate2)


  qed
qed


lemma execution_s_check_sound2:
  assumes a1: "localState S i \<triangleq> ls"
    and a2': "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes.
\<lbrakk>
s_invocOp i = invocOp S i;
s_invocRes i = None;
\<And>tx. s_txOrigin tx \<noteq> Some i
\<rbrakk> \<Longrightarrow>
  execution_s_check 
  progr 
  i
  s_calls
  s_happensBefore
  s_callOrigin
  s_txOrigin
  s_knownIds
  s_invocOp
  s_invocRes
  {}
  {}
  {}
  []
  None
  True
  ls"
  shows "execution_s_correct S i"
  using a1
proof (rule execution_s_check_sound)

  have a2: "S \<in> initialStates progr i"
    using a2' by (simp add: initialStates'_same) 

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

  show currentTx: "currentTx S i = None"
    using a2 initialState_noTxns2 by blast


  show "execution_s_check progr i (calls S) (happensBefore S) (callOrigin S) (txOrigin S) (knownIds S) (invocOp S)
     (invocRes S) {} {} {} [] (currentTx S i) True ls "
    unfolding currentTx
  proof (rule c)
    show "invocOp S i = invocOp S i" by simp
    show "invocRes S i = None"
      by (simp add: a1 local.wf state_wellFormed_no_result_when_running)
    show "\<And>tx. txOrigin S tx \<noteq> Some i"
      using a2 by (auto simp add: initialStates_def)

  qed

  show "\<And>tx'. currentTx S i \<noteq> Some tx' \<longrightarrow> txStatus S tx' \<noteq> Some Uncommitted"
    using a2 initialState_noTxns1 by blast

  show "True = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> txOrigin S tx \<triangleq> i \<and> txStatus S tx \<triangleq> Committed)"
    by (meson \<open>visibleCalls S i \<triangleq> {}\<close> empty_iff local.wf state_wellFormed_ls_visibleCalls_callOrigin)


qed simp+


lemma execution_s_check_sound3:
  assumes a1: "localState S i \<triangleq> ls"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocOp S i \<triangleq> op"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes.
\<lbrakk>
\<And>tx. s_txOrigin tx \<noteq> Some i
\<rbrakk> \<Longrightarrow>
  execution_s_check 
  progr 
  i
  s_calls
  s_happensBefore
  s_callOrigin
  s_txOrigin
  s_knownIds
  (s_invocOp(i\<mapsto>op))
  (s_invocRes(i:=None))
  {}
  {}
  {}
  []
  None
  True
  ls"
  shows "execution_s_correct S i"
  by (smt a1 a2 a3 a4 c execution_s_check_sound2 fun_upd_triv)

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

lemma no_ainvoc:
  assumes "\<forall>p t. (AInvoc p, t) \<notin> set trace"
    and "trace = (action, Inv) # trace'"
and "\<lbrakk>\<forall>p t. (AInvoc p, t) \<notin> set trace; \<And>proc. action \<noteq> AInvoc proc\<rbrakk> \<Longrightarrow> P"
shows "P"
  using assms by auto

method show_proof_rule = 
  (subst  execution_s_check_def, intro allI impI, erule case_trace_not_empty3, erule(1) no_ainvoc, fuzzy_goal_cases Step)

inductive_cases step_s_NewId: "S ~~ (i, ANewId uidv, Inv) \<leadsto>\<^sub>S S'"

lemma execution_s_check_newId:
  assumes "infinite (Collect P)"
    and "program_wellFormed progr"
    and cont: "\<And>v. \<lbrakk>P v; 
to_nat v \<notin> s_knownIds;
to_nat v \<notin> generatedLocal;
uniqueIds v = {to_nat v};
uid_is_private' i s_calls s_invocOp s_invocRes s_knownIds (to_nat v)
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_txOrigin 
  s_knownIds 
  s_invocOp
  s_invocRes
  (generatedLocal \<union> {to_nat v})
  (generatedLocalPrivate \<union> {to_nat v})
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
  s_txOrigin 
  s_knownIds 
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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


      have h1: "new_unique_not_in_calls s_calls (to_nat uidv)"
        using Step.calls_eq Step.prog_eq Step.state_wellFormed assms(2) c5 new_unique_not_in_calls_def wf_onlyGeneratedIdsInCalls by blast


      have h2: "new_unique_not_in_calls_result s_calls (to_nat uidv)"
        using Step.calls_eq Step.prog_eq Step.state_wellFormed assms(2) c5 new_unique_not_in_calls_result_def wf_onlyGeneratedIdsInCallResults by blast

      have h3: "new_unique_not_in_invocOp s_invocOp (to_nat uidv)"
        using Step.invocOp_eq Step.prog_eq Step.state_wellFormed assms(2) c5 new_unique_not_in_invocOp_def wf_onlyGeneratedIdsInInvocationOps by blast

      have h4: "new_unique_not_in_invocRes s_invocRes (to_nat uidv)"
        using Step.invocRes_eq Step.prog_eq Step.state_wellFormed assms(2) c5 new_unique_not_in_invocRes_def wf_onlyGeneratedIdsInInvocationRes by blast


      have h5: "new_unique_not_in_other_invocations i S'a (to_nat uidv)"
        unfolding new_unique_not_in_other_invocations_def
      proof (intro allI impI)
        fix i'
        assume a0: "i' \<noteq> i"

        have "program_wellFormed (prog S1)"
          by (simp add: Step.prog_eq assms(2))


        obtain uids 
          where "uids\<subseteq>dom (generatedIds S1)" and "invocation_cannot_guess_ids uids i' S1"
          using wf_knownIds_subset_generatedIds_h(1)[OF `state_wellFormed S1` `program_wellFormed (prog S1)`]
          by auto


        from `uids\<subseteq>dom (generatedIds S1)`
          and `generatedIds S1 (to_nat uidv) = None`
        have " to_nat uidv \<notin> uids"
          by auto


        show "\<exists>uids. to_nat uidv \<notin> uids \<and> invocation_cannot_guess_ids uids i' S'a"
          using Step.step_s \<open>invocation_cannot_guess_ids uids i' S1\<close> \<open>to_nat uidv \<notin> uids\<close> a0 c2 show_invocation_cannot_guess_ids_step_other step_s_to_step  by fastforce
      qed



      have h6: "to_nat uidv \<notin> s_knownIds"
        using Step.knownIds_eq Step.prog_eq Step.state_wellFormed assms(2) c5 wf_onlyGeneratedIdsInKnownIds by blast


      show "execution_s_check
            progr 
            i
            s_calls 
            s_happensBefore 
            s_callOrigin 
            s_txOrigin 
            s_knownIds 
            s_invocOp
            s_invocRes
            (generatedLocal \<union> {to_nat uidv})
            (generatedLocalPrivate \<union> {to_nat uidv})
            vis
            localCalls
            tx
            firstTx
            (cont uidv)"
      proof (rule cont)
        show "P uidv"
          by (simp add: c7)

        
        show "to_nat uidv \<notin> s_knownIds"
          using h6 by auto

        show "to_nat uidv \<notin> generatedLocal"
          by (simp add: Step.generatedLocal_def c5)

        show "uniqueIds uidv = {to_nat uidv}"
          by (simp add: c6)

        show "uid_is_private' i s_calls s_invocOp s_invocRes s_knownIds (to_nat uidv)"
          by (simp add: h1 h2 h3 h4 h6 uid_is_private'_def)


      qed


      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        using Step.case_option by  (auto simp add: S'a_def  split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step by (auto simp add:S'a_def )

      show "generatedLocal \<union> {to_nat uidv} = {x. generatedIds S'a x \<triangleq> i}"
        by (auto simp add: S'a_def Step)

      show "generatedLocalPrivate \<union> {to_nat uidv} \<subseteq> generatedLocal \<union> {to_nat uidv}"
        apply (auto simp add: S'a_def Step)
        using Step.Ball uid_is_private_def by blast

      

      show "uid_is_private i S'a v" if "v \<in> generatedLocalPrivate \<union> {to_nat uidv}" for v
        using that proof auto

        show  "uid_is_private i S'a (to_nat uidv)"
          using S'a_def h5 by (auto simp add: uid_is_private_def S'a_def Step h1 h2 h3 h4 h5 h6)

          

        show "uid_is_private i S'a v" if "v \<in> generatedLocalPrivate"
          unfolding uid_is_private_def
        proof (intro conjI)

          have pre: "uid_is_private i S1 v" 
            by (simp add: Step.Ball that)

          show "new_unique_not_in_invocOp (invocOp S'a) v"
            using pre by (auto simp add: uid_is_private_def S'a_def)


          show "new_unique_not_in_calls (calls S'a) v"
            using pre by (auto simp add: uid_is_private_def S'a_def)
          show "new_unique_not_in_calls_result (calls S'a) v"
            using pre by (auto simp add: uid_is_private_def S'a_def)
          show "new_unique_not_in_invocRes (invocRes S'a) v"
            using pre by (auto simp add: uid_is_private_def S'a_def)
          show "v \<notin> knownIds S'a"
            using pre by (auto simp add: uid_is_private_def S'a_def)
          show "generatedIds S'a v \<triangleq> i"
            using pre by (auto simp add: uid_is_private_def S'a_def)
          show "new_unique_not_in_other_invocations i S'a v"
            using pre proof (auto simp add: uid_is_private_def )

            show "new_unique_not_in_other_invocations i S'a v"
              if c0: "new_unique_not_in_invocOp (invocOp S1) v"
                and c1: "new_unique_not_in_calls (calls S1) v"
                and c2: "new_unique_not_in_calls_result (calls S1) v"
                and c3: "new_unique_not_in_invocRes (invocRes S1) v"
                and c4: "v \<notin> knownIds S1"
                and c5: "generatedIds S1 v \<triangleq> i"
                and c6: "new_unique_not_in_other_invocations i S1 v"
             
            using c6 proof (auto simp add: new_unique_not_in_other_invocations_def)
            fix i'
            assume a0: "\<forall>i'. i' \<noteq> i \<longrightarrow> (\<exists>uids. v \<notin> uids \<and> invocation_cannot_guess_ids uids i' S1)"
              and a1: "i' \<noteq> i"

            obtain uids where "v \<notin> uids" and "invocation_cannot_guess_ids uids i' S1"
              using a0 a1 by auto

            have "i \<noteq> i'" using a1 by simp

            have "invocation_cannot_guess_ids uids i' S'a"
              using `invocation_cannot_guess_ids uids i' S1` `S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
              by (rule show_invocation_cannot_guess_ids_step_s_other)
                (auto simp add: `action = ANewId uidv` `i \<noteq> i'`)


            thus "\<exists>uids. v \<notin> uids \<and> invocation_cannot_guess_ids uids i' S'a"
              using \<open>v \<notin> uids\<close> by blast

          qed

        qed
      qed
    qed
        

    qed (simp add: S'a_def Step; fail)+
  qed
qed





lemma execution_s_check_beginAtomic:
  assumes "program_wellFormed progr"
    and cont: "\<And>tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis'
 s_invocOp' s_invocRes' .
\<lbrakk>invariant progr
     \<lparr>calls = s_calls', 
      happensBefore = s_happensBefore',
      callOrigin = s_callOrigin',
      txOrigin = s_txOrigin', 
      knownIds = s_knownIds',
      invocOp = (s_invocOp'(i := s_invocOp i)), 
      invocRes = s_invocRes'(i := None)\<rparr>;
s_txOrigin' tx = None;
\<And>i op. s_invocOp i \<triangleq> op \<Longrightarrow> s_invocOp' i \<triangleq> op;
\<And>c. s_callOrigin' c \<noteq> Some tx;
vis \<subseteq> vis';
vis' \<subseteq> dom s_calls';
firstTx \<Longrightarrow> (\<And>c tx. s_callOrigin' c \<triangleq> tx \<Longrightarrow> s_txOrigin' tx \<noteq> Some i);
\<comment> \<open>consistency: \<close>
causallyConsistent s_happensBefore' vis';
transactionConsistent_atomic s_callOrigin' vis';
\<forall>v\<in>generatedLocalPrivate. uid_is_private' i s_calls' s_invocOp' s_invocRes' s_knownIds' v;
\<comment> \<open>generic wellFormed and growth predicates (this is more like a backup, the important facts should be above) : \<close>
\<exists>some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus.
state_wellFormed \<lparr>
  calls = s_calls',
  happensBefore = s_happensBefore',
  callOrigin = s_callOrigin',
  txOrigin = s_txOrigin',
  knownIds = s_knownIds',
  invocOp = s_invocOp',
  invocRes = s_invocRes',
  prog = progr,
  txStatus = some_txStatus,
  generatedIds =  some_generatedIds,
  localState = some_localState,
  currentProc = some_currentProc,
  visibleCalls =  some_visibleCalls,
  currentTx = some_currentTx\<rparr>;
 \<exists>some_generatedIds1 some_currentTx1 some_localState1 some_currentProc1 some_visibleCalls1 some_txStatus1
  some_generatedIds2 some_currentTx2 some_localState2 some_currentProc2 some_visibleCalls2 some_txStatus2.
state_monotonicGrowth i \<lparr>
  calls = s_calls,
  happensBefore = s_happensBefore,
  callOrigin = s_callOrigin,
  txOrigin = s_txOrigin,
  knownIds = s_knownIds,
  invocOp = s_invocOp,
  invocRes = s_invocRes,
  prog = progr,
  txStatus = some_txStatus1,
  generatedIds =  some_generatedIds1,
  localState = some_localState1,
  currentProc = some_currentProc1,
  visibleCalls =  some_visibleCalls1,
  currentTx = some_currentTx1\<rparr> 
\<lparr>
  calls = s_calls',
  happensBefore = s_happensBefore',
  callOrigin = s_callOrigin',
  txOrigin = s_txOrigin',
  knownIds = s_knownIds',
  invocOp = s_invocOp',
  invocRes = s_invocRes',
  prog = progr,
  txStatus = some_txStatus2,
  generatedIds =  some_generatedIds2,
  localState = some_localState2,
  currentProc = some_currentProc2,
  visibleCalls =  some_visibleCalls2,
  currentTx = some_currentTx2\<rparr>
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls' 
  s_happensBefore' 
  s_callOrigin' 
  (s_txOrigin'(tx \<mapsto> i))
  s_knownIds' 
  (s_invocOp'(i := s_invocOp i))
  (s_invocRes'(i := None))
  generatedLocal
  generatedLocalPrivate
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
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
  obtain t  S' vis' vis''
    where c0: "localState S1 i \<triangleq> (beginAtomic \<bind> cont)"
      and c1: "currentProc S1 i \<triangleq> toImpl"
      and c2: "action = ABeginAtomic t vis''"
      and c3: "Inv"
      and c4: "currentTx S1 i = None"
      and c5: "txStatus S1 t = None"
      and c6: "prog S' = prog S1"
      and growth: "state_monotonicGrowth i S1 S'"
      and c8: "\<forall>x. txOrigin S1 x \<triangleq> i = txOrigin S' x \<triangleq> i"
      and inv: "invariant (prog S1) (invContext S')"
      and c10: "\<forall>x. txStatus S' x \<noteq> Some Uncommitted"
      and wf_S': "state_wellFormed S'"
      and c12: "state_wellFormed (S'\<lparr>txStatus := txStatus S'(t \<mapsto> Uncommitted), txOrigin := txOrigin S'(t \<mapsto> i), currentTx := currentTx S'(i \<mapsto> t), localState := localState S'(i \<mapsto> cont ()), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>)"
      and c13: "localState S' i \<triangleq> (beginAtomic \<bind> cont)"
      and c14: "currentProc S' i \<triangleq> toImpl"
      and c15: "currentTx S' i = None"
      and c16: "visibleCalls S1 i \<triangleq> vis'"
      and c17: "visibleCalls S' i \<triangleq> vis'"
      and c18: "chooseSnapshot vis'' vis' S'"
      and c19: "consistentSnapshot S' vis''"
      and c20: "txStatus S' t = None"
      and c21: "\<forall>x. callOrigin S' x \<noteq> Some t"
      and c22: "txOrigin S' t = None"
      and S'a_def: "S'a = S' \<lparr>txStatus := txStatus S'(t \<mapsto> Uncommitted), txOrigin := txOrigin S'(t \<mapsto> i), currentTx := currentTx S'(i \<mapsto> t), localState := localState S'(i \<mapsto> cont ()), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>"
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

      show "currentTx S'a i \<triangleq> t"
        by (simp add: S'a_def)

      show " \<And>tx'. Some t \<noteq> Some tx' \<Longrightarrow> txStatus S'a tx' \<noteq> Some Uncommitted"
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

      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a) (txOrigin S'a) (knownIds S'a)
     (invocOp S'a) (invocRes S'a) generatedLocal generatedLocalPrivate  vis'' [] (Some t) firstTx (cont ())"
      proof (fuzzy_rule cont)

        show "progr = prog S'a"
          by (simp add: S'a_def `prog S1 = progr` c6)

        show "txOrigin S'(t \<mapsto> i) = txOrigin S'a"
          by (simp add: S'a_def)

        show "txOrigin S' t = None"
          by (simp add: c22)


        show " invariant progr
     \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
        txOrigin = txOrigin S', knownIds = knownIds S'a, invocOp = (invocOp S'a)(i := s_invocOp i),
        invocRes = (invocRes S'a)(i := None)\<rparr>"
        proof (fuzzy_rule inv)
          show "prog S1 = progr"
            by (simp add: Step)

          have cCalls: "committedCalls S' = dom (calls S')"
            by (simp add: c10 wf_S' committedCalls_allCommitted)

          have allTransactionsCommitted: "committedTransactions S' = dom (txOrigin S')"
            apply (auto simp add: dom_def)
             apply (metis wf_S' domD domIff option.simps(3) wf_transaction_status_iff_origin)
            by (metis c10 not_None_eq not_uncommitted_cases wf_S' wf_transaction_status_iff_origin)



          show "invContext S' =
           \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
            txOrigin = txOrigin S', knownIds = knownIds S'a, invocOp = (invocOp S'a)(i := s_invocOp i),
           invocRes = (invocRes S'a)(i := None)\<rparr>"
          proof (auto simp add: invContextH_def S'a_def cCalls allTransactionsCommitted)
            show "\<And>a b. (a, b) \<in> happensBefore S' |r dom (calls S') \<Longrightarrow> (a, b) \<in> happensBefore S'"
              by (simp add: restrict_relation_def)
            show "\<And>a b. (a, b) \<in> happensBefore S' \<Longrightarrow> (a, b) \<in> happensBefore S' |r dom (calls S')"
              by (simp add: wf_S' happensBefore_in_calls_left happensBefore_in_calls_right restrict_relation_def)
            show " callOrigin S' |` dom (calls S') = callOrigin S'"
              by (metis wf_S' restrict_map_noop2 wellFormed_callOrigin_dom)
            show "invocOp S' = (invocOp S')(i := s_invocOp i)"
              using Step.invocOp_eq growth state_monotonicGrowth_invocOp_i  by fastforce
            show "invocRes S' = (invocRes S')(i := None)"
              by (simp add: c13 fun_upd_idem wf_S' wf_localState_noReturn)
          qed
        qed

        show "\<And>i op. s_invocOp i \<triangleq> op \<Longrightarrow> invocOp S'a i \<triangleq> op"
          apply(simp add: S'a_def)
          using Step.invocOp_eq growth state_monotonicGrowth_invocOp by blast

        show "\<And>c. callOrigin S'a c \<noteq> Some t"
          using \<open>case Some t of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S'a c \<triangleq> tx'}\<close> by auto
        
        from `chooseSnapshot vis'' vis' S'`
        have "vis' \<subseteq> vis''"
          by (auto simp add: chooseSnapshot_def)

        have "vis \<subseteq> vis'"
          using `visibleCalls S1 i \<triangleq> (vis \<union> set [])` c16 by auto

        show "vis \<subseteq> vis''"
          using \<open>vis \<subseteq> vis'\<close> \<open>vis' \<subseteq> vis''\<close> by auto

        
        show "vis'' \<subseteq> dom (calls S'a)"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def)

        show "causallyConsistent (happensBefore S'a) vis''"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def)

        show "transactionConsistent_atomic (callOrigin S'a) vis''"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def transactionConsistent_def)

        from `state_wellFormed S'`
        show "\<exists>some_generatedIds some_currentTx some_localState some_currentProc some_visibleCalls some_txStatus.
       state_wellFormed
        \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
           txOrigin = txOrigin S', knownIds = knownIds S'a, invocOp = invocOp S'a,
           invocRes = invocRes S'a, prog = progr, txStatus = some_txStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTx = some_currentTx\<rparr>"
          apply (simp add: S'a_def `prog S1 = progr`[symmetric])
          by (metis (full_types) c6 old.unit.exhaust state.surjective)

        have smg: "state_monotonicGrowth i
         \<lparr>calls = calls S1, happensBefore = happensBefore S1, callOrigin = callOrigin S1,
            txOrigin = txOrigin S1, knownIds = knownIds S1, invocOp = invocOp S1,
            invocRes = invocRes S1, prog = prog S1, txStatus = txStatus S1,
            generatedIds = generatedIds S1, localState = localState S1, currentProc = currentProc S1,
            visibleCalls = visibleCalls S1, currentTx = currentTx S1\<rparr>
         \<lparr>calls = calls S', happensBefore = happensBefore S', callOrigin = callOrigin S',
            txOrigin = txOrigin S', knownIds = knownIds S', invocOp = invocOp S',
            invocRes = invocRes S', prog = prog S', txStatus = txStatus S',
            generatedIds = generatedIds S', localState = localState S', currentProc = currentProc S',
            visibleCalls = visibleCalls S', currentTx = currentTx S'\<rparr>"
          by (fuzzy_rule `state_monotonicGrowth i S1 S'`, auto)



        show " \<exists>some_generatedIds1 some_currentTx1 some_localState1 some_currentProc1 some_visibleCalls1
         some_txStatus1 some_generatedIds2 some_currentTx2 some_localState2 some_currentProc2
         some_visibleCalls2 some_txStatus2.
         state_monotonicGrowth i
          \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
             txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp,
             invocRes = s_invocRes, prog = progr, txStatus = some_txStatus1,
             generatedIds = some_generatedIds1, localState = some_localState1, currentProc = some_currentProc1,
             visibleCalls = some_visibleCalls1, currentTx = some_currentTx1\<rparr>
          \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
             txOrigin = txOrigin S', knownIds = knownIds S'a, invocOp = invocOp S'a,
             invocRes = invocRes S'a, prog = progr, txStatus = some_txStatus2,
             generatedIds = some_generatedIds2, localState = some_localState2, currentProc = some_currentProc2,
             visibleCalls = some_visibleCalls2, currentTx = some_currentTx2\<rparr>"
          apply (simp add: S'a_def)
          apply (rule exI)+
          apply (fuzzy_rule smg)
          by (auto simp add: Step c6)


        

        show "\<forall>v\<in>generatedLocalPrivate.
         uid_is_private' i (calls S'a) (invocOp S'a) (invocRes S'a) (knownIds S'a) v"
        proof (auto simp add: S'a_def )
          fix v::nat
          assume "v\<in>generatedLocalPrivate"
          with `\<forall>v\<in>generatedLocalPrivate.
                uid_is_private i S1 v`
          have "uid_is_private i S1 v"
            by auto
          hence "uid_is_private i S' v"
            using  Step.prog_eq assms(1) growth growth_still_hidden  by  blast

          thus "uid_is_private' i (calls S') (invocOp S') (invocRes S') (knownIds S') v"
            by (meson uid_is_private'_implies)
        qed

        show "(invocOp S'a)(i := s_invocOp i) = invocOp S'a"
          apply (auto simp add: S'a_def)
          apply (rule fun_upd_idem)
          using Step.invocOp_eq growth state_monotonicGrowth_invocOp_i by  blast

        show "(invocRes S'a)(i := None) = invocRes S'a"
          apply (auto simp add: S'a_def)
          apply (rule fun_upd_idem)
          by (simp add: c13 state_wellFormed_no_result_when_running wf_S')


        show "txOrigin S' tx \<noteq> Some i"
          if c0: "firstTx"
            and c1: "callOrigin S'a c \<triangleq> tx"
          for  c tx
          using `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> txOrigin S1 tx \<triangleq> i \<and> txStatus S1 tx \<triangleq> Committed)`
            c0 c1
          apply (auto simp add: S'a_def )
          by (smt Step.All_implies_not_txStatus_eq Step.state_wellFormed c16 c17 c8 domD domIff growth state_monotonicGrowth_callOrigin state_wellFormed_ls_visibleCalls_callOrigin wellFormed_callOrigin_dom3 wellFormed_currentTx_unique_h(2) wellFormed_state_transaction_consistent(1) wellFormed_visibleCallsSubsetCalls2 wf_S')




      qed
      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> txOrigin S1 tx \<triangleq> i \<and> txStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> txOrigin S'a tx \<triangleq> i \<and> txStatus S'a tx \<triangleq> Committed)"
        apply (auto simp add: S'a_def)
        apply (smt Step.state_wellFormed c16 c17 c4 c8 domExists_simp domIff growth state_monotonicGrowth_callOrigin state_wellFormed_ls_visibleCalls_callOrigin transactionConsistent_Committed wellFormed_callOrigin_dom3 wellFormed_visibleCallsSubsetCalls2 wf_S' wf_transactionConsistent_noTx)
        by (metis (mono_tags, lifting) Step.state_wellFormed c5 growth state_monotonicGrowth_callOrigin state_monotonicGrowth_txOrigin state_monotonicGrowth_txStatus2 wf_callOrigin_implies_txStatus_defined)

      show "\<And>c. i_callOriginI S'a c \<triangleq> i \<Longrightarrow> c \<in> vis''"
        apply (simp add: S'a_def i_callOriginI_h_def c21 split: option.splits if_splits)
        using c17 c18 chooseSnapshot_def state_wellFormed_ls_visibleCalls_callOrigin wf_S' by fastforce

      from `generatedLocal = {x. generatedIds S1 x \<triangleq> i}`
      show "generatedLocal = {x. generatedIds S'a x \<triangleq> i}"
        using growth state_monotonicGrowth_generatedIds_same1  by (simp add: S'a_def, fastforce)

      show "generatedLocalPrivate \<subseteq> generatedLocal"
        using Step.less_eq by blast

      show "uid_is_private i S'a x"
        if c0: "x \<in> generatedLocalPrivate"
        for  x
      proof -
        from c0 have "uid_is_private i S1 x"
          using Step by blast

        hence "uid_is_private i S' x"
          using Step.prog_eq assms(1) growth growth_still_hidden  by  blast

        show "uid_is_private i S'a x"
          unfolding uid_is_private_def
        proof (intro conjI)

          show "new_unique_not_in_other_invocations i S'a x"
            unfolding new_unique_not_in_other_invocations_def
          proof (intro allI impI)
            fix i' 
            assume "i' \<noteq> i"

            obtain uids where "x \<notin> uids" and "invocation_cannot_guess_ids uids i' S'"
              by (meson \<open>i' \<noteq> i\<close> \<open>uid_is_private i S' x\<close> new_unique_not_in_other_invocations_def uid_is_private_def)

            from  ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
            have " S1 ~~ (i, ABeginAtomic t vis'', Inv) \<leadsto>\<^sub>S S'a"
              by (simp add:  `action = ABeginAtomic t vis''`)

            thm step_s_beginAtomic_to_steps
            from `state_monotonicGrowth i S1 S'`
            obtain tr
              where "S1 ~~ tr \<leadsto>* S'"
                and "\<forall>(i', a)\<in>set tr. i' \<noteq> i"
                and "\<forall>i. (i, ACrash) \<notin> set tr" 
              by (auto simp add: state_monotonicGrowth_def)


            have " S' ~~ (i, ABeginAtomic t vis'') \<leadsto> S'a"
              using c13 c14 c15 c17 c18 c20 by (auto simp add: step.simps S'a_def state_ext)




            have "invocation_cannot_guess_ids uids i' S'a"
              using \<open>S' ~~ (i, ABeginAtomic t vis'') \<leadsto> S'a\<close> \<open>i' \<noteq> i\<close> \<open>invocation_cannot_guess_ids uids i' S'\<close> show_invocation_cannot_guess_ids_step_other by blast

            show "\<exists>uids. x \<notin> uids \<and> invocation_cannot_guess_ids uids i' S'a"
              using \<open>invocation_cannot_guess_ids uids i' S'a\<close> \<open>x \<notin> uids\<close> by auto

          qed

        qed (insert `uid_is_private i S' x`, simp add: S'a_def uid_is_private_def new_unique_not_in_other_invocations_def; fail)+


      qed

    qed (simp add: S'a_def Step; fail)+
  qed
qed



lemma execution_s_check_endAtomic:
  assumes "program_wellFormed progr"
    and "s_txOrigin tx = None"
    and tx_nonempty: "localCalls \<noteq> []"
and inv_cont: "
\<lbrakk>
distinct localCalls;
\<And>c. c\<in>set localCalls \<Longrightarrow> s_callOrigin c = None;
\<And>c. c\<in>set localCalls \<Longrightarrow> c \<notin> vis;
\<And>c c'. c\<in>set localCalls \<Longrightarrow> (c,c') \<notin> s_happensBefore;
\<And>c c'. c\<in>set localCalls \<Longrightarrow> (c',c) \<notin> s_happensBefore;
invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_txOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_txOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore })
\<rbrakk>
 \<Longrightarrow> invariant progr
     \<lparr>calls = s_calls, 
      happensBefore = updateHb s_happensBefore vis localCalls,
      callOrigin = map_update_all s_callOrigin localCalls tx,
      txOrigin = s_txOrigin(tx \<mapsto> i), 
      knownIds = s_knownIds,
      invocOp = s_invocOp, 
      invocRes = s_invocRes\<rparr>
\<and> execution_s_check
  progr 
  i
  s_calls 
  (updateHb s_happensBefore vis localCalls) 
  (map_update_all s_callOrigin localCalls tx) 
  (s_txOrigin(tx \<mapsto> i))
  s_knownIds 
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
  (vis \<union> set localCalls)
  []
  None
  False
  (cont ())
"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  (s_txOrigin(tx \<mapsto> i)) 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
    `currentTx S1 i \<triangleq> tx`
  have action_def: "action = AEndAtomic"
    and S'a_def: "S'a = S1
     \<lparr>localState := localState S1(i \<mapsto> cont ()), currentTx := (currentTx S1)(i := None),
        txStatus := txStatus S1(tx \<mapsto> Committed)\<rparr>"
    and S'a_wf: "state_wellFormed S'a"
    and Inv_def: "Inv \<longleftrightarrow> 
     invariant (prog S1)
      (invContextH (callOrigin S1) (txOrigin S1) (txStatus S1(tx \<mapsto> Committed)) (happensBefore S1)
        (calls S1) (knownIds S1) (invocOp S1) (invocRes S1))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    have allCommitted1: 
      "txStatus S1 tx' \<triangleq> Committed" if "tx' \<noteq> tx" and "callOrigin S1 c \<triangleq> tx'" for c tx'
      using that
      by (metis (no_types, lifting) Step.All_implies_not_txStatus_eq Step.state_wellFormed not_uncommitted_cases option.exhaust option.sel wf_no_txStatus_origin_for_nothing)

    have tx_uncommitted: "txStatus S1 tx \<triangleq> Uncommitted"
      using Step.currentTx_eq Step.state_wellFormed not_uncommitted_cases wellFormed_currentTx_unique_h(2)  by  blast

    have allCommitted2: "txStatus S1 t \<triangleq> Committed \<longleftrightarrow> t \<noteq> tx \<and> txStatus S1 t \<noteq> None" for t
      apply (cases "txStatus S1 t", auto simp add: tx_uncommitted)
      using Step.All_implies_not_txStatus_eq txStatus.exhaust  by  force



    have committedCallsH_simp: "committedCallsH (callOrigin S1) (txStatus S1(tx \<mapsto> Committed))
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
        using Step.happensBefore_eq Step.state_wellFormed h1 happensBefore_in_calls_left happensBefore_in_calls_right  by  fastforce+
      

      have h3: "map_update_all s_callOrigin localCalls tx = callOrigin S1 |` dom (calls S1)"
        apply (simp add: Step)
        apply (subst restrict_map_noop)
         apply auto
        using  Step.callOrigin_eq Step.state_wellFormed h1 wellFormed_callOrigin_dom  by  fastforce+



      have h4: "s_txOrigin(tx\<mapsto>i) =
        txOrigin S1 |` {t. t \<noteq> tx \<longrightarrow> txStatus S1 t \<triangleq> Committed}"
        apply (simp add: Step )
        apply (subst restrict_map_noop)
         apply (auto simp add: `s_txOrigin tx = None`  allCommitted2 wf_transaction_status_iff_origin)
        by (metis Step.state_wellFormed Step.txOrigin_eq fun_upd_apply option.distinct(1) option.exhaust wf_transaction_status_iff_origin)

      have "localCalls \<noteq> []"
        by (simp add: tx_nonempty)
      have "distinct localCalls"
        by (simp add: Step.distinct)
      have  co_tx_none: "\<forall>c\<in>set localCalls. s_callOrigin c = None"
        using Step.inf_eq2 by blast
      have to_tx_none: " s_txOrigin tx = None"
        by (simp add: assms(2))
      have co_not_tx: "\<And>c. s_callOrigin c \<noteq> Some tx"
        using Step.callOrigin_eq Step.case_option co_tx_none map_update_all_Some_same by  fastforce

      have hb_wf_l:"\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c \<triangleq> t"
        using FieldI1 FieldI2 Step.state_wellFormed (* TODO Step(20) *) (* TODO Step(3) *) (* TODO Step(4) *) disjoint_iff_not_equal domExists_simp domIff map_update_all_get updateHb_simp2 wellFormed_happensBefore_calls_l wf_callOrigin_and_calls
        by (smt Step.callOrigin_eq Step.happensBefore_eq Step.inf_eq3 Step.state_wellFormed)
      have hb_wf_r: "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c' \<triangleq> t"
        by (metis FieldI2 Step.callOrigin_eq Step.happensBefore_eq Step.inf_eq3 Step.state_wellFormed disjoint_iff_not_equal map_update_all_get option.exhaust updateHb_simp2 wellFormed_happensBefore_calls_r wf_callOrigin_and_calls)

      have  invocation_hb_simp:
        "invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_txOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_txOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore })"
      proof (rule if_cases)
        assume firstTx


        show "invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i)))
           (updateHb s_happensBefore vis localCalls) =
          invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore \<union>
          {i' |  i' c'.
              c' \<in> vis \<and>
              i_callOriginI_h s_callOrigin s_txOrigin c' \<triangleq> i' \<and>
              (\<forall>c''. i_callOriginI_h s_callOrigin s_txOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis)} \<times>
          {i}"
          using `localCalls \<noteq> []` 
            `distinct localCalls` co_tx_none to_tx_none co_not_tx hb_wf_l hb_wf_r
        proof (fuzzy_rule(noabs) invocation_happensBeforeH_one_transaction_simp2)

          show "s_txOrigin t \<noteq> Some i" if "s_callOrigin c \<triangleq> t" for c t
          proof -
            from `s_callOrigin c \<triangleq> t`
            have "c \<notin> set localCalls"
              using co_tx_none by fastforce
            then have "c \<notin> set localCalls \<and> s_callOrigin c \<triangleq> t"
              using that by blast
            then have f1: "t \<noteq> tx \<longrightarrow> callOrigin S1 c \<triangleq> t"
              by (simp add: Step.callOrigin_eq map_update_all_get)
            have "s_callOrigin c \<noteq> Some tx"
              using co_not_tx by blast
            then have "t \<noteq> tx"
              using that by blast
            then have "s_txOrigin(t \<mapsto> i) \<noteq> s_txOrigin"
              using f1
              by (metis Step.firstTx_def Step.txOrigin_eq \<open>firstTx\<close> allCommitted1 fun_upd_idem_iff fun_upd_other)
            then show "s_txOrigin t \<noteq> Some i"
              by (metis (no_types) fun_upd_triv)
          qed

        qed auto
      next
        assume "\<not> firstTx"
        from this obtain old_c old_t 
          where "s_callOrigin old_c \<triangleq> old_t"
            and "s_txOrigin old_t \<triangleq> i"
            and "txStatus S1 old_t \<triangleq> Committed"
          using Step.callOrigin_eq Step.firstTx_def Step.txOrigin_eq fun_upd_apply option.sel allCommitted2 map_update_all_Some_other by  fastforce


        show " invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i)))
     (updateHb s_happensBefore vis localCalls) =
    invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore -
    {i} \<times> {i'. (i, i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore}"
          using tx_nonempty `s_txOrigin old_t \<triangleq> i` co_tx_none `s_callOrigin old_c \<triangleq> old_t`
                hb_wf_l co_not_tx
        proof (fuzzy_rule invocation_happensBeforeH_more_transactions_simp2)

          show "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> (c, c') \<in> s_happensBefore"
            by simp

          show "Field s_happensBefore \<inter> set localCalls = {}"
            by (simp add: Step.inf_eq3)

          show "\<And>c. i_callOriginI_h s_callOrigin s_txOrigin c \<triangleq> i \<Longrightarrow> c \<in> vis"
            by (simp add: Step.All_implies_member i_callOriginI_h_update_to2)

          show "\<And>c c'. \<lbrakk>c' \<in> vis; (c, c') \<in> s_happensBefore\<rbrakk> \<Longrightarrow> c \<in> vis"
          proof -
            fix c :: callId and c' :: callId
            assume a1: "c' \<in> vis"
            assume a2: "(c, c') \<in> s_happensBefore"
            have f3: "\<forall>c. c \<notin> Field s_happensBefore \<or> (\<forall>ca. ca \<notin> set localCalls \<or> c \<noteq> ca)"
              using Step.inf_eq3 by  auto
            have f4: "c' \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI2)
            have "c \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI1)
            then show "c \<in> vis"
              using f4 f3 a2 a1 
              by (metis Step.happensBefore_eq Step.state_wellFormed Step.visibleCalls_eq Un_iff updateHb_simp2 wf_vis_downwards_closed2)
          qed



        qed
      qed



      

      have inv_cont2: "invariant progr
       \<lparr>calls = s_calls, happensBefore = updateHb s_happensBefore vis localCalls,
          callOrigin = map_update_all s_callOrigin localCalls tx, txOrigin = s_txOrigin(tx \<mapsto> i),
          knownIds = s_knownIds, invocOp = s_invocOp, invocRes = s_invocRes\<rparr> \<and>
      execution_s_check progr i s_calls (updateHb s_happensBefore vis localCalls)
       (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i)) s_knownIds s_invocOp s_invocRes
     generatedLocal generatedLocalPrivate (vis \<union> set localCalls) [] None False (cont ())"
        using  `distinct localCalls`
      proof (rule inv_cont)
        show h5: "\<And>c. c \<in> set localCalls \<Longrightarrow> s_callOrigin c = None"
          using co_tx_none by auto
        show h6: "\<And>c c'. c \<in> set localCalls \<Longrightarrow> (c, c') \<notin> s_happensBefore"
          using co_tx_none hb_wf_l by fastforce
        show h7: "\<And>c c'. c \<in> set localCalls \<Longrightarrow> (c', c) \<notin> s_happensBefore"
          using co_tx_none hb_wf_r by fastforce
        show "\<And>c. c \<in> set localCalls \<Longrightarrow> c \<notin> vis"
          using Step.inf_eq by  blast

        show "invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_txOrigin(tx \<mapsto> i)))
         (updateHb s_happensBefore vis localCalls) =
        (if firstTx
         then invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore \<union>
              {i' | i' c'.
                  c' \<in> vis \<and>
                  i_callOriginI_h s_callOrigin s_txOrigin c' \<triangleq> i' \<and>
                  (\<forall>c''. i_callOriginI_h s_callOrigin s_txOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis)} \<times>
              {i}
         else invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore -
              {i} \<times>
              {i'. (i, i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_txOrigin) s_happensBefore})"
          by (auto simp add: committedCallsH_simp invocation_hb_simp)
      qed



      show "Inv"
        unfolding Inv_def invContextH_def
      proof (fuzzy_rule inv_cont2[THEN conjunct1])
      qed (auto simp add:  committedCallsH_simp h1 h2 h3 h4, (auto simp add: Step))


    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "currentTx S'a i = None"
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

      show "\<And>tx'. None \<noteq> Some tx' \<Longrightarrow> txStatus S'a tx' \<noteq> Some Uncommitted"
        by (simp add: S'a_def Step)

      show "sorted_by (happensBefore S'a) []"
        by (simp add: sorted_by_empty)

      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a)
       (txOrigin S'a) (knownIds S'a) (invocOp S'a) (invocRes S'a)
       {x. generatedIds S'a x \<triangleq> i} generatedLocalPrivate (vis \<union> set localCalls) [] None False (cont ())"
      proof (fuzzy_rule inv_cont2[THEN conjunct2])
      qed (simp add: S'a_def Step)+

      obtain c where "c\<in>set localCalls"
        using `localCalls \<noteq> []` by fastforce


      thm Step(4)
      find_theorems name: Step


      show "False = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> txOrigin S'a tx \<triangleq> i \<and> txStatus S'a tx \<triangleq> Committed)"
        using  \<open>c \<in> set localCalls\<close>  by (auto simp add: S'a_def intro!: exI[where x=c] exI[where x=tx]
            Step.state_wellFormed Step.currentTx_eq state_wellFormed_current_transaction_origin
            Step.callOrigin_eq map_update_all_Some_same, simp add: Step.callOrigin_eq map_update_all_Some_same) 

      show "\<And>c. i_callOriginI S'a c \<triangleq> i \<Longrightarrow> c \<in> vis \<union> set localCalls"
        apply (auto simp add: S'a_def i_callOriginI_h_def split: option.splits)
        using Step.state_wellFormed Step.visibleCalls_eq state_wellFormed_ls_visibleCalls_callOrigin by  fastforce

      show "generatedLocalPrivate \<subseteq> {x. generatedIds S'a x \<triangleq> i}"
        using Step by (simp add: S'a_def)

      fix x
      assume c0: "x \<in> generatedLocalPrivate"

      from c0
      have "uid_is_private i S1 x"
        by (simp add: Step.Ball)

      show "uid_is_private i S'a x"
        unfolding uid_is_private_def
      proof (intro conjI)

        show " new_unique_not_in_other_invocations i S'a x"
          using  Step.step_s \<open>uid_is_private i S1 x\<close> action_def new_unique_not_in_other_invocations_maintained uid_is_private_def  by  blast

      qed (insert `uid_is_private i S1 x`, auto simp add: S'a_def uid_is_private_def new_unique_not_in_other_invocations_def)




    qed (simp add: S'a_def Step; fail)+
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
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
  have "action = ALocal True"
    and  Inv
    and S'a_def: "S'a = S1\<lparr>localState := localState S1(i \<mapsto> cont ())\<rparr>"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof

    show "Inv" using `Inv` .

    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      from `case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S1 c \<triangleq> tx'}`
      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        by (auto simp add: S'a_def split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step.sorted_by by  (simp add: S'a_def )



      show " execution_s_check progr i s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds
     s_invocOp s_invocRes {x. generatedIds S1 x \<triangleq> i} generatedLocalPrivate vis localCalls tx firstTx (cont ())"
      proof (fuzzy_rule cont)
        show "generatedLocal = {x. generatedIds S1 x \<triangleq> i}"
          using Step.generatedLocal_def by blast
      qed

      show "generatedLocalPrivate \<subseteq> {x. generatedIds S1 x \<triangleq> i}"
        using Step.Ball uid_is_private_def by auto
      
      fix x
      assume a0: "x \<in> generatedLocalPrivate"
      hence "uid_is_private i S1 x"
        by (simp add: Step.Ball)

      show "uid_is_private i S'a x"
        unfolding uid_is_private_def
      proof (intro conjI)
        show "new_unique_not_in_other_invocations i S'a x"
          using Step.step_s \<open>action = ALocal True\<close> \<open>uid_is_private i S1 x\<close> new_unique_not_in_other_invocations_maintained uid_is_private_def by  blast
      qed (insert `uid_is_private i S1 x`, auto simp add:S'a_def uid_is_private_def new_unique_not_in_other_invocations_def)


    qed (simp add: S'a_def Step; fail)+
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
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  (generatedLocalPrivate - uniqueIds op - uniqueIds res)
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
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPrivate
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
    ` currentTx S1 i \<triangleq> tx`
`visibleCalls S1 i \<triangleq> (vis \<union> set localCalls)`
  obtain c res
    where c0: "localState S1 i \<triangleq> (call op \<bind> cont)"
   and c1: "currentProc S1 i \<triangleq> toImpl"
   and c2: "currentTx S1 i \<triangleq> tx"
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
        using Step.case_option Step.callOrigin_eq by  (auto simp add: s S'a_def Step map_add_def map_of_None split: option.splits del: )


      have "c \<notin> set localCalls"
        using Step.state_wellFormed c3 fresh_c wellFormed_visibleCallsSubsetCalls2 by auto

      have "c \<notin> vis"
        by (meson Step.state_wellFormed UnCI c3 fresh_c wellFormed_visibleCallsSubsetCalls2)


      have "callOrigin S1 c = None"
        using wellFormed_callOrigin_dom[OF `state_wellFormed S1`] fresh_c by blast

      hence "s_callOrigin c = None"
        using `callOrigin S1 = map_update_all s_callOrigin localCalls (the (Some tx))`
        by (auto simp add: map_update_all_get split: if_splits)


      show "sorted_by (happensBefore S'a) (localCalls @ [c])"
      proof (auto simp add: sorted_by_append_iff sorted_by_single)
        from `sorted_by (happensBefore S1) localCalls`
        show "sorted_by (happensBefore S'a) localCalls"
          using \<open>c \<notin> set localCalls\<close> by (auto simp add: S'a_def sorted_by_def)

        thm Step(18)

        show "\<And>x. \<lbrakk>x \<in> set localCalls; (c, x) \<in> happensBefore S'a\<rbrakk> \<Longrightarrow> False"
          apply (auto simp add: S'a_def Step)
          using Step.state_wellFormed Step.happensBefore_eq fresh_c wellFormed_happensBefore_calls_l apply blast
          using \<open>c \<notin> vis\<close> apply blast 
          using \<open>c \<notin> set localCalls\<close> by auto
      qed

      from `vis \<inter> set (localCalls) = {}`
      show "vis \<inter> set (localCalls @ [c]) = {}"
        by (auto simp add: `c \<notin> vis`)


      show "dom s_callOrigin \<inter> set (localCalls @ [c]) = {}"
        apply (auto simp add: `s_callOrigin c = None`)
        using Step.inf_eq2 by blast 

      have "c \<notin> Field s_happensBefore"
        by (metis Field_Un Step.happensBefore_eq Step.state_wellFormed UnI1 fresh_c updateHb_simp_split wellFormed_happensBefore_Field)

      from this and `Field s_happensBefore \<inter> set localCalls = {}`
      show "Field s_happensBefore \<inter> set (localCalls @ [c]) = {}"
        by auto

      from `distinct localCalls` and `c\<notin>set localCalls`
      show "distinct (localCalls @ [c])"
        by auto

      show " execution_s_check progr i (s_calls(c \<mapsto> Call op res)) s_happensBefore s_callOrigin
       s_txOrigin s_knownIds s_invocOp s_invocRes {x. generatedIds S1 x \<triangleq> i} (generatedLocalPrivate - uniqueIds op - uniqueIds res) vis
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

        from `generatedLocal = {x. generatedIds S1 x \<triangleq> i}`
        show "generatedLocal = {x. generatedIds S1 x \<triangleq> i}" .
      qed

      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> txOrigin S1 tx \<triangleq> i \<and> txStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> txOrigin S'a tx \<triangleq> i \<and> txStatus S'a tx \<triangleq> Committed)"
        apply auto
         apply (auto simp add: S'a_def split: if_splits)
        using c2 not_uncommitted_cases wellFormed_currentTx_unique_h(2) 
        apply (simp add: wellFormed_currentTx_unique_h(2) Step.state_wellFormed)
        using \<open>callOrigin S1 c = None\<close> by force

      show "generatedLocalPrivate - uniqueIds op - uniqueIds res \<subseteq> {x. generatedIds S1 x \<triangleq> i}"
        using Step.Ball uid_is_private_def by auto

      
      fix x
      assume a0: "x \<in> generatedLocalPrivate - uniqueIds op - uniqueIds res"
      hence "uid_is_private i S1 x"
        using Step.Ball by auto


      show "uid_is_private i S'a x"
        unfolding uid_is_private_def
      proof (intro conjI)

        show "new_unique_not_in_other_invocations i S'a x"
          using Step.step_s \<open>uid_is_private i S1 x\<close> c4 new_unique_not_in_other_invocations_maintained uid_is_private_def by  blast


      qed (insert a0 `uid_is_private i S1 x`, auto simp add: S'a_def uid_is_private_def new_unique_not_in_calls_def new_unique_not_in_calls_result_def new_unique_not_in_other_invocations_def)


      

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
        txOrigin = s_txOrigin,
        knownIds = s_knownIds  \<union> uniqueIds res,
        invocOp = s_invocOp,
        invocRes = s_invocRes(i \<mapsto> res)
      \<rparr>"
shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_txOrigin 
  s_knownIds
  s_invocOp
  s_invocRes
  generatedLocal
  generatedLocalPriate
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
   and c3: "currentTx S1 i = None"
   and S'a_def: "S'a = S1 \<lparr>localState := (localState S1)(i := None), currentProc := (currentProc S1)(i := None), visibleCalls := (visibleCalls S1)(i := None), invocRes := invocRes S1(i \<mapsto> res), knownIds := knownIds S1 \<union> uniqueIds res\<rparr>"
   and Inv_def: "Inv \<longleftrightarrow> invariant (prog S1) (invContextH (callOrigin S1) (txOrigin S1) (txStatus S1) (happensBefore S1) (calls S1) (knownIds S1 \<union> uniqueIds res) (invocOp S1) (invocRes S1(i \<mapsto> res)))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> txStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus1: "txStatus S1 tx' \<noteq> Some Uncommitted" for tx'
      by auto

    have txStatus2: "txStatus S1 tx \<triangleq> y
      \<longleftrightarrow> (txStatus S1 tx \<triangleq> Committed \<and> y = Committed)" for tx y
      apply auto
      using txStatus.exhaust txStatus1 by auto



    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> txStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus3: "txStatus S1 tx \<triangleq> Committed
      \<longleftrightarrow>txStatus S1 tx \<noteq> None" for tx
      using txStatus.exhaust by (auto, blast)


    have commmitted: "committedTransactions S1 = dom s_txOrigin"
      apply (auto simp add: `txOrigin S1 = s_txOrigin`[symmetric] txStatus1)
       apply (simp add: Step.state_wellFormed txStatus3 wf_transaction_status_iff_origin)
      by (simp add: Step.state_wellFormed state_wellFormed_txStatus_txOrigin txStatus3)

    have committed2: "committedCalls S1 = dom (calls S1)"
      using Step.state_wellFormed committedCalls_allCommitted txStatus1 by  blast 

    hence committed3: "committedCallsH s_callOrigin (txStatus S1) =  dom s_calls"
      by (simp add: Step)


    show "Inv" 
      unfolding Inv_def invContextH_def
    proof (fuzzy_rule inv; (simp add: Step commmitted committed3))

      show "s_callOrigin = s_callOrigin |` dom s_calls"
      proof (rule restrict_map_noop[symmetric])
        show "dom s_callOrigin \<subseteq> dom s_calls"
          using Step.state_wellFormed Step.callOrigin_eq Step.calls_eq wellFormed_callOrigin_dom  by  fastforce
      qed

      show "s_happensBefore = s_happensBefore |r dom s_calls"
      proof (rule restrict_relation_noop[symmetric])
        show "Field s_happensBefore \<subseteq> dom s_calls"
          apply (auto simp add: Field_def)
          using Step.state_wellFormed Step.calls_eq Step.happensBefore_eq happensBefore_in_calls_left happensBefore_in_calls_right  by  fastforce+
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

lemmas execution_s_check_endAtomic' = execution_s_check_endAtomic[rotated 3, OF context_conjI]
  

lemmas repliss_proof_rules = 
  execution_s_check_newId
  execution_s_check_beginAtomic
  execution_s_check_endAtomic'
  execution_s_check_pause
  execution_s_check_dbop
  execution_s_check_return

method repliss_vcg_step = (rule repliss_proof_rules; (intro impI conjI)?; simp?; (intro impI conjI)?;  repliss_vcg_step?)

method repliss_vcg uses impl = ((simp add: impl)?, (unfold atomic_def skip_def)?, simp? , repliss_vcg_step)


declare newId_def[language_construct_defs] 
atomic_def[language_construct_defs]  
beginAtomic_def [language_construct_defs] 
call_def [language_construct_defs] 
skip_def [language_construct_defs] 
endAtomic_def [language_construct_defs] 
return_def[language_construct_defs] 


end