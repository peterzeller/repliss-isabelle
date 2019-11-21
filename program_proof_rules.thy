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
begin

thm execution_s_correct_def
  (*
 execution_s_correct ?progr ?S ?i \<equiv> \<forall>trace S'. ?S ~~ (?i, trace) \<leadsto>\<^sub>S* S' \<longrightarrow> traceCorrect_s ?progr trace
*)

find_consts "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"

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
  tx
  ls
 \<equiv>  (\<forall>trace S1 S'. 
           (S1 ~~ (i, trace) \<leadsto>\<^sub>S* S')
       \<longrightarrow> (\<forall>p t. (AInvoc p, t) \<notin> set trace)
       \<longrightarrow> state_wellFormed S1
       \<longrightarrow> calls S1 = s_calls
       \<longrightarrow> happensBefore S1 = s_happensBefore
       \<longrightarrow> callOrigin S1 = s_callOrigin
       \<longrightarrow> transactionOrigin S1 = s_transactionOrigin
       \<longrightarrow> knownIds S1 = s_knownIds
       \<longrightarrow> invocationOp S1 = s_invocationOp
       \<longrightarrow> invocationRes S1 = s_invocationRes
       \<longrightarrow> prog S1 = progr
       \<longrightarrow> generatedLocal = {x. generatedIds S1 x \<triangleq> i}
       \<longrightarrow> localState S1 i \<triangleq> ls
       \<longrightarrow> currentProc S1 i \<triangleq> toImpl
       \<longrightarrow> visibleCalls S1 i \<triangleq>  vis
       \<longrightarrow> currentTransaction S1 i = tx
       \<longrightarrow> (\<forall>tx'. tx \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted)
       \<longrightarrow> traceCorrect_s  trace)"

lemma beforeInvoc_execution_s_check: 
  assumes "s_invocationOp i = None"
  shows "
execution_s_check   progr   i  s_calls   s_happensBefore   s_callOrigin   s_transactionOrigin   s_knownIds   s_invocationOp  s_invocationRes  generatedLocal  vis  tx  ls
"
  using assms  apply (auto simp add: execution_s_check_def)
  apply (case_tac trace, auto)
   apply (simp add: traceCorrect_s_def)
  apply (auto simp add: steps_s_cons_simp Let_def)
  
  apply (erule step_s.cases, auto)
  using wf_localState_to_invocationOp apply auto
  by fastforce+






text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"



lemma execution_s_check_sound:
  assumes  "localState S i \<triangleq> ls"
    and "visibleCalls S i \<triangleq> vis"
    and "prog S = progr"
    and "currentProc S i \<triangleq> toImpl"
    and "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
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

    show "visibleCalls S i \<triangleq> vis"
      by (simp add: assms)


    show "currentTransaction S i \<noteq> Some tx' \<Longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted" for tx'
      by (simp add: assms)

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

  have currentTx: "currentTransaction S i = None"
    using a2 initialState_noTxns2 by blast


  show "execution_s_check progr i (calls S) (happensBefore S) (callOrigin S) (transactionOrigin S) (knownIds S) (invocationOp S)
     (invocationRes S) {} {} (currentTransaction S i) ls "
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
  assumes H: "\<And>S1 action Inv S'. \<lbrakk>
  S1 ~~ (i,action,Inv) \<leadsto>\<^sub>S S';
  invocationOp S1 i \<noteq> None;
  calls S1 = s_calls;
  happensBefore S1 = s_happensBefore;
  callOrigin S1 = s_callOrigin;
  transactionOrigin S1 = s_transactionOrigin;
  knownIds S1 = s_knownIds;
  invocationOp S1 = s_invocationOp;
  invocationRes S1 = s_invocationRes;
  prog S1 = progr;
  generatedLocal = {x. generatedIds S1 x \<triangleq> i};
  localState S1 i \<triangleq> ls;
  currentProc S1 i \<triangleq> toImpl;
  visibleCalls S1 i \<triangleq>  vis;
  currentTransaction S1 i = tx;
  state_wellFormed S1;
  \<And>tx'. tx \<noteq> Some tx' \<Longrightarrow>  transactionStatus S1 tx' \<noteq> Some Uncommitted
\<rbrakk> \<Longrightarrow> 
  Inv
\<and> (case localState S' i of
    None \<Rightarrow> True
  | Some LS' \<Rightarrow>
    execution_s_check
    progr 
    i
    (calls S')
    (happensBefore S')
    (callOrigin S')
    (transactionOrigin S')
    (knownIds S')
    (invocationOp S')
    (invocationRes S')
    {x. generatedIds S' x \<triangleq> i}
    (case visibleCalls S' i of Some vis \<Rightarrow> vis | None \<Rightarrow> {})
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


      from step
      have appliedH: "Inv \<and>
    (case localState S1' i of None \<Rightarrow> True
     | Some LS' \<Rightarrow>
         execution_s_check progr i (calls S1') (happensBefore S1') (callOrigin S1') (transactionOrigin S1') (knownIds S1') (invocationOp S1')
          (invocationRes S1') {x. generatedIds S1' x \<triangleq> i} (visibleCalls S1' i orElse {}) (currentTransaction S1' i) LS')"
        by (rule H; (simp add: A hasInvoc wf )?)



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

          with appliedH have "execution_s_check progr i (calls S1') (happensBefore S1') (callOrigin S1') (transactionOrigin S1') (knownIds S1') (invocationOp S1')
          (invocationRes S1') {x. generatedIds S1' x \<triangleq> i} (visibleCalls S1' i orElse {}) (currentTransaction S1' i) LS'"
            by auto

          then
          show ?thesis
          proof (rule execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format])
            show "S1' ~~ (i, trace') \<leadsto>\<^sub>S* S'" using steps .
            show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
              using Some local.step local.wf no_more_invoc state_wellFormed_combine_s1 steps by fastforce
            show "state_wellFormed S1'"
              using A local.step state_wellFormed_combine_s1 by blast
            show "prog S1' = progr"
              by (metis A steps unchangedProg)
            show "localState S1' i \<triangleq> LS'"
              by (simp add: Some)



            show "currentProc S1' i \<triangleq> toImpl"
              using step Some by (auto simp add: step_s.simps A wf_localState_to_invocationOp)

            show "visibleCalls S1' i \<triangleq> visibleCalls S1' i orElse {}"
              using step  Some  by (auto simp add: step_s.simps A wf_localState_to_invocationOp split: option.splits)

            show "\<And>tx'. currentTransaction S1' i \<noteq> Some tx' \<Longrightarrow> transactionStatus S1' tx' \<noteq> Some Uncommitted"
              using step Some  by (auto simp add: step_s.simps A wf_localState_to_invocationOp split: option.splits if_splits)



          qed auto
        qed
      qed
    qed
  qed
qed

lemma back_subst2: "\<lbrakk>P x'1 x'2; x'1 = x1; x'2 = x2 \<rbrakk> \<Longrightarrow>  P x1 x2" by auto 
lemma back_subst3: "\<lbrakk>P x'1 x'2 x'3; x'1 = x1; x'2 = x2; x'3 = x3 \<rbrakk> \<Longrightarrow>  P x1 x2 x3" by auto 
lemma back_subst4: "\<lbrakk>P x'1 x'2 x'3 x'4; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4" by auto 
lemma back_subst5: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5" by auto 
lemma back_subst6: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6" by auto 
lemma back_subst7: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7" by auto 
lemma back_subst8: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8" by auto 
lemma back_subst9: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9" by auto 
lemma back_subst10: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10" by auto 
lemma back_subst11: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11" by auto 
lemma back_subst12: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12" by auto 
lemma back_subst13: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13" by auto 
lemma back_subst14: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14" by auto 
lemma back_subst15: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15" by auto 
lemma back_subst16: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15 x'16; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15; x'16 = x16 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16" by auto 
lemma back_subst17: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15 x'16 x'17; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15; x'16 = x16; x'17 = x17 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17" by auto 
lemma back_subst18: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15 x'16 x'17 x'18; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15; x'16 = x16; x'17 = x17; x'18 = x18 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18" by auto 
lemma back_subst19: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15 x'16 x'17 x'18 x'19; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15; x'16 = x16; x'17 = x17; x'18 = x18; x'19 = x19 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19" by auto 
lemma back_subst20: "\<lbrakk>P x'1 x'2 x'3 x'4 x'5 x'6 x'7 x'8 x'9 x'10 x'11 x'12 x'13 x'14 x'15 x'16 x'17 x'18 x'19 x'20; x'1 = x1; x'2 = x2; x'3 = x3; x'4 = x4; x'5 = x5; x'6 = x6; x'7 = x7; x'8 = x8; x'9 = x9; x'10 = x10; x'11 = x11; x'12 = x12; x'13 = x13; x'14 = x14; x'15 = x15; x'16 = x16; x'17 = x17; x'18 = x18; x'19 = x19; x'20 = x20 \<rbrakk> \<Longrightarrow>  P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20" by auto 

method back_subst for P :: "'a1 \<Rightarrow> bool" uses rule = (rule back_subst[where P=P], rule rule)
method back_subst2 for P :: "'a1\<Rightarrow>'a2 \<Rightarrow> bool" uses rule = (rule back_subst2[where P=P], rule rule) 
method back_subst3 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3 \<Rightarrow> bool" uses rule = (rule back_subst3[where P=P], rule rule) 
method back_subst4 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4 \<Rightarrow> bool" uses rule = (rule back_subst4[where P=P], rule rule) 
method back_subst5 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5 \<Rightarrow> bool" uses rule = (rule back_subst5[where P=P], rule rule) 
method back_subst6 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6 \<Rightarrow> bool" uses rule = (rule back_subst6[where P=P], rule rule) 
method back_subst7 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7 \<Rightarrow> bool" uses rule = (rule back_subst7[where P=P], rule rule) 
method back_subst8 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8 \<Rightarrow> bool" uses rule = (rule back_subst8[where P=P], rule rule) 
method back_subst9 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9 \<Rightarrow> bool" uses rule = (rule back_subst9[where P=P], rule rule) 
method back_subst10 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10 \<Rightarrow> bool" uses rule = (rule back_subst10[where P=P], rule rule) 
method back_subst11 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11 \<Rightarrow> bool" uses rule = (rule back_subst11[where P=P], rule rule) 
method back_subst12 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12 \<Rightarrow> bool" uses rule = (rule back_subst12[where P=P], rule rule) 
method back_subst13 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13 \<Rightarrow> bool" uses rule = (rule back_subst13[where P=P], rule rule) 
method back_subst14 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14 \<Rightarrow> bool" uses rule = (rule back_subst14[where P=P], rule rule) 
method back_subst15 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15 \<Rightarrow> bool" uses rule = (rule back_subst15[where P=P], rule rule) 
method back_subst16 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15\<Rightarrow>'a16 \<Rightarrow> bool" uses rule = (rule back_subst16[where P=P], rule rule) 
method back_subst17 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15\<Rightarrow>'a16\<Rightarrow>'a17 \<Rightarrow> bool" uses rule = (rule back_subst17[where P=P], rule rule) 
method back_subst18 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15\<Rightarrow>'a16\<Rightarrow>'a17\<Rightarrow>'a18 \<Rightarrow> bool" uses rule = (rule back_subst18[where P=P], rule rule) 
method back_subst19 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15\<Rightarrow>'a16\<Rightarrow>'a17\<Rightarrow>'a18\<Rightarrow>'a19 \<Rightarrow> bool" uses rule = (rule back_subst19[where P=P], rule rule) 
method back_subst20 for P :: "'a1\<Rightarrow>'a2\<Rightarrow>'a3\<Rightarrow>'a4\<Rightarrow>'a5\<Rightarrow>'a6\<Rightarrow>'a7\<Rightarrow>'a8\<Rightarrow>'a9\<Rightarrow>'a10\<Rightarrow>'a11\<Rightarrow>'a12\<Rightarrow>'a13\<Rightarrow>'a14\<Rightarrow>'a15\<Rightarrow>'a16\<Rightarrow>'a17\<Rightarrow>'a18\<Rightarrow>'a19\<Rightarrow>'a20 \<Rightarrow> bool" uses rule = (rule back_subst20[where P=P], rule rule) 

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
  tx
  (newId P \<bind> cont)
"
proof (rule  execution_s_check_single_step, auto simp add: step_s.simps split: if_splits, goal_cases "goal")
  case (goal S1 Inv y uidv)
  show ?case 
  proof (rule back_subst13[where P=execution_s_check], rule cont; (simp add: goal; fail)?)
    show "localGenerated \<union> {to_nat uidv} = {x. x \<noteq> to_nat uidv \<longrightarrow> generatedIds S1 x \<triangleq> i}"
      using `localGenerated = {x. generatedIds S1 x \<triangleq> i}` by auto

    show "new_unique_not_in_invocationOp s_invocationOp uidv"
      using assms(2) goal(12) goal(14) goal(18) goal(5) new_unique_not_in_invocationOp_def wf_onlyGeneratedIdsInInvocationOps by blast
    show "new_unique_not_in_invocationRes s_invocationRes uidv"
      using assms(2) goal(13) goal(14) goal(18) goal(5) new_unique_not_in_invocationRes_def wf_onlyGeneratedIdsInInvocationRes by blast
    have "to_nat uidv \<notin> uniqueIds opr" if "calls S1 c \<triangleq> Call opr r" for c opr r
    proof (rule wf_onlyGeneratedIdsInCalls)
      show "calls S1 c \<triangleq> Call opr r" using that .
      show "state_wellFormed S1"
        by (simp add: goal(5)) 

      show "program_wellFormed (prog S1)"
        using assms(2) goal(14) by blast

      show "generatedIds S1 (to_nat uidv) = None"
        by (simp add: goal(18))
    qed

    from this
    show " new_unique_not_in_calls s_calls uidv"
      by (simp add: goal(7) new_unique_not_in_calls_def)

    show " new_unique_not_in_calls_result s_calls uidv"
      using assms(2) goal(14) goal(18) goal(5) goal(7) new_unique_not_in_calls_result_def wf_onlyGeneratedIdsInCallResults by blast

    show "to_nat uidv \<notin> s_knownIds"
      using assms(2) goal(11) goal(14) goal(18) goal(5) wf_onlyGeneratedIdsInKnownIds by blast

  qed
qed


lemma restrict_map_noop: "dom m \<subseteq> S \<Longrightarrow> m |` S = m"
   using domIff by (auto simp add: restrict_map_def intro!: ext, force)


lemma restrict_map_noop2[simp]: "m |` dom m = m"
  by (simp add: restrict_map_noop)

lemma restrict_relation_noop: "Field r \<subseteq> S \<Longrightarrow> r |r S = r"
  by (auto simp add: restrict_relation_def FieldI1 FieldI2 subset_h1)


lemma execution_s_check_beginAtomic:
  assumes "tx = None"
    and "program_wellFormed progr"
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
- valid snapshot (causally + transactionally)
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
  tx
  (beginAtomic \<bind> cont)
"
proof (rule  execution_s_check_single_step, auto simp add: step_s.simps split: if_splits, goal_cases "goal")
  case (goal S1 Inv y t S'a vis')
  show ?case 
  proof (rule back_subst13[where P=execution_s_check], rule cont; (rule refl)?)
    show "localGenerated = {x. generatedIds S'a x \<triangleq> i}"
      apply (auto simp add: goal)
      using `state_monotonicGrowth i S1 S'a` state_monotonicGrowth_generatedIds apply blast
      using goal(21) state_monotonicGrowth_generatedIds_same1 by blast

    have [simp]: "(prog S1) = progr"
      by (simp add: goal(14))

    show "progr = prog S1" by simp

    have [simp]: "committedCalls S'a = dom(calls S'a)"
      using committedCallsH_def committedCalls_allCommitted
        `\<forall>x. transactionStatus S'a x \<noteq> Some Uncommitted`
        `state_wellFormed S'a`
      by (fastforce)

    show "invariant progr
     \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
        transactionOrigin = transactionOrigin S'a, knownIds = knownIds S'a, invocationOp = invocationOp S'a,
        invocationRes = invocationRes S'a\<rparr>"
      using `invariant (prog S1) (invContext S'a)`
    proof (auto simp add: invContextH_def elim!: back_subst[where P="invariant progr"])
      
      show "\<And>a b. (a, b) \<in> happensBefore S'a |r dom (calls S'a) \<Longrightarrow> (a, b) \<in> happensBefore S'a"
        by (simp add: restrict_relation_def)
      show "\<And>a b. (a, b) \<in> happensBefore S'a \<Longrightarrow> (a, b) \<in> happensBefore S'a |r dom (calls S'a)"
        by (simp add: goal(25) happensBefore_in_calls_left happensBefore_in_calls_right restrict_relation_def)
      show "callOrigin S'a |` dom (calls S'a) = callOrigin S'a"
        by (simp add: goal(25) restrict_map_noop wellFormed_callOrigin_dom)

      show "transactionOrigin S'a |` committedTransactions S'a = transactionOrigin S'a"
      proof (rule restrict_map_noop)
        show "dom (transactionOrigin S'a) \<subseteq> committedTransactions S'a"
          apply auto
          by (metis (no_types, lifting) goal(25) goal(24) option.exhaust option.simps(3) transactionStatus.exhaust wf_transactionOrigin_and_status)
      qed
    qed
  qed
qed


lemma execution_s_check_endAtomic:
  assumes "tx \<noteq> None"
    and "program_wellFormed progr"
and assert_inv: "invariant progr 
     \<lparr>calls = s_calls, 
      happensBefore = s_happensBefore,
      callOrigin = s_callOrigin,
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
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin
  s_knownIds 
  s_invocationOp
  s_invocationRes
  localGenerated
  vis
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
  tx
  (endAtomic \<bind> cont)
"
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



end