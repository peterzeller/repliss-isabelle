theory single_invocation_correctness
  imports approach execution_invariants_s
begin

section {* Single-invocation corrrectness *}

text {* This theory includes techniques to prove that a program is correct in the single-invocation semantics. *}

text {*
  Start with initial state,
  
  then steps
  
  finally return and last check
  
  somehow automated

*}


fun updateHb where
  updateHb_nil: "updateHb hb vis [] = hb"
| updateHb_cons[simp del]: "updateHb hb vis (c#cs) = updateHb (hb \<union> vis \<times> {c}) (insert c vis) cs"

lemma updateHb_single: "updateHb hb vis [c] = hb \<union> vis \<times> {c}"
  by (simp add: updateHb_cons)

lemma updateHb_chain: 
  assumes "vis' = set cs \<union> vis"
  shows "updateHb (updateHb hb vis cs) vis' [c] = updateHb hb vis (cs@[c])"
using assms apply (induct cs arbitrary: hb vis vis' c )
  by (fastforce simp add:  updateHb_cons)+






(* check program (with a given start-state, bound by a number of steps) *)
definition checkCorrectF :: "(('localState, 'any) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool) 
                           \<Rightarrow> ('localState, 'any) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool" where
"checkCorrectF \<equiv> (\<lambda>checkCorrect' (progr, S, i).
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            checkCorrect' (progr, (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>), i)
        | BeginAtomic ls \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S' vis newTxns.
                transactionStatus S t = None
              \<and> invariant_all S'
              \<and> state_wellFormed S'
              \<and> state_monotonicGrowth S S'
              \<and> localState S' i \<triangleq> ls
              \<and> currentProc S' i \<triangleq> impl
              \<and> currentTransaction S' i \<triangleq> t
              \<and> transactionStatus S' t \<triangleq> Uncommited
              \<and> transactionOrigin S' t \<triangleq> i
              \<and> (\<forall>c. callOrigin S' c \<noteq> Some t)
              \<and> visibleCalls S i \<triangleq> vis
              \<and> visibleCalls S' i \<triangleq> (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')
              \<and> newTxns \<subseteq> dom (transactionStatus S')
              \<and> consistentSnapshot S' (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')
              \<and> (\<forall>x. x \<noteq> t \<longrightarrow> transactionStatus S' x \<noteq> Some Uncommited)
              \<longrightarrow> checkCorrect' (progr, S', i))
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                let S' = (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>) in
                  (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) 
                    \<longrightarrow> (invariant_all S'
                         \<and> (invariant_all S' \<longrightarrow> checkCorrect' (progr, S', i)))
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid.
            uid \<notin> generatedIds S
            \<longrightarrow> checkCorrect' (progr, (S\<lparr>localState := (localState S)(i \<mapsto> ls uid), generatedIds := generatedIds S \<union> {uid} \<rparr>), i)
          )
        | DbOperation Op args ls \<Rightarrow> 
           (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                  (\<exists>res. querySpec progr Op args (getContext S i) res)
                  \<and>
                  (\<forall>c res vis. 
                      calls S c = None
                    \<and> querySpec progr Op args (getContext S i) res
                    \<and> visibleCalls S i \<triangleq> vis
                    \<longrightarrow> checkCorrect' (progr, (S\<lparr>
                          localState := (localState S)(i \<mapsto> ls res), 
                          calls := (calls S)(c \<mapsto> Call Op args res ),
                          callOrigin := (callOrigin S)(c \<mapsto> t),
                          visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                          happensBefore := updateHb (happensBefore S) vis [c]  \<rparr>), i)
                  )
           )
        | Return res \<Rightarrow> 
            currentTransaction S i = None
            \<and> (let S' = (S\<lparr>
                 localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>) in
               (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow> invariant_all S'    
            )
        )))
"

lemma checkCorrectF_mono[simp]:
"mono checkCorrectF"
proof (rule monoI)
  show "checkCorrectF x \<le> checkCorrectF y" if c0: "x \<le> y"  for  x :: "(('localState, 'any) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool)" and y
    apply (auto simp add: checkCorrectF_def Let_def split: option.splits localAction.splits)
    using c0 apply fastforce
    using [[smt_solver=cvc4]]
       apply (smt le_boolD le_funD that wellFormed_currentTransactionUncommited)
    apply (smt le_boolD le_funD that)
    apply (smt le_boolD le_funD that)
    using le_funD that by force

qed


definition checkCorrect :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> bool" where
 "checkCorrect progr S i \<equiv> lfp checkCorrectF (progr, S, i)"



schematic_goal checkCorrect_simps:
  "checkCorrect progr S i = ?F"
  apply (subst checkCorrect_def)
  apply (subst lfp_unfold)
   apply simp
  apply (subst checkCorrectF_def)
  apply (fold checkCorrect_def)
  apply (rule refl)
  done


lemma checkCorrect_noProc:
  assumes "currentProc S i = None"
  shows "checkCorrect progr S i"
  using assms  by (auto simp add: checkCorrect_simps)


lemma prog_invariant:
  assumes steps: "S_start ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
  shows "prog S_fin = prog S_start"
  using steps proof (induct rule: step_s_induct)
  case initial
  then show ?case by auto
next
  case (step tr S a S')
  then show ?case 
    by (auto simp add: step_s.simps)
qed

(*

lemma checkCorrect_traceCorrect:
  assumes check: "checkCorrect program S_start i bound"
    and steps: "S_start ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and trace_len: "length trace < bound"
    and prog: "prog S_start = program"
    and noInvocation: "\<And>a c. (a,c)\<in>set trace \<Longrightarrow> \<not> isAInvoc a"
  shows "traceCorrect_s program trace \<and> checkCorrect program S_fin i (bound - length trace)"
  using steps check trace_len noInvocation proof (induct "length trace" arbitrary: S_fin trace)
  case 0
  hence [simp]: "trace = []" by simp
  with `S_start ~~ (i, trace) \<leadsto>\<^sub>S* S_fin` 
  have [simp]: "S_fin = S_start"
    by (simp add: steps_s_empty) 

  from `checkCorrect program S_start i bound` 
  show ?case
    by (auto simp add: traceCorrect_s_def )
next
  case (Suc n)

  from `Suc n = length trace`
  obtain tr a where trace_split: "trace = tr@[a]"
    by (metis Zero_not_Suc list.size(3) rev_exhaust)

  with `S_start ~~ (i, trace) \<leadsto>\<^sub>S* S_fin`  
  obtain S where steps_tr: "S_start ~~ (i, tr) \<leadsto>\<^sub>S* S" and step_a: "S ~~ (i, a) \<leadsto>\<^sub>S S_fin"
    using steps_s_append_simp steps_s_single by blast


  have IH: "traceCorrect_s program tr \<and> checkCorrect program S i (bound - length tr)"
  proof (rule Suc.hyps)
    show "n = length tr"
      using Suc.hyps(2) trace_split by auto
    show "S_start ~~ (i, tr) \<leadsto>\<^sub>S* S" using steps_tr .
    show "checkCorrect program S_start i bound" using `checkCorrect program S_start i bound` .
    show "length tr < bound"
      using Suc.hyps(2) Suc.prems(3) \<open>n = length tr\<close> by linarith 
    show "\<And>a c. (a, c) \<in> set tr \<Longrightarrow> \<not> isAInvoc a"
      using Suc.prems(4) trace_split by auto
  qed
  hence "traceCorrect_s program tr" and "checkCorrect program S i (bound - length tr)" by auto

  obtain bound' where bound'_def: "bound - length tr = Suc bound'"
    by (metis Suc.prems(3) Suc_diff_Suc Suc_lessD length_append_singleton trace_split) 

  hence checkCorrect_S: "checkCorrect program S i (Suc bound')"
    using `checkCorrect program S i (bound - length tr)` by simp

  have [simp]: "bound - length trace = bound'"
    by (metis Suc_diff_Suc Suc_inject bound'_def length_append_singleton trace_split zero_less_Suc zero_less_diff)  

  have [simp]: "prog S = program"
    using prog prog_invariant steps_tr by blast

  have a_not_invoc: "\<not> isAInvoc (fst a)"
    by (metis Suc.prems(4) list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1 trace_split)


  from step_a
  have "snd a \<and> checkCorrect program S_fin i (bound - length trace)" 
  proof (cases rule: step_s.cases)
    case (local ls f ls')
    then show ?thesis 
      using checkCorrect_S by auto


  next
    case (newId ls f ls' uid)
    then show ?thesis using checkCorrect_S by auto
  next
    case (beginAtomic ls f ls' t txns)
    then show ?thesis 
      using checkCorrect_S apply auto
      by (metis local.beginAtomic(15))

  next
    case (endAtomic ls f ls' t valid)
    then show ?thesis 
      using checkCorrect_S apply auto
        apply (auto simp add: split: if_splits)

      sorry

  next
    case (dbop ls f Op args ls' t c res vis)
    then show ?thesis 
      using checkCorrect_S by auto
  next
    case (invocation procName args initState impl C' valid)
    then show ?thesis 
      using a_not_invoc by (case_tac a, auto simp add: isAInvoc_def)
  next
    case (return ls f res valid)
    then show ?thesis using checkCorrect_S 
      apply (case_tac bound', auto)
      apply (metis Suc.prems(3) \<open>bound - length trace = bound'\<close> less_numeral_extra(3) zero_less_diff)

      sorry
  qed
  thus "traceCorrect_s program trace \<and> checkCorrect program S_fin i (bound - length trace)"
    apply auto
    by (metis IH Pair_inject Un_insert_right append_Nil2 insert_iff list.set(2) prod.collapse set_append traceCorrect_s_def trace_split)

qed  


*)
(*
now we have it without invocations, so we have to prove that invocations can only be at the beginning, then we are in initial states ...
*)

lemma use_map_le:
  assumes "m x \<triangleq> y" and "m  \<subseteq>\<^sub>m m'"
  shows "m' x \<triangleq> y"
  using assms
  by (metis domI map_le_def) 

lemma has_invocationOp_forever:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and "invocationOp S i \<triangleq> info"
  shows "invocationOp S' i \<triangleq> info"

  using assms proof (induct rule: step_s_induct)
  case initial
  then show ?case by auto
next
  case (step tr S a S')
  then show ?case apply (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
    by (metis prod.collapse)


qed

(*
lemma wf_localState_has_invocationOp:
assumes wf: "state_wellFormed S"
    and ls: "localState S i \<triangleq> ls"
shows "invocationOp S i \<noteq> None"  
using assms
  using wellFormed_invoc_notStarted(2) by fastforce 
*)

lemma has_invocationOp_afterOneStep:
  assumes step: "S ~~ (i, a) \<leadsto>\<^sub>S S'"
    and wf: "state_wellFormed_s S i"
  shows "invocationOp S' i \<noteq> None"   
  using step wf apply (auto simp add: step_s.simps wf_s_localState_to_invocationOp2)
  by (meson state_monotonicGrowth_def use_map_le wf_s_localState_to_invocationOp2)



lemma has_invocationOp_afterStart:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and notEmpty: "trace \<noteq> []"
    and wf: "state_wellFormed_s S i"
  shows "invocationOp S' i \<noteq> None"   
  using steps notEmpty wf proof (induct rule: step_s_induct)
  case initial
  then show ?case
    by simp  
next
  case (step tr S a S')
  have "state_wellFormed_s S i"
    using local.wf state_wellFormed_s_def step.step steps_s_append by blast 

  from `S ~~ (i, a) \<leadsto>\<^sub>S S'` and `state_wellFormed_s S i`
  show ?case 
    by (rule has_invocationOp_afterOneStep)
qed


lemma invocations_only_in_beginning:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and wf: "state_wellFormed_s S i"
    and notStarted: "invocationOp S i = None"
    and traceLen: "j < length trace"
  shows "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
proof -

  from steps
  obtain S_mid where "S ~~ (i, take j trace) \<leadsto>\<^sub>S* S_mid" and "S_mid ~~ (i, drop j trace) \<leadsto>\<^sub>S* S'"
    using steps_s_append_simp by force


  obtain Sa where firstStep: "S ~~ (i, hd trace) \<leadsto>\<^sub>S Sa" and afterFirstStep: "Sa ~~ (i, tl trace) \<leadsto>\<^sub>S* S'"
    by (metis Cons_nth_drop_Suc append.assoc append_take_drop_id hd_Cons_tl snoc_eq_iff_butlast steps steps_s_cons_simp traceLen)

  with notStarted
  have startsWithInvoc: "isAInvoc (fst (hd trace))"
    by (auto simp add: step_s.simps isAInvoc_def local.wf wf_s_localState_to_invocationOp)


  {
    assume "j = 0"
    hence "isAInvoc (fst (trace ! j))" 
      using startsWithInvoc hd_drop_conv_nth traceLen by force 
  }
  moreover
  {
    assume "j \<noteq> 0"

    from afterFirstStep
    obtain Sc where steps_until_after_j: "Sa ~~ (i, take j (tl trace)) \<leadsto>\<^sub>S* Sc"
      by (metis append_take_drop_id steps_s_append_simp)


(* get Sb so that S Sa Sb S*)
    from steps_until_after_j
    have "Sa ~~ (i, (take (j-1) (tl trace))@[trace!j]) \<leadsto>\<^sub>S* Sc"
      by (metis \<open>j \<noteq> 0\<close> drop_Nil drop_eq_Nil hd_drop_conv_nth leD take_eq_Nil take_hd_drop take_tl tl_append2 tl_take traceLen)
    from this    
    obtain Sb 
      where steps1: "Sa ~~ (i, take (j-1) (tl trace)) \<leadsto>\<^sub>S* Sb"
        and step_j: "Sb ~~ (i, trace ! j) \<leadsto>\<^sub>S Sc"
      by (auto simp add: steps_s_append_simp steps_s_single)

    have "invocationOp Sa i \<noteq> None"
      using firstStep has_invocationOp_afterOneStep local.wf by blast  

    hence "invocationOp Sb i \<noteq> None"
      using has_invocationOp_forever steps1 by blast

    with step_j 
    have "\<not>isAInvoc (fst (trace ! j))" 
      by (auto simp add: step_s.simps isAInvoc_def)
  }
  ultimately
  show "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
    by blast
qed    

lemma initialState_noTxns1:
  assumes initS: "S \<in> initialStates program i"
  shows "transactionStatus S tx \<noteq> Some Uncommited"
  using initS by (auto simp add: initialStates_def)

lemma initialState_noTxns2:
  assumes initS: "S \<in> initialStates program i"
  shows "currentTransaction S i' = None"
  using initS apply (auto simp add: initialStates_def)
  by (meson option.exhaust wellFormed_currentTransaction_unique_h(2))


lemma steps_s_noOtherTx:
  assumes steps: "initS ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and initS: "initS \<in> initialStates program i"
    and "i' \<noteq> i"
  shows "currentTransaction S_fin i' = None"
  using steps proof (induct rule: step_s_induct)
  case initial
  from initS
  show "currentTransaction initS i' = None"
    using initialState_noTxns2 by auto

next
  case (step tr S a S')


  from `S ~~ (i, a) \<leadsto>\<^sub>S S'` 
  show ?case 
    apply (auto simp add: step_s.simps `currentTransaction S i' = None`)
    apply (metis assms(3) option.exhaust wellFormed_currentTransaction_unique wellFormed_currentTransaction_unique_h(2))
    by (meson option.exhaust wellFormed_currentTransaction_unique_h(2))
qed

lemma show_traceCorrect_s_1:
  assumes initialCorrect: "\<And>S. S\<in>initialStates program i \<Longrightarrow> invariant_all S "
    and check: "\<And>S. S\<in>initialStates program i \<Longrightarrow> checkCorrect program S i"
    and steps: "initS ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and initS: "initS \<in> initialStates program i"
    and trace_len2: "0 < length trace"
    and initS_wf: "state_wellFormed initS"
  shows "traceCorrect_s program trace \<and> checkCorrect program S_fin i"
  using steps check  trace_len2 proof (induct "length trace" arbitrary: trace S_fin)
  case 0
  thus ?case
    by simp 

next
  case (Suc trLen trace S_fin)

  obtain tr a where tr_def: "trace = tr@[a]"
    by (metis Suc.hyps(2) Zero_not_Suc list.size(3) rev_exhaust)

  obtain a_action a_inv where a_def[simp]: "a = (a_action, a_inv)"
    by fastforce


  have  wf: "state_wellFormed_s initS i"
    using initS initialStates_wf steps_s_refl  by blast


  from `initS ~~ (i, trace) \<leadsto>\<^sub>S* S_fin`
  obtain S_pre 
    where steps_pre: "initS ~~ (i, tr) \<leadsto>\<^sub>S* S_pre"
      and step_final: "S_pre ~~ (i, a) \<leadsto>\<^sub>S S_fin"
    by (auto simp add: tr_def steps_s_append_simp steps_s_single)



  show ?case
  proof (cases "trLen > 0")
    case True

    have hasInvocation: "invocationOp S_pre i \<noteq> None"
      using Suc.hyps(2) True has_invocationOp_afterStart local.wf steps_pre tr_def by fastforce

    have "prog initS = program"
      using initS by (auto simp add: initialStates_def)
    hence [simp]: "prog S_pre = program"
      using prog_invariant steps_pre by blast

    have "traceCorrect_s program tr \<and> checkCorrect program S_pre i"
    proof (rule Suc.hyps)
      show "trLen = length tr"
        using `Suc trLen = length trace` tr_def by auto

      show "initS ~~ (i, tr) \<leadsto>\<^sub>S* S_pre"
        by (simp add: steps_pre)

      show "\<And>S. S \<in> initialStates program i \<Longrightarrow> checkCorrect program S i"
        using check by blast

      show "0 < length tr"
        using True \<open>trLen = length tr\<close> by auto
    qed
    hence tr_correct: "traceCorrect_s program tr"
      and S_pre_correct: "checkCorrect program S_pre i "
      using \<open>traceCorrect_s program tr \<and> checkCorrect program S_pre i\<close> by blast+

    show "traceCorrect_s program trace \<and> checkCorrect program S_fin i"
    proof (cases "currentTransaction S_pre i")
      case (Some tx)
      hence tx1: "currentTransaction S_pre i \<triangleq> tx"
        by simp




      have tx2: "transactionStatus S_pre tx \<triangleq> Uncommited"
        using initS initialStates_wf state_wellFormed_s_currentTransactions_iff_uncommitted steps_pre tx1 by blast 

      have onlyOneTx: "transactionStatus S_pre t \<noteq> Some Uncommited" if "t \<noteq> tx" for t
        using initS initialStates_wf state_wellFormed_s_currentTransactions_iff_uncommitted steps_pre that tx1 by fastforce

      from S_pre_correct tr_correct step_final  
      have "a_inv = True" (*and "checkCorrect program S_fin i (bound - length trace)" *)
        apply (subst(asm) checkCorrect_simps)
        by (auto simp add: tx1 step_s.simps Let_def hasInvocation onlyOneTx split: option.splits if_splits)
        


      from S_pre_correct step_final
      have cc: "checkCorrect program S_fin i" 
        apply (subst (asm) checkCorrect_simps)
        apply (auto simp add: step_s.simps Let_def hasInvocation \<open>a_inv = True\<close> tx1 split: option.splits if_splits)
        using onlyOneTx tx1 apply auto[1]
        apply (drule_tac x=c in spec)
        apply auto
        by (simp add: updateHb_single)



      from tr_correct `a_inv = True`
      have "traceCorrect_s program trace"
        by (auto simp add: traceCorrect_s_def tr_def)

      with cc
      show ?thesis by blast
    next
      case None

      have onlyOneTx: "transactionStatus S_pre t \<noteq> Some Uncommited" for t
        using None initS initialStates_wf state_wellFormed_s_currentTransactions_iff_uncommitted steps_pre by fastforce


      from S_pre_correct tr_correct step_final  
      have "a_inv = True" (*and "checkCorrect program S_fin i (bound - length trace)" *)
        apply (subst(asm) checkCorrect_simps)
        by (auto simp add: onlyOneTx step_s.simps Let_def hasInvocation  split: option.splits if_splits)

      from S_pre_correct step_final
      have cc: "checkCorrect program S_fin i" 
        apply (subst(asm) checkCorrect_simps)
        apply (auto simp add: step_s.simps Let_def hasInvocation \<open>a_inv = True\<close> onlyOneTx None  split: option.splits if_splits)
        using wellFormed_currentTransactionUncommited apply blast
        apply (simp add: checkCorrect_noProc)
        done


      from tr_correct `a_inv = True`
      have "traceCorrect_s program trace"
        by (auto simp add: traceCorrect_s_def tr_def)



      show "traceCorrect_s program trace \<and> checkCorrect program S_fin i"
        by (simp add: \<open>traceCorrect_s program trace\<close> cc)
    qed

  next
    case False
    hence [simp]: "tr = []"
      using Suc.hyps(2) tr_def by auto

    hence [simp]: "S_pre = initS"
      using steps_pre steps_s_empty by blast   

    hence "initS ~~ (i, a) \<leadsto>\<^sub>S S_fin"
      using step_final by blast

    have initS_correct: "checkCorrect program initS i"
      by (simp add: check initS)  

    from `initS \<in> initialStates program i`
    have hasInvocationOp: "invocationOp initS i \<noteq> None"
      by (auto simp add: initialStates_def)

    from `initS \<in> initialStates program i`
    have noTransaction: "currentTransaction initS i = None"  
      apply (auto simp add: initialStates_def)
      using wellFormed_invoc_notStarted(1) by blast


    from step_final 
    have "a_inv" 
    proof (cases rule: step_s.cases)
      case (local ls f ls')
      then show ?thesis by auto
    next
      case (newId ls f ls' uid)
      then show ?thesis  by auto
    next
      case (beginAtomic ls f ls' t txns)
      then show ?thesis  by auto
    next
      case (endAtomic ls f ls' t valid)
      then show ?thesis
        by (simp add: noTransaction) 
    next
      case (dbop ls f Op args ls' t c res vis)
      then show ?thesis  by auto
    next
      case (invocation procName args initState impl C' valid)
      then show ?thesis
        by (simp add: hasInvocationOp) 
    next
      case (return ls f res valid)
      then show ?thesis  
        using initS_correct
        apply (subst(asm) checkCorrect_simps)
        apply (auto simp add: )
        using initS initialState_noTxns1 by blast
    qed


    hence "traceCorrect_s program trace"
      by (auto simp add: tr_def traceCorrect_s_def)   




    from step_final   
    have "checkCorrect program S_fin i "
    proof (cases rule: step_s.cases)
      case (local ls f ls')
      then show ?thesis 
        using initS_correct by (auto simp add: checkCorrect_simps)
    next
      case (newId ls f ls' uid)
      then show ?thesis using initS_correct by (auto simp add: checkCorrect_simps)
    next
      case (beginAtomic ls f ls' t txns)
      then show ?thesis using initS_correct 
        apply (auto simp add: checkCorrect_simps )
        using `transactionStatus S_fin t \<triangleq> Uncommited` by blast
    next
      case (endAtomic ls f ls' t valid)
      then show ?thesis using initS_correct
        by (simp add: noTransaction)
    next
      case (dbop ls f Op args ls' t c res vis)
      then show ?thesis using initS_correct 
        by (auto simp add:  noTransaction)
    next
      case (invocation procName args initState impl C' valid)
      then show ?thesis using initS_correct 
        by (auto simp add:  hasInvocationOp)
    next
      case (return ls f res valid)
      then show ?thesis using initS_correct 
        by (auto simp add: checkCorrect_simps)
    qed

    with `traceCorrect_s program trace`
    show ?thesis
      by (auto simp add: checkCorrect_simps)
  qed
qed


lemma "\<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> False"
  by simp


lemma show_program_correct_single_invocation:
  assumes initialCorrect: "\<And>S i. S\<in>initialStates program i \<Longrightarrow> invariant_all S "
    and check: "\<And>S i. \<lbrakk>S\<in>initialStates program i; invariant_all S; state_wellFormed S\<rbrakk> \<Longrightarrow> checkCorrect program S i"
  shows "programCorrect_s program"
proof (auto simp add: programCorrect_s_def)
  fix trace i S_fin
  assume steps: "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"

  {
    fix a tr
    assume trace_def: "trace = a#tr"

    with steps
    obtain S_init 
      where step1: "initialState program ~~ (i, a) \<leadsto>\<^sub>S S_init"
        and steps': "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S_fin"
      using steps_s_cons_simp by blast

    find_theorems isAInvoc

    thm invocations_only_in_beginning[OF steps, where j=0, simplified]
    have "isAInvoc (fst (trace ! 0))"
    proof (rule invocations_only_in_beginning[OF steps, where j=0, simplified])
      show "state_wellFormed_s (initialState program) i"
        using state_wellFormed_s_def steps_s_refl by blast
      show "invocationOp (initialState program) i = None"
        by (simp add: initialState_def)
      show "trace \<noteq> [] "
        by (simp add: trace_def)
    qed
    from this
    obtain p args invInitial where a_def: "a = (AInvoc p args, invInitial)"
      by (cases a, auto simp add: trace_def isAInvoc_def split: action.splits)


    from step1 and a_def
    have "invInitial"
      apply (auto simp add: step_s.simps)
      apply (erule notE, rule initialCorrect[where i=i])
      apply (auto simp add: initialStates_def )
      by (rule_tac x="C'" in exI, auto simp add: initialState_def)


    have "S_init\<in>initialStates program i"
      using step1 by (auto simp add: step_s.simps initialStates_def a_def initialState_def; blast)


    { 
      assume "0 < length tr"
      have "traceCorrect_s program tr"
      proof (rule show_traceCorrect_s_1[THEN conjunct1]) 
        show "S_init\<in>initialStates program i" using `S_init\<in>initialStates program i` .
        show "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S_fin" using steps' .
        show "\<And>S. S \<in> initialStates program i \<Longrightarrow> invariant_all S"
          using initialCorrect by blast

        show S_init_wf: "state_wellFormed S_init"
          using \<open>S_init \<in> initialStates program i\<close> initialStates_wellFormed by blast

        show "checkCorrect program S i" if " S \<in> initialStates program i" for S
          using `S \<in> initialStates program i` proof (rule check)
          show " invariant_all S"
            using initialCorrect `S \<in> initialStates program i` by blast
          show "state_wellFormed S"
          proof -
            from `S \<in> initialStates program i` obtain S_pre initState impl procName args tr
              where S_def: "S = S_pre\<lparr>localState := localState S_pre(i \<mapsto> initState), currentProc := currentProc S_pre(i \<mapsto> impl), visibleCalls := visibleCalls S_pre(i \<mapsto> {}),
                 invocationOp := invocationOp S_pre(i \<mapsto> (procName, args))\<rparr>"
                and "program = prog S_pre"
                and implproc: "procedure (prog S_pre) procName args \<triangleq> (initState, impl)"
                and uids: "uniqueIdsInList args \<subseteq> knownIds S_pre"
                and "invariant_all S_pre"
                and noInvOp: "invocationOp S_pre i = None"
                and steps_pre: "initialState (prog S_pre) ~~ tr \<leadsto>* S_pre" 
              apply (atomize_elim)
              apply (auto simp add: initialStates_def state_wellFormed_def)
              by blast

            have "S_pre ~~ (i, AInvoc procName args) \<leadsto> S"
              apply (auto simp add: step_simps S_def)
              apply (rule_tac x="initState" in exI)
              apply (rule_tac x="impl" in exI)
              apply auto
              using steps_pre noInvOp invocation_ops_if_localstate_nonempty apply blast
                apply (simp add: implproc)
              using uids apply auto[1]
              by (simp add: noInvOp)

            with steps_pre
            show "state_wellFormed S"
              using initialStates_wellFormed that by blast
          qed
        qed
        show "0 < length tr" using `0 < length tr` .
      qed
    } 
    moreover
    {
      assume "0 = length tr"
      have "traceCorrect_s program tr"
        using \<open>0 = length tr\<close> traceCorrect_s_def by force
    }
    ultimately have "traceCorrect_s program trace" 
      by (auto simp add: traceCorrect_s_def trace_def a_def \<open>invInitial\<close>, fastforce)
  }
  moreover 
  {
    assume "trace = []"
    hence "traceCorrect_s program trace" 
      by (simp add: traceCorrect_s_def)
  }
  ultimately
  show "traceCorrect_s program trace"
    using list.exhaust by blast
qed  



(* check program (with a given start-state, bound by a number of steps) *)
definition checkCorrect2F :: "(('localState, 'any) prog \<times> callId set \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool) 
                           \<Rightarrow> ('localState, 'any) prog \<times> callId set \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool" where
"checkCorrect2F \<equiv> (\<lambda>checkCorrect' (progr, VIS, txCalls, S, i).
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            checkCorrect' (progr, VIS, txCalls, (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>), i)
        | BeginAtomic ls \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S' vis vis' newTxns VIS'.
                transactionStatus S t = None
              \<and> invariant_all S'
              \<and> state_wellFormed S'
              \<and> state_monotonicGrowth S S'
              \<and> localState S' i \<triangleq> ls
              \<and> currentProc S' i \<triangleq> impl
              \<and> currentTransaction S' i \<triangleq> t
              \<and> transactionStatus S' t \<triangleq> Uncommited
              \<and> transactionOrigin S' t \<triangleq> i
              \<and> (\<forall>c. callOrigin S' c \<noteq> Some t)
              \<and> visibleCalls S i \<triangleq> vis
              \<and> vis' = (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')
              \<and> visibleCalls S' i \<triangleq> vis'
              \<and> newTxns \<subseteq> dom (transactionStatus S')
              \<and> consistentSnapshot S' vis'
              \<and> (\<forall>x. x \<noteq> t \<longrightarrow> transactionStatus S' x \<noteq> Some Uncommited)
              \<and> invariant progr (invContextVis S' vis')
              \<and> consistentSnapshot S' VIS'
              \<and> invariant progr (invContextVis S' VIS')
              \<longrightarrow> checkCorrect' (progr, VIS' , vis', S', i))
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                let S' = (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>) in
                  (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) 
                  \<and> (txCalls \<inter> VIS = {} \<or> txCalls \<subseteq> VIS \<and> the (visibleCalls S i) \<subseteq> VIS) (* ALL or nothing *)
                    (* split here: check VIS with new transaction and without *)
                    \<longrightarrow> (invariant progr (invContextVis S' VIS)
                         \<and> (invariant_all S' \<and> consistentSnapshot S' VIS \<and> invariant progr (invContextVis S' VIS)  \<longrightarrow> checkCorrect' (progr, VIS, {}, S', i))
                         \<and> (txCalls \<subseteq> VIS 
                            \<longrightarrow> (invariant progr (invContextVis S' (VIS \<union> txCalls) )
                                \<and> (invariant_all S' \<and> consistentSnapshot S' (VIS \<union> txCalls) \<and> invariant progr (invContextVis S' (VIS \<union> txCalls))  \<longrightarrow> checkCorrect' (progr, VIS \<union> txCalls, {}, S', i))
                       )))
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid.
            uid \<notin> generatedIds S
            \<longrightarrow> checkCorrect' (progr, VIS, txCalls, (S\<lparr>localState := (localState S)(i \<mapsto> ls uid), generatedIds := generatedIds S \<union> {uid} \<rparr>), i)
          )
        | DbOperation Op args ls \<Rightarrow> 
           (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                  (\<exists>res. querySpec progr Op args (getContext S i) res)
                  \<and>
                  (\<forall>c res vis. 
                      calls S c = None
                    \<and> querySpec progr Op args (getContext S i) res
                    \<and> visibleCalls S i \<triangleq> vis
                    \<longrightarrow> checkCorrect' (progr, VIS, insert c txCalls, (S\<lparr>
                          localState := (localState S)(i \<mapsto> ls res), 
                          calls := (calls S)(c \<mapsto> Call Op args res ),
                          callOrigin := (callOrigin S)(c \<mapsto> t),
                          visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                          happensBefore := updateHb (happensBefore S) vis [c]  \<rparr>), i)
                  )
           )
        | Return res \<Rightarrow> 
            currentTransaction S i = None
            \<and> (let S' = (S\<lparr>
                 localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>) in
               (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow> invariant progr (invContextVis S' VIS)  
            )
        )))
"

lemma checkCorrect2F_mono[simp]:
"mono checkCorrect2F"
proof (rule monoI)
  show "checkCorrect2F x \<le> checkCorrect2F y" if c0: "x \<le> y"  for  x :: "(('localState, 'any) prog \<times> callId set \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool)" and y
    apply (auto simp add: checkCorrect2F_def Let_def split: option.splits localAction.splits)
    using c0 apply fastforce
    using [[smt_solver=cvc4]]
       apply (smt le_boolD le_funD that wellFormed_currentTransactionUncommited)
    apply (smt le_boolD le_funD that)
        apply (smt le_boolD le_funD that)
    using le_funD that apply force
    using le_funD that apply force
    using le_funD that apply force
    using le_funD that apply force
    done

qed


definition checkCorrect2 :: "('localState, 'any) prog \<Rightarrow> callId set \<Rightarrow> callId set \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> bool" where
 "checkCorrect2 progr VIS txCalls S i \<equiv> lfp checkCorrect2F (progr, VIS, txCalls, S, i)"



schematic_goal checkCorrect2_simps:
  "checkCorrect2 progr VIS txCalls S i = ?F"
  apply (subst checkCorrect2_def)
  apply (subst lfp_unfold)
   apply simp
  apply (subst checkCorrect2F_def)
  apply (fold checkCorrect2_def)
  apply (rule refl)
  done

lemma consistentSnapshot_empty: "consistentSnapshot S {}"
  by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def)

lemma checkCorrect_eq2:
  assumes "invariant_all S" 
    and "state_wellFormed S"
    and "progr = prog S"
    and "visibleCalls S i \<triangleq> txCalls"
    and c2: "\<And>VIS. consistentSnapshot S VIS \<Longrightarrow> (checkCorrect2F ^^bound) bot (progr, VIS, txCalls, S, i) "
  shows "checkCorrect progr S i"
  using assms proof (induct bound arbitrary: S txCalls)
  case 0

  have "consistentSnapshot S {}"
    by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def)
  hence "(checkCorrect2F ^^0) bot (progr, {}, txCalls, S, i)"
    using `\<And>VIS. consistentSnapshot S VIS \<Longrightarrow> (checkCorrect2F ^^ 0) bot (progr, VIS, txCalls, S, i)` by blast
  hence False
    by auto

  then show ?case by simp

next
  case (Suc bound)

  have [simp]: "prog S = progr"
    by (simp add: Suc)


  have IH: "\<lbrakk>invariant_all S; 
      state_wellFormed S; 
      progr = prog S; 
      visibleCalls S i \<triangleq> txCalls;
     \<And>VIS. consistentSnapshot S VIS \<Longrightarrow>(checkCorrect2F ^^ bound) bot (progr, VIS, txCalls, S, i)\<rbrakk>
    \<Longrightarrow> checkCorrect progr S i" for S txCalls
    using Suc by blast


  have use_checkCorrect2: "consistentSnapshot S VIS \<Longrightarrow>(checkCorrect2F ^^ Suc bound) bot (progr, VIS, txCalls, S, i)" for VIS
    using Suc by blast

  show "checkCorrect progr S i"
  proof (cases "currentProc S i")
    case None
    then show ?thesis by (simp add: checkCorrect_simps)
  next
    case (Some proc)
    hence [simp]: "currentProc S i \<triangleq> proc" .

    obtain ls where ls_def[simp]: "localState S i \<triangleq> ls"
      using `state_wellFormed S` `visibleCalls S i \<triangleq> txCalls` state_wellFormed_ls_visibleCalls by fastforce

    show "checkCorrect progr S i"
    proof (cases "proc ls")
      case (LocalStep f)



      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: LocalStep)
        show "checkCorrect progr (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>) i"
        proof (rule IH)
          from `invariant_all S`
          show "invariant_all (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>)"
             by (auto simp add: invariant_all_def)

           have step: "S ~~ (i, ALocal) \<leadsto> S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>"
             using LocalStep Some ls_def step_simp_ALocal by blast

           with state_wellFormed_combine_step[OF `state_wellFormed S`, OF step]
           show "state_wellFormed (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>)" by simp

           show " progr = prog (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>)" by simp

           from `visibleCalls S i \<triangleq> txCalls`
           show "visibleCalls (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>) i \<triangleq> txCalls"
             by auto

           show "(checkCorrect2F ^^ bound) bot (progr, VIS, txCalls, S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>, i)"
             if cs: "consistentSnapshot (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>) VIS"
             for  VIS
           proof -

             from cs
             have "consistentSnapshot S VIS"
               by simp


             from use_checkCorrect2[OF `consistentSnapshot S VIS`]
             show "(checkCorrect2F ^^ bound) bot (progr, VIS, txCalls, S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>, i)"
               apply simp
               apply (subst(asm) checkCorrect2F_def)
               apply (auto simp add: LocalStep)
               done
           qed
         qed
       qed
    next
      case (BeginAtomic tx)
      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: BeginAtomic)
        have cs_empty: "consistentSnapshot S {}"
          by (simp add: consistentSnapshot_empty)


        show "currentTransaction S i = None"
          using use_checkCorrect2[OF cs_empty]
          apply simp
          apply (subst(asm) checkCorrect2F_def)
          apply (auto simp add: BeginAtomic)
          done

        show "checkCorrect progr S' i"
          if c0: "transactionStatus S t = None"
            and c1: "invariant_all S'"
            and c2: "state_wellFormed S'"
            and c3: "state_monotonicGrowth S S'"
            and c4: "localState S' i \<triangleq> tx"
            and c5: "currentProc S' i \<triangleq> proc"
            and c6: "currentTransaction S' i \<triangleq> t"
            and c7: "transactionOrigin S' t \<triangleq> i"
            and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
            and c9: "visibleCalls S i \<triangleq> vis"
            and c10: "visibleCalls S' i \<triangleq> (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')"
            and c11: "newTxns \<subseteq> dom (transactionStatus S')"
            and c12: "consistentSnapshot S' (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')"
            and c13: "\<forall>x. x \<noteq> t \<longrightarrow> transactionStatus S' x \<noteq> Some Uncommited"
          for  t S' vis newTxns
        proof (rule IH[OF c1 c2])

          show "progr = prog S'"
            using c3 state_monotonicGrowth_prog by force

          show "visibleCalls S' i \<triangleq> (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')"
            using Suc.prems(4) c10 c9 by auto

          

          
          show "(checkCorrect2F ^^ bound) bot (progr, VIS, txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S', S', i)"
            if cs: "consistentSnapshot S' VIS"
            for VIS
          proof -

            show "(checkCorrect2F ^^ bound) bot (progr, VIS, txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S', S', i)"
            using use_checkCorrect2[OF cs_empty]
               apply simp
               apply (subst(asm) checkCorrect2F_def)
            apply (auto simp add: BeginAtomic)
            apply (drule_tac x=t in spec)
            apply (drule_tac x=S' in spec)
            apply (drule_tac x=vis in spec)
            apply (drule_tac x=newTxns in spec)
            apply (drule_tac x=VIS in spec)
            apply (drule mp)
             apply (auto simp add: c0 c1 c10 c11 c12 c13 c2 c3 c4 c5 c6 c7 c8 c9 cs)
            using c2 c6 wellFormed_currentTransactionUncommited apply blast
            using \<open>progr = prog S'\<close> c1 c12 invariant_all_def apply blast
            using \<open>progr = prog S'\<close> c1 invariant_all_def that apply blast
            using \<open>visibleCalls S' i \<triangleq> (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')\<close> c10 by auto

        qed
      qed

    next
      case (EndAtomic x3)
      then show ?thesis sorry
    next
      case (NewId x4)
      then show ?thesis sorry
    next
      case (DbOperation x51 x52 x53)
      then show ?thesis sorry
    next
      case (Return x6)
      then show ?thesis sorry
    qed
  qed
qed



lemma checkCorrect_eq2:
  assumes "S\<in>initialStates progr i" 
    and c2: "\<And>VIS. consistentSnapshot S VIS \<Longrightarrow> (checkCorrect2F ^^bound) bot (progr, VIS, {}, S, i) "
  shows "checkCorrect progr S i"
proof -



  define P where "P \<equiv> \<lambda>S txCalls. visibleCalls S i \<triangleq> txCalls 
                       \<and> ((\<forall>VIS. consistentSnapshot S VIS \<longrightarrow> checkCorrect2 progr VIS txCalls S i) \<longleftrightarrow> checkCorrect progr S i)"

  thm lfp_ordinal_induct

  find_theorems "mono checkCorrectF"


  thm lfp_ordinal_induct[OF checkCorrectF_mono]
from assms
  have "lfp checkCorrectF (progr, S, i)"
  proof (induct rule: lfp_ordinal_induct[OF checkCorrectF_mono])
    show "mono checkCorrectF"

oops

qed

       

end