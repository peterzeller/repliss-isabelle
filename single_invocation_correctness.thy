theory single_invocation_correctness
  imports approach execution_invariants_s fixedpoints
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

(* TODO remove? *)
abbreviation invariant_all' :: "('localState, 'any) state \<Rightarrow> bool" where
"invariant_all' state \<equiv>  invariant (prog state) (invContext' state)"



(* check program (with a given start-state, bound by a number of steps) *)
definition checkCorrectF :: "(('localState, 'any::valueType) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool) 
                           \<Rightarrow> ('localState, 'any) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool" where
"checkCorrectF \<equiv> (\<lambda>checkCorrect' (progr, S, i).
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            checkCorrect' (progr, (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>), i)
        | BeginAtomic ls' \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S' vis newTxns S'' vis' ls.
               localState S i \<triangleq> ls
              \<and> currentTransaction S i = None
              \<and> transactionStatus S t = None
              \<and> prog S' = prog S
              \<and> invariant_all' S'
              \<and> (\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited)
              \<and> state_wellFormed S'
              \<and> state_wellFormed S''
              \<and> state_monotonicGrowth i S S'
              \<and> (\<forall>t. transactionOrigin S' t \<triangleq> i \<longleftrightarrow> transactionOrigin S t \<triangleq> i)
              \<and> localState S' i \<triangleq> ls
              \<and> currentProc S' i \<triangleq> impl
              \<and> currentTransaction S' i = None
              \<and> visibleCalls S i \<triangleq> vis
              \<and> visibleCalls S' i \<triangleq> vis
              \<and> vis' = (vis \<union> callsInTransaction S' newTxns \<down> happensBefore S')
              \<and> newTxns \<subseteq> dom (transactionStatus S')
              \<and> consistentSnapshot S' vis'
              \<and> transactionStatus S' t = None
              \<and> (\<forall>c. callOrigin S' c \<noteq> Some t)
              \<and> transactionOrigin S' t = None
              \<and> (S'' = S'\<lparr>transactionStatus := (transactionStatus S')(t \<mapsto> Uncommited),
                          transactionOrigin := (transactionOrigin S')(t \<mapsto> i),
                          currentTransaction := (currentTransaction S')(i \<mapsto> t),
                          localState := (localState S')(i \<mapsto> ls'),
                          visibleCalls := (visibleCalls S')(i \<mapsto> vis')
                \<rparr>)
              \<longrightarrow> checkCorrect' (progr, S'' , i))
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                let S' = (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>) in
                  (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) 
                  \<and> state_wellFormed S'
                    \<longrightarrow> (invariant_all' S'
                         \<and> (invariant_all' S' \<longrightarrow> checkCorrect' (progr, S', i)))
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid ls'.
            generatedIds S uid = None
           \<and> ls uid \<triangleq> ls'
           \<and> uniqueIds uid = {uid}
            \<longrightarrow> checkCorrect' (progr, (S\<lparr>localState := (localState S)(i \<mapsto> ls'), generatedIds := (generatedIds S)(uid \<mapsto> i) \<rparr>), i)
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
               (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow> invariant_all' S'    
            )
        )))
"



lemma checkCorrectF_mono[simp]:
"mono checkCorrectF"
proof (rule monoI)
  show "checkCorrectF x \<le> checkCorrectF y" if c0: "x \<le> y"  for  x :: "(('localState, 'any::valueType) prog \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool)" and y
    by (auto simp add: checkCorrectF_def Let_def intro: predicate1D[OF `x \<le> y`] split: option.splits localAction.splits)

qed


definition checkCorrect :: "('localState, 'any::valueType) prog \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> bool" where
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
  case (step tr S' a S'')
  hence i1: "invocationOp S i \<triangleq> info" and  i2: "invocationOp S' i \<triangleq> info"
    by auto

  from `S' ~~ (i, a) \<leadsto>\<^sub>S S''`
  show ?case
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )

  next
    case (newId C s ls f ls' uid)
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (beginAtomic C s ls f ls' t C' C'' vis vis' newTxns txns)
    thus ?case using i2 state_monotonicGrowth_invocationOp[OF `state_monotonicGrowth s C C'`]
      by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (endAtomic C s ls f ls' t C' valid)
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (dbop C s ls f Op args ls' t c res vis)
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (invocation C s procName args initState impl C' C'' valid)
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (return C s ls f res C' valid)
    thus ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  qed

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
  by (meson state_monotonicGrowth_invocationOp wf_s_localState_to_invocationOp2)



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
    using `i' \<noteq> i` apply (auto simp add: step_s.simps `currentTransaction S i' = None`)
    by (meson option.exhaust wellFormed_currentTransaction_unique_h(2))+
qed

lemma state_wellFormed_combine1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto> S'"
  and "a\<noteq>AFail"
shows "state_wellFormed S'"
  using `state_wellFormed S` proof (rule state_wellFormed_combine)
  from `S ~~ (i, a) \<leadsto> S'`
  show "S ~~ [(i,a)] \<leadsto>* S'"
    by simp
  show "\<And>ia. (ia, AFail) \<notin> set [(i, a)]"
    using `a\<noteq>AFail` by simp
qed

lemma state_wellFormed_combine_s1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto>\<^sub>S S'"
shows "state_wellFormed S'"
proof -

from `S ~~ (i, a) \<leadsto>\<^sub>S S'` 
  show "state_wellFormed S'"
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    hence "S ~~ (i, ALocal) \<leadsto> S'"
      by (auto simp add: step.simps)
    with `state_wellFormed S` show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (newId C s ls f ls' uid)
    hence "S ~~ (i, ANewId uid) \<leadsto> S'"
      by (auto simp add: step.simps)
    with `state_wellFormed S` show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (beginAtomic C s ls f ls' t C' vis vis' newTxns txns)
    then show ?case 
      by blast
  next
    case (endAtomic C s ls f ls' t C' valid)
    hence "S ~~ (i, AEndAtomic) \<leadsto> S'"
      by (auto simp add: step.simps)
    with `state_wellFormed S` show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (dbop C s ls f Op args ls' t c res vis)
    hence "S ~~ (i, ADbOp c Op args res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with `state_wellFormed S` show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (invocation C s procName args initState impl C' C'' valid)
    hence "C' ~~ (i, AInvoc procName args) \<leadsto> C''"
      apply (auto simp add: step.simps)
      using wf_localState_to_invocationOp by blast+

    then show ?case
      using `state_wellFormed C'` `S' = C''` state_wellFormed_combine1 by blast
  next
    case (return C s ls f res C' valid)
    hence "S ~~ (i, AReturn res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with `state_wellFormed S` show ?case 
      by (rule state_wellFormed_combine1, simp)
  qed
qed

lemma committedCalls_allCommitted:
  assumes wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. transactionStatus S t \<noteq> Some Uncommited"
  shows "commitedCalls S = dom (calls S)"
  apply (auto simp add: commitedCallsH_def isCommittedH_def )
   apply (simp add: domD domIff local.wf wellFormed_callOrigin_dom3)
  apply (case_tac "callOrigin S x", auto)
  apply (metis local.wf option.distinct(1) wellFormed_callOrigin_dom3)
  by (metis (full_types) domD domIff local.wf noUncommitted transactionStatus.exhaust wellFormed_state_callOrigin_transactionStatus)

lemma invContextH_same_allCommitted':
  assumes  wf1: "\<And>c. (state_calls c = None) \<longleftrightarrow> (state_callOrigin c = None)"
    and wf2: "\<And>c tx. state_callOrigin c \<triangleq> tx \<Longrightarrow> state_transactionStatus tx \<noteq> None"
    and wf3: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls a \<noteq> None"
    and wf4: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls b \<noteq> None"
    and wf5: "\<And>c. (state_transactionOrigin c = None) \<longleftrightarrow> (state_transactionStatus c = None)"
    and noUncommitted: "\<And>t c. \<lbrakk>state_transactionStatus t \<triangleq> Uncommited\<rbrakk> \<Longrightarrow> state_callOrigin c \<noteq> Some t"
  shows "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes
       = invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes"
  apply (auto simp add: invContextH_def invContextH2_def intro!: ext)
      apply (auto simp add: commitedCallsH_def isCommittedH_def restrict_map_def restrict_relation_def)
      apply (metis (full_types) noUncommitted not_None_eq transactionStatus.exhaust wf1 wf2)
     apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf3)
    apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf4)
   apply (metis (full_types) noUncommitted option.exhaust_sel transactionStatus.exhaust wf2)
(* does not work, because now I have transaction origin leaked *)
  oops


lemma invContextH_same_allCommitted:
  assumes  wf1: "\<And>c. (state_calls c = None) \<longleftrightarrow> (state_callOrigin c = None)"
    and wf2: "\<And>c tx. state_callOrigin c \<triangleq> tx \<Longrightarrow> state_transactionStatus tx \<noteq> None"
    and wf3: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls a \<noteq> None"
    and wf4: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls b \<noteq> None"
    and wf5: "\<And>c. (state_transactionOrigin c = None) \<longleftrightarrow> (state_transactionStatus c = None)"
    and noUncommitted: "\<And>t. state_transactionStatus t \<noteq> Some Uncommited"
  shows "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes
       = invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes"
  apply (auto simp add: invContextH_def invContextH2_def intro!: ext)
      apply (auto simp add: commitedCallsH_def isCommittedH_def restrict_map_def restrict_relation_def)
      apply (metis (full_types) noUncommitted option.exhaust_sel transactionStatus.exhaust wf1 wf2)
     apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf3)
    apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf4)
   apply (metis (full_types) noUncommitted option.exhaust_sel transactionStatus.exhaust wf2)
  by (metis noUncommitted option.exhaust_sel transactionStatus.exhaust wf5)

lemma invContext_same_allCommitted:
  assumes  wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. transactionStatus S t \<noteq> Some Uncommited"
  shows "invContext S
       = invContext' S"
proof (rule invContextH_same_allCommitted)
  show "\<And>c. (calls S c = None) = (callOrigin S c = None)"
  using local.wf wellFormed_callOrigin_dom3 by blast
    show "\<And>c tx. callOrigin S c \<triangleq> tx \<Longrightarrow> transactionStatus S tx \<noteq> None"
      by (simp add: local.wf wellFormed_state_callOrigin_transactionStatus)
   show "\<And>a b. (a, b) \<in> happensBefore S \<Longrightarrow> calls S a \<noteq> None"
     by (simp add: local.wf wellFormed_happensBefore_calls_l)
   show "\<And>a b. (a, b) \<in> happensBefore S \<Longrightarrow> calls S b \<noteq> None"
     by (simp add: local.wf wellFormed_happensBefore_calls_r)
   show "\<And>c. (transactionOrigin S c = None) = (transactionStatus S c = None)"
     by (simp add: local.wf wf_transaction_status_iff_origin)
   show "\<And>t. transactionStatus S t \<noteq> Some Uncommited"
     using noUncommitted by blast
 qed


lemma wf_localState_currentProc:
  assumes "state_wellFormed S"
  shows "localState S i = None \<longleftrightarrow> currentProc S i = None"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  then show ?case 
    by (auto simp add: step.simps split: if_splits)
qed

lemma checkCorrect_end: 
  assumes "state_wellFormed S"
and "localState S i = None"
shows "checkCorrect program S i"
  using assms checkCorrect_noProc wf_localState_currentProc by blast



lemma show_traceCorrect_s_1:
  assumes initialCorrect: "\<And>S. S\<in>initialStates program i \<Longrightarrow> invariant_all' S "
    and check: "\<And>S. S\<in>initialStates program i \<Longrightarrow> checkCorrect program S i"
    and steps: "initS ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and initS: "initS \<in> initialStates program i"
    and trace_len2: "0 < length trace"
    and initS_wf: "state_wellFormed initS"
  shows "traceCorrect_s program trace \<and> checkCorrect program S_fin i \<and> state_wellFormed S_fin"
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

      

    have "traceCorrect_s program tr \<and> checkCorrect program S_pre i \<and> state_wellFormed S_pre"
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
      and S_pre_wf: "state_wellFormed S_pre"
      using \<open>traceCorrect_s program tr \<and> checkCorrect program S_pre i \<and> state_wellFormed S_pre\<close> by blast+

    have "state_wellFormed S_fin"
      using S_pre_wf state_wellFormed_combine_s1 step_final by blast

    show "traceCorrect_s program trace \<and> checkCorrect program S_fin i  \<and> state_wellFormed S_fin"
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
        using `state_wellFormed S_fin` invContext_same_allCommitted[OF `state_wellFormed S_fin`]
        by (auto simp add: tx1 step_s.simps Let_def hasInvocation onlyOneTx split: option.splits if_splits)
        


      from S_pre_correct step_final
      have cc: "checkCorrect program S_fin i" 
        apply (subst (asm) checkCorrect_simps)
        using \<open>state_wellFormed S_fin\<close> apply (auto simp add: step_s.simps Let_def hasInvocation \<open>a_inv = True\<close> tx1 split: option.splits if_splits)
        using onlyOneTx tx1 apply auto[1]
        apply (drule_tac x=c in spec)
        apply auto
        by (simp add: updateHb_single)



      from tr_correct `a_inv = True`
      have "traceCorrect_s program trace"
        by (auto simp add: traceCorrect_s_def tr_def)

      with cc
      show ?thesis
        by (simp add: \<open>state_wellFormed S_fin\<close>) 
    next
      case None
      hence notx[simp]: "currentTransaction S_pre i = None" by simp

      have onlyOneTx: "transactionStatus S_pre t \<noteq> Some Uncommited" for t
        using None initS initialStates_wf state_wellFormed_s_currentTransactions_iff_uncommitted steps_pre by fastforce



      have invContextSimp: "invContext S_fin = invContext' S_fin" if "\<And>t. transactionStatus S_fin t \<noteq> Some Uncommited"
        by (simp add: \<open>state_wellFormed S_fin\<close> invContext_same_allCommitted that) 


      from S_pre_correct tr_correct step_final  
      have "a_inv = True" (*and "checkCorrect program S_fin i (bound - length trace)" *)
        apply (subst(asm) checkCorrect_simps)
        using \<open>state_wellFormed S_fin\<close> invContextSimp apply (auto simp add: onlyOneTx step_s.simps Let_def hasInvocation invContextSimp None split: option.splits if_splits)
        apply (subst(asm) invContextH_same_allCommitted)
         apply (auto simp add: wellFormed_callOrigin_dom3[OF S_pre_wf])
        using wf_no_transactionStatus_origin_for_nothing[OF S_pre_wf]  apply auto[1]
        using wellFormed_happensBefore_calls_l[OF S_pre_wf] wellFormed_happensBefore_calls_r[OF S_pre_wf]
          wf_no_transactionStatus_origin_for_nothing[OF S_pre_wf]
          wellFormed_callOrigin_dom3[OF S_pre_wf]
          wellFormed_state_callOrigin_transactionStatus[OF S_pre_wf]
           wf_transaction_status_iff_origin[OF S_pre_wf]
          onlyOneTx
        by auto
        





      have invAll': "invariant_all' S_fin" if "invariant_all S_fin" and "\<And>t. transactionStatus S_fin t \<noteq> Some Uncommited"
        using that by (simp add: invContextSimp) 

      from step_final
      have cc: "checkCorrect program S_fin i" 
      proof (induct rule: step_s.cases)
        case (local C s ls f ls')
        thus ?case
          apply (insert S_pre_correct)
          apply (subst(asm) checkCorrect_simps)
          using local by (auto simp add:  split: option.splits localAction.splits)

      next
        case (newId C s ls f ls' uid)
        thus ?case
          apply (insert S_pre_correct)
          apply (subst(asm) checkCorrect_simps)
          using newId by (auto simp add:  split: option.splits localAction.splits)
      next
        case (beginAtomic C i' ls f ls' t C' C'' vis vis' newTxns txns)


        hence [simp]: "i' = i"
          by blast 


        from S_pre_correct
        have S_pre_correct': "(\<forall>t S' vis newTxns S'' vis' ls.
                  localState C i \<triangleq> ls \<and>
                  currentTransaction C i = None \<and>
                  transactionStatus C t = None \<and>
                  prog S' = prog C \<and>
                  invariant_all' S' \<and>
                  (\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited) \<and>
                  state_wellFormed S' \<and>
                  state_wellFormed S'' \<and>
                  state_monotonicGrowth i C S' \<and>
                  (\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin C t \<triangleq> i) \<and>
                  localState S' i \<triangleq> ls \<and>
                  currentProc S' i \<triangleq> f \<and>
                  currentTransaction S' i = None \<and>
                  visibleCalls C i \<triangleq> vis \<and>
                  visibleCalls S' i \<triangleq> vis \<and>
                  vis' = vis \<union> callsInTransaction S' newTxns \<down> happensBefore S' \<and>
                  newTxns \<subseteq> dom (transactionStatus S') \<and>
                  consistentSnapshot S' vis' \<and>
                  transactionStatus S' t = None \<and>
                  (\<forall>c. callOrigin S' c \<noteq> Some t) \<and>
                  transactionOrigin S' t = None \<and>
                  S'' = S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'(t \<mapsto> i),
                             currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> ls'), visibleCalls := visibleCalls S'(i \<mapsto> vis')\<rparr> \<longrightarrow>
                  checkCorrect program S'' i)"
          apply (subst(asm) checkCorrect_simps)
          by (auto simp add: beginAtomic[simplified]  split: option.splits localAction.splits)

        show ?case
        proof (rule S_pre_correct'[rule_format], intro conjI)
          show "transactionStatus C t = None" using `transactionStatus C t = None` .

          show "invariant_all' C'"
            using `invariant_all C'` `\<And>tx. transactionStatus C' tx \<noteq> Some Uncommited` `state_wellFormed C'` invContext_same_allCommitted by fastforce 
          show "state_wellFormed C'"  
            by (simp add: `state_wellFormed C'`)
          show "state_monotonicGrowth i C C'"
            using \<open>i' = i\<close> beginAtomic.hyps(10) by blast
          show "localState C' i \<triangleq> ls"
            using `localState C' i' \<triangleq> ls` by auto
          show "currentProc C' i \<triangleq> f"
            using True beginAtomic.hyps by blast 
          show "currentTransaction C' i = None"  
            using True beginAtomic.hyps by blast
          show "transactionStatus C' t = None"  
            using beginAtomic.hyps(24) by blast
          show "transactionOrigin C' t = None"  
            using beginAtomic.hyps(26) by auto
          show " \<forall>c. callOrigin C' c \<noteq> Some t"  
            by (simp add: beginAtomic.hyps(25))
          show "prog C' = prog C"
            by (simp add: beginAtomic.hyps(9))

          show " \<forall>tx. transactionStatus C' tx \<noteq> Some Uncommited"
            by (simp add: beginAtomic.hyps(13))

          show "visibleCalls C' i \<triangleq> vis"
            using True beginAtomic.hyps by blast

          show "localState C i \<triangleq> ls"
            using True beginAtomic.hyps by blast

          show "currentTransaction C i = None"
            using beginAtomic.hyps(7) by auto

          show "state_wellFormed S_fin"
            by (simp add: \<open>state_wellFormed S_fin\<close>)

          show "visibleCalls C i \<triangleq> vis"
            using beginAtomic.hyps(19) by auto

          show "newTxns \<subseteq> dom (transactionStatus C')"
            by (simp add: beginAtomic.hyps(22))

          show "vis' = vis \<union> callsInTransaction C' newTxns \<down> happensBefore C'"
            using beginAtomic.hyps(21) by auto

          show "consistentSnapshot C' vis'"
            by (simp add: beginAtomic.hyps(23))

          show "\<forall>t. transactionOrigin C' t \<triangleq> i = transactionOrigin C t \<triangleq> i"
            using beginAtomic.hyps(11) by auto

          show "S_fin = C'
              \<lparr>transactionStatus := transactionStatus C'(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin C'(t \<mapsto> i), currentTransaction := currentTransaction C'(i \<mapsto> t),
                 localState := localState C'(i \<mapsto> ls'), visibleCalls := visibleCalls C'(i \<mapsto> vis')\<rparr>"  
            by (auto simp add: beginAtomic(3) beginAtomic(27) state_ext)
        qed
      next
        case (endAtomic C s ls f ls' t C' valid)
        thus ?case
          apply (insert S_pre_correct)
          apply (subst(asm) checkCorrect_simps)
          using endAtomic notx by (auto simp add: Let_def  split: option.splits localAction.splits if_splits)
      next
        case (dbop C s ls f Op args ls' t c res vis)
        thus ?case
          apply (insert S_pre_correct)
          apply (subst(asm) checkCorrect_simps)
          using dbop notx by (auto simp add:  split: option.splits localAction.splits)
      next
        case (invocation C s procName args initState impl C' C'' valid)
        thus ?case
          apply (insert S_pre_correct)
          apply (subst(asm) checkCorrect_simps)
          using invocation notx hasInvocation by (auto simp add:  split: option.splits localAction.splits)
      next
        case (return C s ls f res C' valid)

        show ?case
        proof (rule checkCorrect_end)
          show " state_wellFormed S_fin"
            by (simp add: \<open>state_wellFormed S_fin\<close>)
          show "localState S_fin i = None"
            using return by auto
        qed

      qed



      from tr_correct `a_inv = True`
      have "traceCorrect_s program trace"
        by (auto simp add: traceCorrect_s_def tr_def)



      show "traceCorrect_s program trace \<and> checkCorrect program S_fin i  \<and> state_wellFormed S_fin "
        by (simp add: \<open>traceCorrect_s program trace\<close> cc `state_wellFormed S_fin`)
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
        using initS initialState_noTxns1 apply blast
        apply (subst(asm) invContextH_same_allCommitted)
        using wellFormed_callOrigin_dom3[OF initS_wf]
              wellFormed_state_callOrigin_transactionStatus[OF initS_wf]
              initialState_noTxns1[OF initS]
              wellFormed_happensBefore_calls_r[OF initS_wf]
              wellFormed_happensBefore_calls_l[OF initS_wf]
              wf_no_transactionStatus_origin_for_nothing[OF initS_wf]
              wf_transaction_status_iff_origin[OF initS_wf]
              by blast+
    qed


    hence "traceCorrect_s program trace"
      by (auto simp add: tr_def traceCorrect_s_def)   

    have " state_wellFormed S_fin"
      using \<open>initS ~~ (i, a) \<leadsto>\<^sub>S S_fin\<close> initS_wf state_wellFormed_combine_s1 by blast



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
      case (beginAtomic ls f ls' t S' vis vis' txns newTxns )

      have "transactionStatus S_fin t \<triangleq> Uncommited"
        by (simp add: beginAtomic)

      find_theorems S_pre

      have "checkCorrect program S_pre i"
        using \<open>S_pre = initS\<close> initS_correct by blast

      have "currentTransaction initS i = None"
        by (simp add: noTransaction)



      from initS_correct
      have initS_correct2:
        "(\<forall>t S' vis newTxns S'' vis' ls.
                  localState initS i \<triangleq> ls \<and>
                  currentTransaction initS i = None \<and>
                  transactionStatus initS t = None \<and>
                  prog S' = prog initS \<and>
                  invariant_all' S' \<and>
                  (\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited) \<and>
                  state_wellFormed S' \<and>
                  state_wellFormed S'' \<and>
                  state_monotonicGrowth i initS S' \<and>
                  (\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin initS t \<triangleq> i) \<and>
                  localState S' i \<triangleq> ls \<and>
                  currentProc S' i \<triangleq> f \<and>
                  currentTransaction S' i = None \<and>
                  visibleCalls initS i \<triangleq> vis \<and>
                  visibleCalls S' i \<triangleq> vis \<and>
                  vis' = vis \<union> callsInTransaction S' newTxns \<down> happensBefore S' \<and>
                  newTxns \<subseteq> dom (transactionStatus S') \<and>
                  consistentSnapshot S' vis' \<and>
                  transactionStatus S' t = None \<and>
                  (\<forall>c. callOrigin S' c \<noteq> Some t) \<and>
                  transactionOrigin S' t = None \<and>
                  S'' = S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'(t \<mapsto> i),
                             currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> ls'), visibleCalls := visibleCalls S'(i \<mapsto> vis')\<rparr> \<longrightarrow>
                  checkCorrect program S'' i)"
        apply (subst(asm) checkCorrect_simps)
        using `currentProc S_pre i \<triangleq> f` `f ls = BeginAtomic ls'` `localState S_pre i \<triangleq> ls` by auto

      thm  initS_correct2[rule_format]

      show ?thesis
      proof (rule initS_correct2[rule_format], intro conjI; (solves\<open> simp add:  beginAtomic[simplified]\<close>)?)

        show "state_wellFormed S_fin" 
          using beginAtomic by simp

        show "invariant_all' S'"
          using invContext_same_allCommitted local.beginAtomic(12) local.beginAtomic(10) local.beginAtomic(11) by fastforce 


        show "txns \<subseteq> dom (transactionStatus S')"
          using beginAtomic by simp

        show "consistentSnapshot S' (vis \<union> callsInTransaction S' txns \<down> happensBefore S')"
          using beginAtomic   by simp
      qed


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
      by (auto simp add: checkCorrect_simps `state_wellFormed S_fin`)
  qed
qed


lemma "\<lbrakk>\<not>P; P\<rbrakk> \<Longrightarrow> False"
  by simp



term "\<lparr>
calls = ???,
happensBefore = ???,
  prog = ???,
  callOrigin  = ???,
  transactionOrigin  = ???,
  generatedIds  = ???,
  knownIds  = ???,
  invocationOp  =???,
  invocationRes =???,
  transactionStatus  =???,
  localState  =???,
  currentProc  =???,
  visibleCalls  =???,
  currentTransaction  = ???
 \<rparr> :: (int, int) state"

lemma show_exists_state:
  fixes P :: "('ls,'any) state \<Rightarrow> bool"
  assumes "\<exists>calls happensBefore prog callOrigin transactionOrigin
   generatedIds knownIds invocationOp invocationRes transactionStatus
localState currentProc visibleCalls currentTransaction. P \<lparr>
  calls = calls,
  happensBefore = happensBefore,
  prog = prog,
  callOrigin  = callOrigin,
  transactionOrigin  = transactionOrigin,
  generatedIds  = generatedIds,
  knownIds  = knownIds,
  invocationOp  =invocationOp,
  invocationRes =invocationRes,
  transactionStatus  =transactionStatus,
  localState  =localState,
  currentProc  =currentProc,
  visibleCalls  =visibleCalls,
  currentTransaction  = currentTransaction
 \<rparr>"
  shows "\<exists>S. P S"
  using assms by auto

lemma exists_narrowL1: "(\<exists>x. P x \<and> Q) \<longleftrightarrow> (\<exists>x. P x) \<and> Q" 
  by auto

lemma exists_narrowL2: "(\<exists>x y. P x y \<and> Q y) \<longleftrightarrow> (\<exists>y. (\<exists>x. P x y) \<and> Q y)" 
  by auto

lemma exists_narrowL3: "(\<exists>x y1 y2. P x y1 y2 \<and> Q y1 y2) \<longleftrightarrow> (\<exists>y1 y2. (\<exists>x. P x y1 y2) \<and> Q y1 y2)" 
  by auto

lemma exists_narrowL4: "(\<exists>x y1 y2 y3. P x y1 y2 y3 \<and> Q y1 y2 y3) \<longleftrightarrow> (\<exists>y1 y2 y3. (\<exists>x. P x y1 y2 y3) \<and> Q y1 y2 y3)" 
  by auto

lemma exists_narrowR1: "(\<exists>x. P \<and> Q x) \<longleftrightarrow> P \<and> (\<exists>x. Q x)" 
  by auto

lemma exists_narrowR2: "(\<exists>x y. P y \<and> Q x y) \<longleftrightarrow> (\<exists>y. P  y \<and> (\<exists>x. Q x y))" 
  by auto

lemma exists_narrowR3: "(\<exists>x y1 y2. P y1 y2 \<and> Q x y1 y2) \<longleftrightarrow> (\<exists>y1 y2. P y1 y2 \<and> (\<exists>x. Q x y1 y2))" 
  by auto

lemma exists_narrowR4: "(\<exists>x y1 y2 y3. P y1 y2 y3 \<and> Q x y1 y2 y3) \<longleftrightarrow> (\<exists>y1 y2 y3. P y1 y2 y3 \<and> (\<exists>x. Q x y1 y2 y3))" 
  by auto

lemmas exists_narrow = 
exists_narrowL1 
exists_narrowL2
exists_narrowL3
exists_narrowL4
exists_narrowR1
exists_narrowR2
exists_narrowR3
exists_narrowR4

lemma prog_initial[simp]: "prog (initialState program) = program"
  by (auto simp add: initialState_def)

lemma show_program_correct_single_invocation:
  assumes initialCorrect: "\<And>S i. S\<in>initialStates program i \<Longrightarrow> invariant_all' S "
    and check: "\<And>S i. \<lbrakk>S\<in>initialStates program i; invariant_all' S; state_wellFormed S\<rbrakk> \<Longrightarrow> checkCorrect program S i"
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

    have invContext_same: "invContext S = invContext' S"  if  "S \<in> initialStates program i"  for S
      using initialState_noTxns1 initialStates_wellFormed invContext_same_allCommitted that by blast


    from initialCorrect[where i=i]
    have initialCorrect': "invariant progr (invContext S)" if "S \<in> initialStates program i" and "progr = prog S" for S progr
      using that invContext_same by fastforce 


    have "invariant_all' S_init"
    proof (rule initialCorrect[where i=i])
      show "S_init \<in> initialStates program i"
        using step1 and a_def apply (auto simp add: step_s.simps initialStates_def )
         apply (auto simp add: state_ext)
        by blast+

(*
        using [[smt_solver = cvc4]]
         apply (smt distributed_state.select_convs(1) initialState_def old.unit.exhaust state.surjective)
        by (smt distributed_state.select_convs(1) initialState_def old.unit.exhaust state.surjective)*)
    qed

    with step1 and a_def
    have "invInitial"
      apply (auto simp add: step_s.simps )
      using [[smt_solver=cvc4]]
      by (smt invContextH_same_allCommitted wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l wellFormed_happensBefore_calls_r wellFormed_state_callOrigin_transactionStatus wf_transaction_status_iff_origin)



    have "S_init\<in>initialStates program i"
      using step1 by (auto simp add: step_s.simps initialStates_def a_def initialState_def; blast)


    { 
      assume "0 < length tr"
      have "traceCorrect_s program tr"
      proof (rule show_traceCorrect_s_1[THEN conjunct1]) 
        show "S_init\<in>initialStates program i" using `S_init\<in>initialStates program i` .
        show "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S_fin" using steps' .
        show "\<And>S. S \<in> initialStates program i \<Longrightarrow> invariant_all' S"
          using initialCorrect by blast

        show S_init_wf: "state_wellFormed S_init"
          using \<open>S_init \<in> initialStates program i\<close> initialStates_wellFormed by blast

        show "checkCorrect program S i" if " S \<in> initialStates program i" for S
          using `S \<in> initialStates program i` proof (rule check)
          show " invariant_all' S"
            using initialCorrect `S \<in> initialStates program i` by blast
          show "state_wellFormed S"
          proof -
            from `S \<in> initialStates program i` obtain S_pre initState impl procName args tr
              where S_def: "S = S_pre\<lparr>localState := localState S_pre(i \<mapsto> initState), currentProc := currentProc S_pre(i \<mapsto> impl), visibleCalls := visibleCalls S_pre(i \<mapsto> {}),
                 invocationOp := invocationOp S_pre(i \<mapsto> (procName, args))\<rparr>"
                and "program = prog S_pre"
                and implproc: "procedure (prog S_pre) procName args \<triangleq> (initState, impl)"
                and uids: "uniqueIdsInList args \<subseteq> knownIds S_pre"
                and "invariant_all' S_pre"
                and noInvOp: "invocationOp S_pre i = None"
                and steps_pre: "initialState (prog S_pre) ~~ tr \<leadsto>* S_pre" 
              apply (atomize_elim)
              apply (auto simp add: initialStates_def state_wellFormed_def)
              by (metis invContext_same_allCommitted state_wellFormed_def)

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

(*
TODO continue here: remove VIS set -- we will later provide lemmas for 
showing that a snapshot is consistent
*)


definition Def (infix "::=" 50) where
"x ::= y \<equiv> x = y"

definition DefSome (infix "::\<triangleq>" 50) where
"x ::\<triangleq> y \<equiv> y = Some x"

(* check program (with a given start-state, bound by a number of steps) *)
definition checkCorrect2F :: "(('localState, 'any::valueType) prog \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool) 
                           \<Rightarrow> ('localState, 'any) prog \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool" where
"checkCorrect2F \<equiv> (\<lambda>checkCorrect' (progr, txCalls, S, i).
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            (\<forall>S'. S' ::= (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>)
             \<longrightarrow> checkCorrect' (progr, txCalls, S', i))
        | BeginAtomic ls' \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S' newTxns S'' vis' ls.
               localState S i \<triangleq> ls
              \<and> currentTransaction S i = None
              \<and> transactionStatus S t = None
              \<and> prog S' = prog S
              \<and> invariant_all' S'
              \<and> (\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited)
              \<and> state_wellFormed S'
              \<and> state_wellFormed S''
              \<and> state_monotonicGrowth i S S'
               (* transactions in current invocation unchanged:  *)
              \<and> (\<forall>t . transactionOrigin S t \<triangleq> i \<longleftrightarrow> transactionOrigin S' t \<triangleq> i)
              \<and> localState S' i \<triangleq> ls
              \<and> currentProc S' i \<triangleq> impl
              \<and> currentTransaction S' i = None
              \<and> visibleCalls S i \<triangleq> txCalls
              \<and> visibleCalls S' i \<triangleq> txCalls
              \<and> vis' ::= (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')
              \<and> newTxns \<subseteq> dom (transactionStatus S')
              \<and> consistentSnapshot S' vis'
              \<and> transactionStatus S' t = None
              \<and> (\<forall>c. callOrigin S' c \<noteq> Some t)
              \<and> transactionOrigin S' t = None
              \<and> (S'' ::= S'\<lparr>transactionStatus := (transactionStatus S')(t \<mapsto> Uncommited),
                          transactionOrigin := (transactionOrigin S')(t \<mapsto> i),
                          currentTransaction := (currentTransaction S')(i \<mapsto> t),
                          localState := (localState S')(i \<mapsto> ls'),
                          visibleCalls := (visibleCalls S')(i \<mapsto> vis')
                \<rparr>)
              \<longrightarrow> checkCorrect' (progr, vis', S'' , i))
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                (\<forall>S'.
                 S' ::= (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>)
                \<longrightarrow> (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) 
                     \<longrightarrow> (invariant progr (invContext' S')
                          \<and> (invariant progr (invContext' S')  \<longrightarrow> checkCorrect' (progr, txCalls, S', i))
                        ))
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid S' ls'.
            generatedIds S uid = None
           \<and> ls uid \<triangleq> ls'
           \<and> uniqueIds uid = {uid}
           \<and> S' ::= (S\<lparr>localState := (localState S)(i \<mapsto> ls'), generatedIds := (generatedIds S)(uid \<mapsto> i) \<rparr>)
            \<longrightarrow> checkCorrect' (progr, txCalls, S', i)
          )
        | DbOperation Op args ls \<Rightarrow> 
           (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                  (\<exists>res. querySpec progr Op args (getContext S i) res)
                  \<and>
                  (\<forall>c res S' vis' hb'. 
                      calls S c = None
                    \<and> querySpec progr Op args (getContext S i) res
                    \<and> visibleCalls S i \<triangleq> txCalls
                    \<and> vis' ::= (visibleCalls S)(i \<mapsto> insert c txCalls)
                    \<and> hb' ::= updateHb (happensBefore S) txCalls [c] 
                    \<and> S' ::= (S\<lparr>
                          localState := (localState S)(i \<mapsto> ls res), 
                          calls := (calls S)(c \<mapsto> Call Op args res ),
                          callOrigin := (callOrigin S)(c \<mapsto> t),
                          visibleCalls := vis',
                          happensBefore := hb' \<rparr>)
                    \<longrightarrow> checkCorrect' (progr, insert c txCalls, S', i)
                  )
           )
        | Return res \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>S'. S' ::= (S\<lparr>
                 localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>) \<longrightarrow>
               (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow> invariant progr (invContext' S')  
            )
        )))
"



lemma checkCorrect2F_mono[simp]:
"mono checkCorrect2F"
proof (rule monoI)
  show "checkCorrect2F x \<le> checkCorrect2F y" if c0: "x \<le> y"  for  x :: "(('localState, 'any::valueType) prog \<times> callId set \<times> ('localState, 'any) state \<times> invocation \<Rightarrow> bool)" and y
    apply auto
    apply (auto simp add: checkCorrect2F_def Let_def Def_def intro!: predicate1D[OF `x \<le> y`] split: option.splits localAction.splits if_splits)
    by force
qed



(*
definition checkCorrect2 :: "('localState, 'any) prog \<Rightarrow> callId set \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> bool" where
 "checkCorrect2 progr txCalls S i \<equiv> lfp checkCorrect2F (progr, txCalls, S, i)"
*)

definition checkCorrect2 :: "('localState, 'any::valueType) prog \<Rightarrow> callId set \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> bool" where
 "checkCorrect2 progr txCalls S i \<equiv> \<exists>n. (checkCorrect2F^^n) bot (progr, txCalls, S, i)"


find_theorems "op^^" Suc

lemma exists_nat_split: "(\<exists>n::nat. P n) \<longleftrightarrow> (P 0 \<or> (\<exists>n. P (Suc n)))"
  apply auto
  apply (case_tac n)
   apply auto
  done


lemma checkCorrect2_unfold:
"checkCorrect2 progr txCalls S i = (\<exists>n. checkCorrect2F ((checkCorrect2F^^n) bot) (progr, txCalls, S, i))"
  apply (subst checkCorrect2_def)
  apply (subst exists_nat_split)
  apply auto
  done



lemma checkCorrect2_simps:
assumes "(
           case currentProc S i of None \<Rightarrow> True
           | Some impl \<Rightarrow>
               (case impl (the (localState S i)) of LocalStep ls \<Rightarrow> (checkCorrect2 progr txCalls (S\<lparr>localState := localState S(i \<mapsto> ls)\<rparr>) i)
               | BeginAtomic ls \<Rightarrow>
                   currentTransaction S i = None \<and>
                   (\<forall>t S' vis' newTxns.
                       transactionStatus S t = None \<and>
                       invariant_all' S' \<and>
                       state_wellFormed S' \<and>
                       state_monotonicGrowth i S S' \<and>
                       localState S' i \<triangleq> ls \<and>
                       currentProc S' i \<triangleq> impl \<and>
                       currentTransaction S' i \<triangleq> t \<and>
                       transactionStatus S' t \<triangleq> Uncommited \<and>
                       transactionOrigin S' t \<triangleq> i \<and>
                       (\<forall>c. callOrigin S' c \<noteq> Some t) \<and>
                       visibleCalls S i \<triangleq> txCalls \<and>
                       vis' = txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S' \<and>
                       visibleCalls S' i \<triangleq> vis' \<and>
                       newTxns \<subseteq> dom (transactionStatus S') \<and>
                       consistentSnapshot S' vis' \<and> (\<forall>x. x \<noteq> t \<longrightarrow> transactionStatus S' x \<noteq> Some Uncommited) \<and> invariant progr (invContext' S') \<and> (invariant progr (invContext S') \<longrightarrow>
                       (checkCorrect2 progr vis' S' i)))
               | EndAtomic ls \<Rightarrow>
                   (case currentTransaction S i of None \<Rightarrow> False
                   | Some t \<Rightarrow> let S' = S\<lparr>localState := localState S(i \<mapsto> ls), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(t \<mapsto> Commited)\<rparr>
                               in (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow>
                                  invariant progr (invContext' S') \<and> (invariant progr (invContext' S') \<longrightarrow> (checkCorrect2 progr txCalls S' i)))
               | NewId ls \<Rightarrow> \<forall>uid ls'. 
                            generatedIds S uid = None
                           \<and> ls uid \<triangleq> ls'
                           \<and> uniqueIds uid = {uid}
                            \<longrightarrow> (checkCorrect2 progr txCalls (S\<lparr>localState := localState S(i \<mapsto> ls'), generatedIds := (generatedIds S)(uid \<mapsto> i)\<rparr>) i)
               | DbOperation Op args ls \<Rightarrow>
                   (case currentTransaction S i of None \<Rightarrow> False
                   | Some t \<Rightarrow> Ex (querySpec progr Op args (getContext S i)) \<and>
                               (\<forall>c res. calls S c = None \<and> querySpec progr Op args (getContext S i) res \<and> visibleCalls S i \<triangleq> txCalls \<longrightarrow>
                                        (checkCorrect2
                                         progr (insert c txCalls) (S
                                          \<lparr>localState := localState S(i \<mapsto> ls res), calls := calls S(c \<mapsto> Call Op args res), callOrigin := callOrigin S(c \<mapsto> t),
                                             visibleCalls := visibleCalls S(i \<mapsto> insert c txCalls), happensBefore := updateHb (happensBefore S) txCalls [c]\<rparr>)
                                          i)))
               | Return res \<Rightarrow>
                   currentTransaction S i = None \<and>
                   (let S' = S\<lparr>localState := (localState S)(i := None), currentProc := (currentProc S)(i := None), visibleCalls := (visibleCalls S)(i := None),
                                 invocationRes := invocationRes S(i \<mapsto> res), knownIds := knownIds S \<union> uniqueIds res\<rparr>
                    in (\<forall>t. transactionStatus S' t \<noteq> Some Uncommited) \<longrightarrow> invariant progr (invContext' S'))))"
shows "checkCorrect2 progr txCalls S i"
  apply (insert assms)
  apply (subst checkCorrect2_unfold)
  apply (subst checkCorrect2F_def)
  apply (auto simp add: Def_def split: option.splits localAction.splits)
  using checkCorrect2_def apply blast
  oops


(*
schematic_goal checkCorrect2_simps:
  "checkCorrect2 progr txCalls S i = ?F"
  apply (subst checkCorrect2_unfold)
  apply (subst checkCorrect2F_def)
  apply (fold checkCorrect2_def)
  apply (rule refl)
  done
*)


lemma consistentSnapshot_empty: "consistentSnapshot S {}"
  by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def)

lemma exists_optionI: "x \<noteq> None \<Longrightarrow> \<exists>y. x \<triangleq> y"
  by auto


lemma checkCorrect_eq2:
  assumes "invariant_all S" 
    and "state_wellFormed S"
    and "progr = prog S"
    and "visibleCalls S i \<triangleq> txCalls" 
    and c2: "(checkCorrect2F ^^bound) bot (progr, txCalls, S, i) "
  shows "checkCorrect progr S i"
  using assms proof (induct bound arbitrary: S txCalls)
  case 0

  have "consistentSnapshot S {}"
    by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def)
  hence "(checkCorrect2F ^^0) bot (progr, txCalls, S, i)"
    using `(checkCorrect2F ^^ 0) bot (progr, txCalls, S, i)` by blast
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
      progr' = progr;
      visibleCalls S i \<triangleq> txCalls;
      (checkCorrect2F ^^ bound) bot (progr,  txCalls, S, i)\<rbrakk>
    \<Longrightarrow> checkCorrect progr' S i" for S txCalls progr'
    using Suc  by blast


  have use_checkCorrect2: "(checkCorrect2F ^^ Suc bound) bot (progr, txCalls, S, i)" 
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
            by (auto simp add: )

          have step: "S ~~ (i, ALocal) \<leadsto> S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>"
            using LocalStep Some ls_def step_simp_ALocal by blast

          with state_wellFormed_combine_step[OF `state_wellFormed S`, OF step]
          show "state_wellFormed (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>)" by simp

          show " progr = prog (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>)" by simp

          from `visibleCalls S i \<triangleq> txCalls`
          show "visibleCalls (S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>) i \<triangleq> txCalls"
            by auto

          show "progr = progr" ..

          show "(checkCorrect2F ^^ bound) bot (progr, txCalls, S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>, i)"
          proof -

            from use_checkCorrect2
            show "(checkCorrect2F ^^ bound) bot (progr, txCalls, S\<lparr>localState := localState S(i \<mapsto> f)\<rparr>, i)"
              apply simp
              apply (subst(asm) checkCorrect2F_def)
              apply (auto simp add: LocalStep Def_def)
              done
          qed
        qed
      qed
    next
      case (BeginAtomic tx)

      

      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: BeginAtomic `visibleCalls S i \<triangleq> txCalls`)
        have cs_empty: "consistentSnapshot S {}"
          by (simp add: consistentSnapshot_empty)


        show "currentTransaction S i = None"
          using use_checkCorrect2
          apply simp
          apply (subst(asm) checkCorrect2F_def)
          apply (auto simp add: BeginAtomic)
          done

        fix t newTxns
        fix S'

        assume c0a: "currentTransaction S i = None"
            and c0: "transactionStatus S t = None"
            and c2a: "progr = prog S'"
            and c1: "invariant_all' S'"
            and c13: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited"
            and c2: "state_wellFormed S'"
            and c6a: "state_wellFormed (S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> tx), visibleCalls := visibleCalls S'(i \<mapsto> txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')\<rparr>)"
            and c3: "state_monotonicGrowth i S S'"
            and c4: "localState S' i \<triangleq> ls"
            and c5: "currentProc S' i \<triangleq> proc"
            and c6: "currentTransaction S' i = None"
            and c11a: "visibleCalls S' i \<triangleq> txCalls"
            and c11: "newTxns \<subseteq> dom (transactionStatus S')"
            and c12: "consistentSnapshot S' (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')"
            and c0: "transactionStatus S' t = None"
            and c15a: "\<forall>c. callOrigin S' c \<noteq> Some t"
            and c7: "transactionOrigin S' t = None"
            and transactionOriginUnchanged: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S t \<triangleq> i"

        define S'' where S''_def: "S'' = (S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> tx), visibleCalls := visibleCalls S'(i \<mapsto> txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')\<rparr>)"


        from `state_monotonicGrowth i S S'`
        have "transactionStatus S t \<le> transactionStatus S' t"
          by (simp add: state_monotonicGrowth_transactionStatus)
        with `transactionStatus S' t = None`
        have "transactionStatus S t = None"
          by (simp add: less_eq_option_None_is_None) (*EXTRACT*)
          



        show "checkCorrect (prog S') S'' i"
        proof (rule IH)
          show "prog S' = progr"
            by (simp add: `progr = prog S'`)
          thus "progr = prog S''"
            by (simp add: S''_def)

          show "visibleCalls S'' i \<triangleq> (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')"
            by (simp add: S''_def)

          show "state_wellFormed S''"
            using S''_def c6a by blast

          have "invContext S'' = invContext S'"
            by (auto simp add: S''_def c13 c2 c0 invContextH_def restrict_map_def)

          with `invariant_all' S'`
          show "invariant_all S''"
            by (auto simp add: S''_def c13 c2 invContext_same_allCommitted)

          show "(checkCorrect2F ^^ bound) bot (progr, txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S', S'', i)"
            using use_checkCorrect2
            apply simp
            apply (subst(asm) checkCorrect2F_def)
            apply (auto simp add: BeginAtomic `visibleCalls S i \<triangleq> txCalls`)
            apply (drule_tac x=t in spec)
            apply (drule_tac x=S' in spec)
            apply (drule_tac x=newTxns in spec)
            apply (auto simp add: Def_def)
            using \<open>transactionStatus S t = None\<close> apply blast
                           apply (simp add: c2a)
                          apply (simp add: `invariant_all' S'`)
            using c13 apply blast
            apply (simp add: c2)
            using `state_wellFormed S''` apply (simp add: S''_def)
            using `state_monotonicGrowth i S S'` apply simp
            using transactionOriginUnchanged apply blast
            using transactionOriginUnchanged apply blast
            using `localState S' i \<triangleq> ls` apply simp
            using `currentProc S' i \<triangleq> proc` apply simp
            using `currentTransaction S' i = None` apply simp
            using `visibleCalls S' i \<triangleq> txCalls` apply simp
            using c11 apply blast

            using ` consistentSnapshot S' (txCalls \<union> callsInTransaction S' newTxns \<down> happensBefore S')` apply simp
            using `transactionStatus S' t = None` apply simp
            using c15a apply blast
            using c7 apply blast
            by (simp add: S''_def)


        qed
      qed
    next
      case (EndAtomic ls')

      obtain tx where tx: "currentTransaction S i \<triangleq> tx"
        using use_checkCorrect2
        apply simp
        apply (subst(asm) checkCorrect2F_def)
        apply (auto simp add: EndAtomic split: option.splits)
        done

      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: EndAtomic tx Let_def)

        assume all_committed: "\<forall>t. t \<noteq> tx \<longrightarrow> transactionStatus S t \<noteq> Some Uncommited"
          and wf: "state_wellFormed (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>)"


        show inv: "invariant progr (invContextH2 (callOrigin S) (transactionOrigin S) (transactionStatus S(tx \<mapsto> Commited)) (happensBefore S) (calls S) (knownIds S) (invocationOp S) (invocationRes S))"
          using use_checkCorrect2
          apply simp
          apply (subst(asm) checkCorrect2F_def)
          apply (auto simp add: Def_def EndAtomic all_committed tx split: option.splits if_splits)
          done


        show "checkCorrect progr (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>) i"
        proof (rule IH)
          show "invariant_all (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>)"
            using inv apply (auto simp add:)
            apply (subst invContextH_same_allCommitted)
            using wellFormed_callOrigin_dom3[OF `state_wellFormed S`] wellFormed_state_callOrigin_transactionStatus[OF `state_wellFormed S`]
                  wellFormed_happensBefore_calls_l[OF `state_wellFormed S`]
                  wellFormed_happensBefore_calls_r[OF `state_wellFormed S`]
                (*  wellFormed_currentTransactionUncommited[OF `state_wellFormed S`]
                  wf_transaction_status_iff_origin[OF `state_wellFormed S`]*)
                  all_committed
                  apply (auto simp add: Def_def)
              apply (metis Suc.prems(2) not_Some_eq tx wellFormed_currentTransactionUncommited wf_transaction_status_iff_origin)
            using Suc.prems(2) wf_transaction_status_iff_origin apply blast
            using Suc.prems(2) wf_transaction_status_iff_origin by blast

          show "progr = progr" ..

          show "state_wellFormed (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>)"
            using local.wf by blast

          show "progr = prog (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>)"
            by simp

          from `visibleCalls S i \<triangleq> txCalls`
          show "visibleCalls (S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>) i \<triangleq> txCalls"
            by simp

          show "(checkCorrect2F ^^ bound) bot
             (progr, txCalls, S\<lparr>localState := localState S(i \<mapsto> ls'), currentTransaction := (currentTransaction S)(i := None), transactionStatus := transactionStatus S(tx \<mapsto> Commited)\<rparr>, i)"
            using use_checkCorrect2
            apply simp
            apply (subst(asm) checkCorrect2F_def)
            by (auto simp add: Def_def EndAtomic all_committed tx split: option.splits if_splits)
        qed
      qed
    next
      case (NewId ls')
      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: NewId)

        fix uid ls''
        assume "generatedIds S uid = None" 
          and "ls' uid \<triangleq> ls''"
          and "uniqueIds uid = {uid}"

        have step: "S ~~ (i, ANewId uid) \<leadsto> S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := (generatedIds S)(uid \<mapsto> i)\<rparr>"
          apply (auto simp add: step_simps)
          using NewId \<open>generatedIds S uid = None\<close> \<open>ls' uid \<triangleq> ls''\<close> \<open>uniqueIds uid = {uid}\<close> by blast


        show "checkCorrect progr (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>) i"
        proof (rule IH)
          show " invariant_all (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>)"
            using Suc.prems(1) by auto

          from state_wellFormed_combine_step[OF `state_wellFormed S`, OF step]
          show "state_wellFormed (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>)"
            by simp

          show "progr = prog (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>)"
            by simp

          show "visibleCalls (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>) i \<triangleq> txCalls"
            by (simp add: Suc.prems(4))

          show "progr = progr" ..

          show "(checkCorrect2F ^^ bound) bot (progr, txCalls, (S\<lparr>localState := localState S(i \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i)\<rparr>), i)"
            using use_checkCorrect2
            apply simp
            apply (subst(asm) checkCorrect2F_def)
            apply (auto simp add: Def_def NewId  split: option.splits if_splits)
            using \<open>generatedIds S uid = None\<close> \<open>ls' uid \<triangleq> ls''\<close> \<open>uniqueIds uid = {uid}\<close> by blast
        qed
      qed
    next
      case (DbOperation m a r)

      obtain tx where tx: "currentTransaction S i \<triangleq> tx"
        using use_checkCorrect2
        apply simp
        apply (subst(asm) checkCorrect2F_def)
        apply (auto simp add: DbOperation split: option.splits)
        done


      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: DbOperation tx `visibleCalls S i \<triangleq> txCalls`)

        show "\<exists>res. querySpec progr m a (getContextH (calls S) (happensBefore S) (Some txCalls)) res"
          using use_checkCorrect2
          apply simp
          apply (subst(asm) checkCorrect2F_def)
          by (auto simp add: DbOperation `visibleCalls S i \<triangleq> txCalls` split: option.splits)

        show "checkCorrect progr (S\<lparr>localState := localState S(i \<mapsto> r res), calls := calls S(c \<mapsto> Call m a res), callOrigin := callOrigin S(c \<mapsto> tx), visibleCalls := visibleCalls S(i \<mapsto> insert c txCalls), happensBefore := updateHb (happensBefore S) txCalls [c]\<rparr>) i"
          if c0: "calls S c = None"
            and c1: "querySpec progr m a (getContextH (calls S) (happensBefore S) (Some txCalls)) res"
          for  c res
        proof (rule IH, auto)



          have "(invContextH (callOrigin S(c \<mapsto> tx)) (transactionOrigin S) (transactionStatus S) (updateHb (happensBefore S) txCalls [c]) (calls S(c \<mapsto> Call m a res)) (knownIds S) (invocationOp S) (invocationRes S)) 
               = invContext S"
            using Suc.prems(2) c0 tx by (auto simp add: invContextH_def updateHb.simps(2) restrict_relation_def)


          with `invariant_all S`
          show "invariant progr
             (invContextH (callOrigin S(c \<mapsto> tx)) (transactionOrigin S) (transactionStatus S) (updateHb (happensBefore S) txCalls [c]) (calls S(c \<mapsto> Call m a res)) (knownIds S) (invocationOp S) (invocationRes S))"
            by auto

          have step: "S ~~ (i, ADbOp c m a res) \<leadsto> S\<lparr>localState := localState S(i \<mapsto> r res), calls := calls S(c \<mapsto> Call m a res), callOrigin := callOrigin S(c \<mapsto> tx), visibleCalls := visibleCalls S(i \<mapsto> insert c txCalls),
              happensBefore := updateHb (happensBefore S) txCalls [c]\<rparr>"
            by (auto simp add: step_simps DbOperation Suc.prems(4) c0 c1 tx updateHb_single)


          show "state_wellFormed
            (S\<lparr>localState := localState S(i \<mapsto> r res), calls := calls S(c \<mapsto> Call m a res), callOrigin := callOrigin S(c \<mapsto> tx), visibleCalls := visibleCalls S(i \<mapsto> insert c txCalls),
              happensBefore := updateHb (happensBefore S) txCalls [c]\<rparr>)"
            using state_wellFormed_combine1[OF `state_wellFormed S`, OF step] by simp


          show "(checkCorrect2F ^^ bound) bot
             (progr, insert c txCalls, S
              \<lparr>localState := localState S(i \<mapsto> r res), calls := calls S(c \<mapsto> Call m a res), callOrigin := callOrigin S(c \<mapsto> tx), visibleCalls := visibleCalls S(i \<mapsto> insert c txCalls),
                 happensBefore := updateHb (happensBefore S) txCalls [c]\<rparr>,
              i)"
            using use_checkCorrect2
            apply simp
            apply (subst(asm) checkCorrect2F_def)
            apply (auto simp add: Def_def DbOperation tx Suc.prems(4) c0 c1 split: option.splits if_splits)
            done

        qed
      qed
    next
      case (Return r)

      have tx: "currentTransaction S i = None"
        using use_checkCorrect2
        apply simp
        apply (subst(asm) checkCorrect2F_def)
        apply (auto simp add: Return split: option.splits)
        done

      show ?thesis
      proof (subst checkCorrect_simps, auto simp add: Return tx `visibleCalls S i \<triangleq> txCalls`)

        show "invariant progr (invContextH2 (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S) (knownIds S \<union> uniqueIds r) (invocationOp S) (invocationRes S(i \<mapsto> r)))"
          if c0: "\<forall>t. transactionStatus S t \<noteq> Some Uncommited"
          using use_checkCorrect2
          apply simp
          apply (subst(asm) checkCorrect2F_def)
          by (auto simp add: Def_def c0 Return split: option.splits)

      qed
    qed
  qed
qed


lemma checkCorrect_eq2':
  assumes initState: "S\<in>initialStates progr i" 
    and invInitial: "invariant_all S"
    and c2: "(checkCorrect2F ^^bound) bot (progr, {}, S, i) "
  shows "checkCorrect progr S i"
  using `invariant_all S`
proof (rule checkCorrect_eq2)
  show " state_wellFormed S"
    using initState initialStates_wellFormed by auto

  show "progr = prog S"
    using initState by (auto simp add: initialStates_def)

  show "visibleCalls S i \<triangleq> {}"
    using initState by (auto simp add: initialStates_def)

  show "(checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    using c2 .
qed

(*
lemma checkCorrect_eq2'':
  assumes initState: "S\<in>initialStates progr i" 
    and invInitial: "invariant_all' S"
    and c2: "checkCorrect2 progr {} S i"
  shows "checkCorrect progr S i"
proof -

  from c2
  have "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    apply (auto simp add: checkCorrect2_def)


  from initState invInitial
  show "checkCorrect progr S i"
  proof (rule checkCorrect_eq2')


  show " state_wellFormed S"
    using initState initialStates_wellFormed by auto

  show "progr = prog S"
    using initState by (auto simp add: initialStates_def)

  show "visibleCalls S i \<triangleq> {}"
    using initState by (auto simp add: initialStates_def)

  show "(checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    using c2 .
qed
*)

lemma show_programCorrect_using_checkCorrect1:
  assumes initalStatesCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> invariant_all' S"
    and invInitial: "invariant_all' (initialState progr)"
   and stepsCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates progr i\<rbrakk> \<Longrightarrow> \<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
 shows "programCorrect progr"
proof (rule show_correctness_via_single_session)
  show "invariant_all (initialState progr)"
    using invInitial apply (subst invContext_same_allCommitted)
    by (auto, simp add: initialState_def)


  show "programCorrect_s progr"
  proof (rule show_program_correct_single_invocation)

    show "invariant_all' S"
      if c0: "S \<in> initialStates progr i"
      for  S i
      using initalStatesCorrect that by auto


    show "checkCorrect progr S i"
      if c0: "S \<in> initialStates progr i"
        and c1: "invariant_all' S"
        and c2: "state_wellFormed S"
      for  S i
      using c0 c1 checkCorrect_eq2' stepsCorrect
      using c2 initialState_noTxns1 invContext_same_allCommitted by fastforce 

  qed
qed


definition initialStates' :: "('localState, 'any::valueType) prog \<Rightarrow> invocation \<Rightarrow> ('localState, 'any) state set"  where
  "initialStates' progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocationOp := (invocationOp S)(i \<mapsto> (procName, args))\<rparr>) 
 | S procName args initState impl.
    prog S = progr
  \<and> procedure progr procName args \<triangleq> (initState, impl)  
  \<and> uniqueIdsInList args \<subseteq> knownIds S
  \<and> invariant_all' S
  \<and> state_wellFormed S (*  TODO add wellformed? *)
  \<and> invocationOp S i = None
  \<and> (\<forall>tx. transactionStatus S tx \<noteq> Some Uncommited)
  \<and> (\<forall>tx. transactionOrigin S tx \<noteq> Some i)
}"

lemma initialStates'_same:
  shows "initialStates progr i = initialStates' progr i"
  apply (auto simp add: initialStates_def initialStates'_def)
   apply (rule_tac x=S in exI)
   apply (rule_tac x=procName in exI)
   apply (rule_tac x=args in exI)
   apply (rule_tac x=initState in exI)
   apply (rule_tac x=impl in exI)
   apply (auto simp add: invContext_same_allCommitted)
  apply (rule_tac x=S in exI)
  apply (rule_tac x=procName in exI)
  apply (rule_tac x=args in exI)
  apply (rule_tac x=initState in exI)
  apply (rule_tac x=impl in exI)
  apply (auto simp add: invContext_same_allCommitted)
  done


lemma show_programCorrect_using_checkCorrect:
  assumes initialStatesCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates' progr i\<rbrakk> \<Longrightarrow> invariant_all' S"
    and invInitial: "invariant_all' (initialState progr)"
   and stepsCorrect: "\<And>S i. \<lbrakk>S\<in>initialStates' progr i\<rbrakk> \<Longrightarrow> \<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
 shows "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect1)

  from invInitial
  show "invariant_all' (initialState progr)".

  from stepsCorrect
  show "\<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
    if c0: "S\<in>initialStates progr i"
    for  S i
    using initialStates'_same that by blast

  show "invariant_all' S"
    if c0: "S \<in> initialStates progr i"
    for  S i
    using initialStates'_same initialStatesCorrect that by blast
qed


       

end