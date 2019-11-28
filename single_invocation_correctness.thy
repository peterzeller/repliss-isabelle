theory single_invocation_correctness
  imports execution_invariants_s fixedpoints execution_invariants invContext_simps
begin

section \<open>Single-invocId corrrectness\<close>

text \<open>This theory includes techniques to prove that a program is correct in the single-invocId semantics.\<close>

text \<open>
  Start with initial state,
  
  then steps
  
  finally return and last check
  
  somehow automated

\<close>


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

lemma updateHb_simp1:
  assumes "x \<notin> set cs"
  shows "(x,y) \<in> updateHb hb vis cs \<longleftrightarrow> ((x,y) \<in> hb \<or> x\<in>vis \<and> y \<in> set cs)"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    by (auto simp add: updateHb_cons)
qed


lemma updateHb_simp2:
  assumes "y \<notin> set cs"
  shows "(x,y) \<in> updateHb hb vis cs \<longleftrightarrow> (x,y) \<in> hb"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    by (auto simp add: updateHb_cons)
qed

lemma updateHb_in_vis:
  assumes 
    "x\<in>vis"
    and "y\<in>set cs"
   shows "(x,y) \<in> updateHb hb vis cs"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    apply (auto simp add: updateHb_cons  )
    by (metis UnI2 insert_is_Un mem_Sigma_iff singletonI updateHb_simp2)
qed

lemma updateHb_simp3:
  assumes 
    "cs!i = x"
    and "cs!j = y"
    and "i<j"
    and "j<length cs"
   shows "(x,y) \<in> updateHb hb vis cs"
  using assms proof (induct cs arbitrary: hb vis i j)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)
  then show ?case 
    apply (auto simp add: updateHb_cons in_set_conv_nth nth_Cons' )
    by (simp add: updateHb_in_vis)
qed

lemma updateHb_simp_distinct:
  assumes 
    "distinct cs"
  shows "(x,y) \<in> updateHb hb vis cs 
  \<longleftrightarrow> ((x, y)\<in>hb \<or> x\<in>vis \<and> y\<in>set cs \<or> (\<exists>i j. cs!i=x \<and> cs!j=y \<and> i < j \<and> j < length cs))"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by simp
next
  case (Cons a cs)

  have IH:
    "(x,y) \<in> updateHb (hb \<union> vis \<times> {a}) (insert a vis) cs
\<longleftrightarrow> ((x, y)\<in>(hb \<union> vis \<times> {a}) \<or> x\<in>(insert a vis) \<and> y\<in>set cs \<or> (\<exists>i j. cs!i=x \<and> cs!j=y \<and> i < j \<and> j < length cs))"
    apply (rule Cons) using Cons.prems by auto

  show ?case 
    apply (auto simp add: updateHb_cons IH )
    apply (metis One_nat_def in_set_conv_nth list.sel(3) not_less_eq nth_Cons_0 nth_Cons_pos nth_tl zero_less_Suc)
    apply (metis One_nat_def Suc_mono diff_Suc_1 nth_Cons_Suc)
    apply (metis One_nat_def Suc_less_eq Suc_pred nat_neq_iff not_less_zero nth_Cons')
    by (metis One_nat_def diff_Suc_1 gr_implies_not0 less_Suc_eq_0_disj nth_Cons')
qed


lemma updateHb_simp_distinct2:
  shows "(x,y) \<in> updateHb hb vis cs 
  \<longleftrightarrow> ((x, y)\<in>hb 
      \<or> x\<in>vis \<and> y\<in>set cs 
      \<or> before_in_list cs x y)"
proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case by auto
next
case (Cons a cs)
  show ?case 
    by (auto simp add: updateHb_cons before_in_list_cons updateHb_simp2 Cons.hyps before_in_list_contains_r)
qed


\<comment> \<open>TODO remove?\<close>
abbreviation invariant_all' :: "('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" where
"invariant_all' state \<equiv>  invariant (prog state) (invContext' state)"


(*
\<comment> \<open>check program (with a given start-state, bound by a number of steps)\<close>
definition checkCorrectF :: "(('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) prog \<times> ('proc, 'ls, 'operation, 'any) state \<times> invocId \<Rightarrow> bool) 
                           \<Rightarrow> ('proc, 'ls, 'operation, 'any) prog \<times> ('proc, 'ls, 'operation, 'any) state \<times> invocId \<Rightarrow> bool" where
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
              \<and> (\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted)
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
              \<and> (S'' = S'\<lparr>transactionStatus := (transactionStatus S')(t \<mapsto> Uncommitted),
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
                  transactionStatus := (transactionStatus S)(t \<mapsto> Committed) \<rparr>) in
                  (\<forall>t. transactionStatus S' t \<noteq> Some Uncommitted) 
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
               (\<forall>t. transactionStatus S' t \<noteq> Some Uncommitted) \<longrightarrow> invariant_all' S'    
            )
        )))
"



lemma checkCorrectF_mono:
"mono checkCorrectF"
proof (rule monoI)
  show "checkCorrectF x \<le> checkCorrectF y" if c0: "x \<le> y"  for  x :: "(('ls, 'any::valueType) prog \<times> ('proc, 'ls, 'operation, 'any) state \<times> invocId \<Rightarrow> bool)" and y
    by (auto simp add: checkCorrectF_def Let_def intro: predicate1D[OF \<open>x \<le> y\<close>] split: option.splits localAction.splits)

qed


definition checkCorrect :: "('ls, 'any::valueType) prog \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> invocId \<Rightarrow> bool" where
 "checkCorrect progr S i \<equiv> lfp checkCorrectF (progr, S, i)"



schematic_goal checkCorrect_simps:
  "checkCorrect progr S i = ?F"
  apply (subst checkCorrect_def)
  apply (subst lfp_unfold)
  apply (simp add: checkCorrectF_mono)
  apply (subst checkCorrectF_def)
  apply (fold checkCorrect_def)
  apply (rule refl)
  done


lemma checkCorrect_noProc:
  assumes "currentProc S i = None"
  shows "checkCorrect progr S i"
  using assms by (auto simp add: checkCorrect_simps)



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
*)
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
  then have i1: "invocationOp S i \<triangleq> info" and  i2: "invocationOp S' i \<triangleq> info"
    by auto

  from \<open>S' ~~ (i, a) \<leadsto>\<^sub>S S''\<close>
  show ?case
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )

  next
    case (newId C s ls f ls' uid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (beginAtomic C s ls f ls' t C' C'' vis vis' txns)
    then show ?case using i2 state_monotonicGrowth_invocationOp[OF \<open>state_monotonicGrowth s C C'\<close>]
      by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (endAtomic C s ls f ls' t C' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (dbop C s ls f Op  ls' t c res vis)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (invocation C s procName  initState impl C' C'' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  next
    case (return C s ls f res C' valid)
    then show ?case using i2 by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
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

  from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> and \<open>state_wellFormed_s S i\<close>
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
    then have "isAInvoc (fst (trace ! j))" 
      using startsWithInvoc hd_drop_conv_nth traceLen by force 
  }
  moreover
  {
    assume "j \<noteq> 0"

    from afterFirstStep
    obtain Sc where steps_until_after_j: "Sa ~~ (i, take j (tl trace)) \<leadsto>\<^sub>S* Sc"
      by (metis append_take_drop_id steps_s_append_simp)


\<comment> \<open>get Sb so that S Sa Sb S\<close>
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

    then have "invocationOp Sb i \<noteq> None"
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
  shows "transactionStatus S tx \<noteq> Some Uncommitted"
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


  from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> 
  show ?case 
    using \<open>i' \<noteq> i\<close> apply (auto simp add: step_s.simps \<open>currentTransaction S i' = None\<close>)
    by (meson option.exhaust wellFormed_currentTransaction_unique_h(2))+
qed

lemma state_wellFormed_combine1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto> S'"
  and "a\<noteq>AFail"
shows "state_wellFormed S'"
  using \<open>state_wellFormed S\<close> proof (rule state_wellFormed_combine)
  from \<open>S ~~ (i, a) \<leadsto> S'\<close>
  show "S ~~ [(i,a)] \<leadsto>* S'"
    by (simp add: steps_single)
  show "\<And>ia. (ia, AFail) \<notin> set [(i, a)]"
    using \<open>a\<noteq>AFail\<close> by simp
qed

lemma state_wellFormed_combine_s1:
  assumes "state_wellFormed S"
  and "S ~~ (i, a) \<leadsto>\<^sub>S S'"
shows "state_wellFormed S'"
proof -

from \<open>S ~~ (i, a) \<leadsto>\<^sub>S S'\<close> 
  show "state_wellFormed S'"
  proof (induct rule: step_s.cases)
    case (local C s ls f ls')
    then have "S ~~ (i, ALocal) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (newId C s ls f ls' uid uidv ls'')
    then have "S ~~ (i, ANewId uidv) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (beginAtomic C s ls f ls' t C' vis vis' newTxns txns)
    then show ?case 
      by blast
  next
    case (endAtomic C s ls f ls' t C' valid)
    then have "S ~~ (i, AEndAtomic) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (dbop C s ls f Op ls' t c res vis)
    then have "S ~~ (i, ADbOp c Op res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  next
    case (invocation C s proc initState impl C' C'' valid)
    then have "C' ~~ (i, AInvoc proc) \<leadsto> C''"
      apply (auto simp add: step.simps)
      using wf_localState_to_invocationOp by blast+

    then show ?case
      using \<open>state_wellFormed C'\<close> \<open>S' = C''\<close> state_wellFormed_combine1 by blast
  next
    case (return C s ls f res C' valid)
    then have "S ~~ (i, AReturn res) \<leadsto> S'"
      by (auto simp add: step.simps)
    with \<open>state_wellFormed S\<close> show ?case 
      by (rule state_wellFormed_combine1, simp)
  qed
qed

lemma committedCalls_allCommitted:
  assumes wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. transactionStatus S t \<noteq> Some Uncommitted"
  shows "committedCalls S = dom (calls S)"
  apply (auto simp add: committedCallsH_def isCommittedH_def )
   apply (simp add: domD domIff local.wf wellFormed_callOrigin_dom3)
  apply (case_tac "callOrigin S x", auto)
  apply (metis local.wf option.distinct(1) wellFormed_callOrigin_dom3)
  by (metis (full_types) domD domIff local.wf noUncommitted transactionStatus.exhaust wellFormed_state_callOrigin_transactionStatus)



lemma invContextH_same_allCommitted:
  assumes  wf1: "\<And>c. (state_calls c = None) \<longleftrightarrow> (state_callOrigin c = None)"
    and wf2: "\<And>c tx. state_callOrigin c \<triangleq> tx \<Longrightarrow> state_transactionStatus tx \<noteq> None"
    and wf3: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls a \<noteq> None"
    and wf4: "\<And>a b. (a, b) \<in> state_happensBefore \<Longrightarrow> state_calls b \<noteq> None"
    and wf5: "\<And>c. (state_transactionOrigin c = None) \<longleftrightarrow> (state_transactionStatus c = None)"
    and noUncommitted: "\<And>t. state_transactionStatus t \<noteq> Some Uncommitted"
  shows "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes
       = invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore state_calls state_knownIds state_invocationOp state_invocationRes"
  apply (auto simp add: invContextH_def invContextH2_def intro!: ext)
      apply (auto simp add: committedCallsH_def isCommittedH_def restrict_map_def restrict_relation_def)
      apply (metis (full_types) noUncommitted option.exhaust_sel transactionStatus.exhaust wf1 wf2)
     apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf3)
    apply (metis (full_types) noUncommitted option.exhaust transactionStatus.exhaust wf1 wf2 wf4)
   apply (metis (full_types) noUncommitted option.exhaust_sel transactionStatus.exhaust wf2)
  by (metis noUncommitted option.exhaust_sel transactionStatus.exhaust wf5)

lemma invContext_same_allCommitted:
  assumes  wf: "state_wellFormed S"
    and noUncommitted: "\<And>t. transactionStatus S t \<noteq> Some Uncommitted"
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
   show "\<And>t. transactionStatus S t \<noteq> Some Uncommitted"
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






lemma show_exists_state:
  fixes P :: "('proc, 'ls, 'operation, 'any)state \<Rightarrow> bool"
  assumes "\<exists>calls happensBefore prog callOrigin transactionOrigin
   generatedIds knownIds invocationOp invocationRes transactionStatus
localState currentProc visibleCalls currentTransaction. P \<lparr>
  calls = calls,
  happensBefore = happensBefore,
  callOrigin  = callOrigin,
  transactionOrigin  = transactionOrigin,
  knownIds  = knownIds,
  invocationOp  =invocationOp,
  invocationRes =invocationRes,
  prog = prog,
  transactionStatus  =transactionStatus,
  generatedIds  = generatedIds,
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

lemma prog_initial: "prog (initialState program) = program"
  by (auto simp add: initialState_def)



definition Def (infix "::=" 50) where
"x ::= y \<equiv> x = y"

definition DefSome (infix "::\<triangleq>" 50) where
"x ::\<triangleq> y \<equiv> y = Some x"




lemma exists_nat_split: "(\<exists>n::nat. P n) \<longleftrightarrow> (P 0 \<or> (\<exists>n. P (Suc n)))"
  apply auto
  apply (case_tac n)
   apply auto
  done






lemma consistentSnapshot_empty: "consistentSnapshot S {}"
  by (auto simp add: consistentSnapshotH_def causallyConsistent_def transactionConsistent_def  transactionConsistent_committed_def transactionConsistent_atomic_def)



lemma exists_optionI: "x \<noteq> None \<Longrightarrow> \<exists>y. x \<triangleq> y"
  by auto



lemma transactionStatus_initial: "transactionStatus (initialState progr) t = None"
  by (simp add: initialState_def)




definition initialStates' :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) prog \<Rightarrow> invocId \<Rightarrow> ('proc, 'ls, 'operation, 'any) state set"  where
  "initialStates' progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocationOp := (invocationOp S)(i \<mapsto> proc)\<rparr>) 
 | S proc initState impl.
    prog S = progr
  \<and> procedure progr proc = (initState, impl)  
  \<and> uniqueIds proc \<subseteq> knownIds S
  \<and> invariant_all' S
  \<and> state_wellFormed S \<comment> \<open>   TODO add wellformed?  \<close>
  \<and> invocationOp S i = None
  \<and> (\<forall>tx. transactionStatus S tx \<noteq> Some Uncommitted)
  \<and> (\<forall>tx. transactionOrigin S tx \<noteq> Some i)
}"

lemma initialStates'_same:
  shows "initialStates progr i = initialStates' progr i"
  apply (auto simp add: initialStates_def initialStates'_def)
   apply (rule_tac x=S in exI)
   apply (rule_tac x=proc in exI)
   apply (rule_tac x=initState in exI)
   apply (rule_tac x=impl in exI)
   apply (auto simp add: invContext_same_allCommitted)
  apply (rule_tac x=S in exI)
  apply (rule_tac x=proc in exI)
  apply (rule_tac x=initState in exI)
  apply (rule_tac x=impl in exI)
  apply (auto simp add: invContext_same_allCommitted)
  done


       

end