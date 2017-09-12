theory single_invocation_correctness
imports approach
begin

text {*
  Start with initial state,
  
  then steps
  
  finally return and last check
  
  somehow automated

*}


definition initialStates :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state set"  where
"initialStates progr \<equiv> {S | S S' procName args initState impl i.
  procedure progr procName args \<triangleq> (initState, impl)  
  \<and> uniqueIdsInList args \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> invocationOp S i = None
  \<and> S' = (S\<lparr>localState := (localState S)(i \<mapsto> initState),
                 currentProc := (currentProc S)(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S)(i \<mapsto> {}),
                 invocationOp := (invocationOp S)(i \<mapsto> (procName, args))\<rparr>)
}"

(* check program (with a given start-state, bound by a number of steps) *)
fun checkCorrect :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> nat \<Rightarrow> bool" where
"checkCorrect progr S i 0 = True"
| "checkCorrect progr S i (Suc bound) =
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            checkCorrect progr (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>) i bound
        | BeginAtomic ls \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S'.
                transactionStatus S t = None
              \<and> invariant_all S'
              \<and> state_wellFormed S'
              \<and> state_monotonicGrowth S S'
              \<and> localState S' i \<triangleq> ls
              \<and> currentTransaction S' i \<triangleq> t
              \<and> transactionStatus S' t \<triangleq> Uncommited
              \<and> transactionOrigin S' t \<triangleq> i
              \<longrightarrow> checkCorrect progr S' i bound)
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                let S' = (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>) in
                invariant_all S'
                \<and> checkCorrect progr S' i bound
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid.
            uid \<notin> generatedIds S
            \<longrightarrow> checkCorrect progr (S\<lparr>localState := (localState S)(i \<mapsto> ls uid), generatedIds := generatedIds S \<union> {uid} \<rparr>) i bound
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
                    \<longrightarrow> checkCorrect progr (S\<lparr>
                          localState := (localState S)(i \<mapsto> ls res), 
                          calls := (calls S)(c \<mapsto> Call Op args res ),
                          callOrigin := (callOrigin S)(c \<mapsto> t),
                          visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                          happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>) i bound
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
               invariant_all S'    
            )
        ))
"


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


lemma 
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
      using local.beginAtomic(13) by blast
  next
    case (endAtomic ls f ls' t valid)
    then show ?thesis using checkCorrect_S by auto
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
    by (case_tac bound', auto)
  qed
  thus "traceCorrect_s program trace \<and> checkCorrect program S_fin i (bound - length trace)"
    apply auto
    by (metis IH Pair_inject Un_insert_right append_Nil2 insert_iff list.set(2) prod.collapse set_append traceCorrect_s_def trace_split)
  
qed  
    
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
  then show ?case by (auto simp add: step_s.simps state_monotonicGrowth_def elim: use_map_le )
  
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
    and wf: "state_wellFormed S"
shows "invocationOp S' i \<noteq> None"   
using step wf apply (auto simp add: step_s.simps )
by (metis invation_info_set_iff_invocation_happened(1) invation_info_set_iff_invocation_happened(2) invocation_ops_if_localstate_nonempty option.simps(3) state_wellFormed_def)+



lemma has_invocationOp_afterStart:
assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and notEmpty: "trace \<noteq> []"
    and wf: "state_wellFormed S"
shows "invocationOp S' i \<noteq> None"   
using steps notEmpty wf proof (induct rule: step_s_induct)
  case initial
  then show ?case
    by simp  
next
  case (step tr S a S')
  have "state_wellFormed S" 
    sorry (* TODO add steps_s to step_s_induct and prove that steps_s preserves wf *)
    
  from `S ~~ (i, a) \<leadsto>\<^sub>S S'` and `state_wellFormed S`
  show ?case 
    by (rule has_invocationOp_afterOneStep)
qed


lemma invocations_only_in_beginning:
assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
    and wf: "state_wellFormed S"
    and notStarted: "invocationOp S i = None"
    and traceLen: "j < length trace"
shows "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
proof -
  
  from steps
  obtain S_mid where "S ~~ (i, take j trace) \<leadsto>\<^sub>S* S_mid" and "S_mid ~~ (i, drop j trace) \<leadsto>\<^sub>S* S'"
    using steps_s_append_simp by force
  
    
  obtain Sa where firstStep: "S ~~ (i, hd trace) \<leadsto>\<^sub>S Sa"
    by (metis traceLen cons_eq_conv_conj length_Suc_conv less_imp_Suc_add steps steps_s_cons_simp)
   
  with notStarted
  have startsWithInvoc: "isAInvoc (fst (hd trace))"
    by (auto simp add: step_s.simps isAInvoc_def local.wf wellFormed_invoc_notStarted(2))
    
  
    
    
    
  {
    assume "j = 0"
    hence "isAInvoc (fst (trace ! j))" 
      using startsWithInvoc hd_drop_conv_nth traceLen by force 
  }
  moreover
  {
    assume "j \<noteq> 0"
    have "\<not>isAInvoc (fst (trace ! j))" 
      sorry
  }
  ultimately
  show "isAInvoc (fst (trace ! j)) \<longleftrightarrow> j = 0"
    by blast
qed    
  



lemma 
assumes initialCorrect: "\<And>S. S\<in>initialStates program \<Longrightarrow> invariant_all S "
    and check: "\<And>S i. S\<in>initialStates program \<Longrightarrow> checkCorrect program S i bound"
    and steps: "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
    and trace_len: "length trace < bound"
    and trace_len2: "0 < length trace"
shows "traceCorrect_s program trace \<and> checkCorrect program S_fin i (bound - length trace)"
using steps check trace_len proof (induct "length trace")
  case 0
  thus ?case
    using trace_len2 by linarith 
    
next
  case (Suc trLen)
  
  
  
  obtain tr a where tr_def: "trace = tr@[a]"
    
  
  
  then show ?case sorry
qed



    
lemma show_program_correct_single_invocation:
assumes initialCorrect: "\<And>S. S\<in>initialStates program \<Longrightarrow> invariant_all S "
    and check: "\<And>S i. S\<in>initialStates program \<Longrightarrow> checkCorrect program S i bound"
shows "programCorrect_s program"
proof (auto simp add: programCorrect_s_def)
  fix trace i S_fin
  assume steps: "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
  
  from steps
  show "traceCorrect_s program trace"
  proof (induct rule: step_s_induct)
    case initial
    then show ?case
      by (simp add: traceCorrect_s_def) 
  next
    case (step tr S a S')
    
    (* 
    Idea: 
    
    - states are reachable
    - checkCorrect proves correctness for all reachable states
    
    *)
    
    from `S ~~ (i, a) \<leadsto>\<^sub>S S'`
    have "snd a \<noteq> False"
    proof (cases rule: step_s.induct)
      case (local C s ls f ls')
      then show ?thesis sorry
    next
      case (newId C s ls f ls' uid)
      then show ?thesis sorry
    next
      case (beginAtomic C s ls f ls' t C' txns)
      then show ?thesis sorry
    next
      case (endAtomic C s ls f ls' t C' valid)
      then show ?thesis sorry
    next
      case (dbop C s ls f Op args ls' t c res vis)
      then show ?thesis sorry
    next
      case (invocation C s procName args initState impl C' C'' valid)
      then show ?thesis sorry
    next
      case (return C s ls f res C' valid)
      then show ?thesis sorry
    qed
      
    from `traceCorrect_s program tr` `snd a \<noteq> False`
    show "traceCorrect_s program (tr @ [a])"
      by (auto simp add: traceCorrect_s_def) 
  qed
qed 




end