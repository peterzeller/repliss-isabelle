theory replissSem1
imports Main
  "~~/src/HOL/Library/LaTeXsugar"
  "~~/src/HOL/Library/Multiset"
  "~/work/afp/thys/Proof_Strategy_Language/PSL" 
begin

strategy Hammers =  RepeatN ( Ors [Hammer, Defer]  )

abbreviation todo ("???") where "??? \<equiv> undefined"

abbreviation eqsome :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<triangleq>" 69) where
 "x \<triangleq> y \<equiv> x = Some y"

typedecl session
typedecl localState
typedecl uniqueId

typedecl any
definition uniqueIds :: "any \<Rightarrow> uniqueId set" where 
"uniqueIds = ???"

definition 
"uniqueIdsInList xs = (\<Union>x\<in>set xs. uniqueIds x)"


typedecl operation



typedecl txid
typedecl callId

datatype call = Call operation (call_args:"any list") (call_res:"any")

datatype localAction =
    LocalStep localState
  | BeginAtomic localState
  | EndAtomic localState
  | NewId "uniqueId \<Rightarrow> localState"
  | DbOperation operation "any list" "any \<Rightarrow> localState"
  | Return any

typedecl procedureName
type_synonym procedureImpl = "localState \<Rightarrow> localAction"

datatype transactionStatus = Uncommited | Commited 

record operationContext = 
  calls :: "callId \<rightharpoonup> call"
  happensBefore :: "callId rel"

record invariantContext = 
  i_calls :: "callId \<rightharpoonup> call"
  i_happensBefore :: "callId rel"
  i_visibleCalls :: "callId set"
  i_callOrigin :: "callId \<rightharpoonup> txid"
  i_knownIds :: "uniqueId set"
  i_invocationOp :: "session \<rightharpoonup> (procedureName \<times> any list)"
  i_invocationRes :: "session \<rightharpoonup> any"

record prog =
  querySpec :: "operation \<Rightarrow> any list \<Rightarrow> operationContext \<Rightarrow> any \<Rightarrow> bool"
  procedure :: "procedureName \<Rightarrow> any list \<rightharpoonup> (localState \<times> procedureImpl)"
  invariant :: "invariantContext \<Rightarrow> bool"

record state = operationContext +
  prog :: prog
  callOrigin :: "callId \<rightharpoonup> txid"
  generatedIds :: "uniqueId set"
  knownIds :: "uniqueId set"
  invocationOp :: "session \<rightharpoonup> (procedureName \<times> any list)"
  invocationRes :: "session \<rightharpoonup> any"
  localState :: "session \<rightharpoonup> localState"
  currentProc :: "session \<rightharpoonup> procedureImpl"
  visibleCalls :: "session \<rightharpoonup> callId set"
  currentTransaction :: "session \<rightharpoonup> txid"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

lemma state_ext: "((x::state) = y) \<longleftrightarrow> (
    calls x = calls y
  \<and> happensBefore x = happensBefore y
  \<and> prog x = prog y
  \<and> localState x = localState y
  \<and> currentProc x = currentProc y
  \<and> visibleCalls x = visibleCalls y
  \<and> currentTransaction x = currentTransaction y
  \<and> transactionStatus x = transactionStatus y
  \<and> callOrigin x = callOrigin y
  \<and> generatedIds x = generatedIds y
  \<and> knownIds x = knownIds y
  \<and> invocationOp x = invocationOp y
  \<and> invocationRes x = invocationRes y
)"
by auto

thm state.defs  

definition restrict_relation :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "|r"  110)
where "r |r A \<equiv> r Int (A \<times> A)"
  
term restrict_map

abbreviation "emptyOperationContext \<equiv> \<lparr> calls = empty, happensBefore = {}\<rparr>"

definition "getContext" where
"getContext state s = (case visibleCalls state s of
      None \<Rightarrow> emptyOperationContext
    | Some vis => \<lparr>
        calls = calls state |` vis,
        happensBefore = happensBefore state |r vis
      \<rparr>
  )"

abbreviation "emptyInvariantContext \<equiv> \<lparr>
        i_calls = empty,
        i_happensBefore = {},
        i_visibleCalls = {},
        i_callOrigin  = empty,
        i_knownIds = {},
        i_invocationOp = empty,
        i_invocationRes = empty
\<rparr>"


definition "commitedCalls state \<equiv> {c | c tx. callOrigin state c \<triangleq> tx \<and> transactionStatus state tx \<triangleq> Commited }"

definition invContext where
"invContext state s = \<lparr>
        i_calls = calls state |` commitedCalls state , 
        i_happensBefore = happensBefore state |r commitedCalls state , 
        i_visibleCalls = case visibleCalls state s of None \<Rightarrow> {} | Some vis \<Rightarrow> vis,
        i_callOrigin  = callOrigin state |` commitedCalls state,
        i_knownIds = knownIds state,
        i_invocationOp = invocationOp state,
        i_invocationRes = invocationRes state
      \<rparr>"

  
lemma invariantContext_eqI: "\<lbrakk>
i_calls x = i_calls y;
i_happensBefore x = i_happensBefore y;
i_visibleCalls x = i_visibleCalls y;
i_callOrigin x = i_callOrigin y;
i_knownIds x = i_knownIds y;
i_invocationOp x = i_invocationOp y;
i_invocationRes x = i_invocationRes y
\<rbrakk> \<Longrightarrow> x = (y::invariantContext)"
by auto


(*
abbreviation isUndef :: "'a option \<Rightarrow> bool" ("_ = \<bottom>" [0]60) where
 "x = \<bottom> \<equiv> x = None"
*)
  


abbreviation "commitedTransactions C \<equiv> {txn. transactionStatus C txn \<triangleq> Commited }"
  
inductive_set downwardsClosure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"  (infixr "\<down>" 100) for S R  where 
 downwardsClosure_refl[simp]: 
 "x\<in>S \<Longrightarrow> x \<in> S\<down>R"
| downwardsClosure_include:
  "\<lbrakk>y \<in> S\<down>R; (x,y)\<in>R\<rbrakk> \<Longrightarrow> x\<in> S\<down>R"


lemma dc_def2: "(S\<down>R) = S \<union> {x | x y. y\<in>S \<and> (x,y) \<in> R\<^sup>+}"
proof auto
  show "\<lbrakk>x \<in> S \<down> R; x \<notin> S\<rbrakk> \<Longrightarrow> \<exists>y. y \<in> S \<and> (x, y) \<in> R\<^sup>+" for x
    proof (induct rule: downwardsClosure.induct)
      case (downwardsClosure_refl x)
        from local.downwardsClosure_refl
        have False by simp 
        thus ?case ..
      next case (downwardsClosure_include y x)
        show "?case"
        proof (cases "y \<in> S")
          case True
            thus "\<exists>y. y \<in> S \<and> (x, y) \<in> R\<^sup>+"
            using downwardsClosure_include.hyps(3) trancl.r_into_trancl by blast            
          next case False
            with local.downwardsClosure_include(2) 
            obtain z where "z \<in> S" and "(y, z) \<in> R\<^sup>+" by auto
            thus "\<exists>y. y \<in> S \<and> (x, y) \<in> R\<^sup>+"
            using downwardsClosure_include.hyps(3) by auto 
        qed
    qed
  next
  show "\<lbrakk>(x, y) \<in> R\<^sup>+; y \<in> S\<rbrakk> \<Longrightarrow> x \<in> S \<down> R" for x y
    apply (induct rule: converse_trancl_induct)
    apply (meson downwardsClosure.simps)
    by (simp add: downwardsClosure.downwardsClosure_include)
qed

(* we can calculate downwards closure by using the transitive closure and filtering *)
lemma dc_def3[code]: "(S\<down>R) = S \<union> fst ` Set.filter (\<lambda>(x,y). y\<in>S) (R\<^sup>+)"
apply (subst dc_def2)
apply auto
by (metis case_prodI fst_conv image_iff member_filter)

lemma downwardsClosure_subset:
"S \<down> R \<subseteq> S \<union> fst ` R"
apply (auto simp add: dc_def3)
using image_iff tranclD by fastforce

lemma downwardsClosure_subset2:
"x \<in> S \<down> R \<Longrightarrow> x \<in> S \<union> fst ` R"
  by (meson downwardsClosure_subset subsetCE)


  
(* example *)  
lemma "{5::int, 9} \<down> {(3,5),(2,3),(4,9)} = {2,3,4,5,9}"
apply eval
done

datatype action =
    ALocal
  | ANewId uniqueId
  | ABeginAtomic txid
  | AEndAtomic
  | ADbOp callId operation "any list" any
  | APull "txid set"
  | AInvoc procedureName "any list"
  | AReturn any
  | AFail  
  | AInvcheck bool

inductive step :: "state \<Rightarrow> (session \<times> action) \<Rightarrow> state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>" 60) where
  local: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = LocalStep ls' 
   \<rbrakk> \<Longrightarrow> C ~~ (s, ALocal)  \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls') \<rparr>)"
| newId: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = NewId ls';
   uid \<notin> generatedIds C
   \<rbrakk> \<Longrightarrow> C ~~ (s, ANewId uid) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls' uid) \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTransaction C s = None;
   t \<notin> dom (transactionStatus C)
   \<rbrakk> \<Longrightarrow> C ~~ (s, ABeginAtomic t) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C)(s \<mapsto> t),
                transactionStatus := (transactionStatus C)(t \<mapsto> Uncommited) \<rparr>)"
| endAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTransaction C s \<triangleq> t
   \<rbrakk> \<Longrightarrow> C ~~ (s, AEndAtomic) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C)(s := None),
                transactionStatus := (transactionStatus C)(t \<mapsto> Commited) \<rparr>)"
| dbop: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = DbOperation Op args ls';
   currentTransaction C s \<triangleq> t;
   c \<notin> dom (calls C);
   querySpec (prog C) Op args (getContext C s)  res;
   visibleCalls C s \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  C ~~ (s, ADbOp c Op args res) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls' res), 
                calls := (calls C)(c \<mapsto> Call Op args res ),
                callOrigin := (callOrigin C)(c \<mapsto> t),
                visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore C \<union> vis \<times> {c}  \<rparr>)"                
| pull:
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   (* choose a set of commited transactions to pull in*)
   \<forall>txn\<in>newTxns. transactionStatus C txn \<triangleq> Commited;
   (* pull in calls from the transactions and their dependencies *)
   newCalls = {c. \<exists>txn\<in>newTxns. callOrigin C c \<triangleq> txn }\<down>happensBefore C
   \<rbrakk> \<Longrightarrow>  C ~~ (s, APull newTxns) \<leadsto> (C\<lparr> visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> newCalls)\<rparr>)"                         
| invocation:
  "\<lbrakk>localState C s = None;
   procedure (prog C) procName args \<triangleq> (initialState, impl);
   uniqueIdsInList args \<subseteq> knownIds C;
   s \<notin> dom (invocationOp C)
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvoc procName args) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> initialState),
                 currentProc := (currentProc C)(s \<mapsto> impl),
                 visibleCalls := (visibleCalls C)(s \<mapsto> {}),
                 invocationOp := (invocationOp C)(s \<mapsto> (procName, args)) \<rparr>)"                   
| return:
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = Return res;
   currentTransaction C s = None
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AReturn res) \<leadsto> (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None),
                 invocationRes := (invocationRes C)(s \<mapsto> res) \<rparr>)"                
| fail:
  "      C ~~ (s, AFail) \<leadsto> (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None) \<rparr>)"                  
| invCheck:
  "\<lbrakk>currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   invariant (prog C) (invContext C s) = res
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvcheck res) \<leadsto> C"   

inductive_simps step_simp_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_simps step_simp_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_simps step_simp_ABeginAtomic: "A ~~ (s, ABeginAtomic t) \<leadsto> B "
inductive_simps step_simp_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_simps step_simp_ADbOp: "A ~~ (s, ADbOp c oper args res) \<leadsto> B "
inductive_simps step_simp_APull: "A ~~ (s, APull txns) \<leadsto> B "
inductive_simps step_simp_AInvoc: "A ~~ (s, AInvoc procname args) \<leadsto> B "
inductive_simps step_simp_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_simps step_simp_AFail: "A ~~ (s, AFail) \<leadsto> B "
inductive_simps step_simp_AInvcheck: "A ~~ (s, b) \<leadsto> B "

lemmas step_simps = 
  step_simp_ALocal
  step_simp_ANewId
  step_simp_ABeginAtomic
  step_simp_AEndAtomic
  step_simp_ADbOp
  step_simp_APull
  step_simp_AInvoc
  step_simp_AReturn
  step_simp_AFail
  step_simp_AInvcheck

inductive_cases step_elim_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_cases step_elim_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_cases step_elim_ABeginAtomic: "A ~~ (s, ABeginAtomic t) \<leadsto> B "
inductive_cases step_elim_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_cases step_elim_ADbOp: "A ~~ (s, ADbOp c oper args res) \<leadsto> B "
inductive_cases step_elim_APull: "A ~~ (s, APull txns) \<leadsto> B "
inductive_cases step_elim_AInvoc: "A ~~ (s, AInvoc procname args) \<leadsto> B "
inductive_cases step_elim_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_cases step_elim_AFail: "A ~~ (s, AFail) \<leadsto> B "
inductive_cases step_elim_AInvcheck: "A ~~ (s, b) \<leadsto> B "

lemmas step_elims = 
  step_elim_ALocal
  step_elim_ANewId
  step_elim_ABeginAtomic
  step_elim_AEndAtomic
  step_elim_ADbOp
  step_elim_APull
  step_elim_AInvoc
  step_elim_AReturn
  step_elim_AFail
  step_elim_AInvcheck

inductive steps :: "state \<Rightarrow> (session \<times> action) list \<Rightarrow> state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>*" 60) where         
  steps_refl:
  "S ~~ [] \<leadsto>* S"
| steps_step:
  "\<lbrakk>S ~~ tr \<leadsto>* S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> S ~~ tr@[a] \<leadsto>* S''"


(* with a given trace, the execution is deterministic *)
lemma stepDeterministic:
assumes e1: "S ~~ tr \<leadsto> Sa" 
    and e2: "S ~~ tr \<leadsto> Sb"
shows "Sa = Sb"
using e1 e2 apply (induct rule: step.induct)
apply (erule step.cases; force)+
done


lemma traceDeterministic:
assumes e1: "S ~~ tr \<leadsto>* Sa" 
    and e2: "S ~~ tr \<leadsto>* Sb"
shows "Sa = Sb"
using e1 e2 proof (induct S tr Sa arbitrary: Sb rule: steps.induct)
thm steps.induct
  case (steps_refl S)
  then show ?case
    using steps.cases by fastforce 
next
  case (steps_step S tr S' a S'')
  then show ?case
    by (metis snoc_eq_iff_butlast stepDeterministic steps.cases) 
qed

definition initialState :: "prog \<Rightarrow> state" where
"initialState program \<equiv> \<lparr>
  calls = empty,
  happensBefore = {},
  prog = program,
  callOrigin = empty,
  generatedIds = {},
  knownIds = {},
  invocationOp = empty,
  invocationRes = empty,
  localState = empty,
  currentProc = empty,
  visibleCalls = empty,
  currentTransaction = empty,
  transactionStatus = empty
\<rparr>"

type_synonym trace = "(session\<times>action) list"

definition traceCorrect where
"traceCorrect program trace \<equiv> (\<forall>s. (s, AInvcheck False) \<notin> set trace) \<and> (\<exists>s. initialState program ~~ trace \<leadsto>* s)"

definition programCorrect where
"programCorrect program \<equiv> (\<forall>trace s. (initialState program ~~ trace \<leadsto>* s) \<longrightarrow> traceCorrect program trace)"

definition "isABeginAtomic action = (case action of ABeginAtomic x \<Rightarrow> True | _ \<Rightarrow> False)"

(*
 splits a trace into three parts
  
1. part until first (s, EndAtomic) on different sessions
2. part until and including (s, EndAtomic); same session
3. rest
*)
fun splitTrace :: "session \<Rightarrow> trace \<Rightarrow> (trace \<times> trace \<times> trace)" where
  "splitTrace s [] = ([],[],[])"
| "splitTrace s ((sa, a)#tr) = (
    if s = sa then
      if a = AEndAtomic then
        ([], [(sa,a)], tr)
      else
        let (h, c, t) = splitTrace s tr in
        (h, (sa,a)#c, t)
    else
      let (h, c, t) = splitTrace s tr in
      ((sa,a)#h, c, t)
  )"



lemma splitTrace_complete: 
"splitTrace s tr = (h,c,t) \<Longrightarrow> mset tr= mset h + mset c + mset t"
apply (induct arbitrary: h c t rule: splitTrace.induct)
apply (auto split: if_splits prod.splits)
done

lemma splitTrace_len[simp]: 
assumes a: "splitTrace s tr = (h,c,t)"
shows "length h \<le> length tr"
  and "length c \<le> length tr"
  and "length t \<le> length tr"
using a apply (induct arbitrary: h c t rule: splitTrace.induct)
apply (auto simp add: le_SucI split: if_splits prod.splits)
done

lemma splitTrace_len2[simp]: 
assumes a: "(h,c,t) = splitTrace s tr"
shows "length h \<le> length tr"
  and "length c \<le> length tr"
  and "length t \<le> length tr"
using a by (metis splitTrace_len)+ 

declare splitTrace.simps[simp del]


fun compactTrace :: "session \<Rightarrow> trace \<Rightarrow> trace" where
  compactTrace_empty:
  "compactTrace s [] = []"
| compactTrace_step:
  "compactTrace s ((sa, a)#tr) = (
    if s = sa \<and> isABeginAtomic a then
      let (h, c, t) = splitTrace s tr in
      h @ (sa,a)#c @ compactTrace s t
    else
      (sa, a) # compactTrace s tr
  )"


lemma compactTrace_complete: 
"mset (compactTrace s tr) = mset tr"
apply (induct rule: compactTrace.induct)
apply (auto simp add: splitTrace_complete split: prod.splits)
done

declare compactTrace_step[simp del]

(*
theorem compactTrace_preservesSemantic:
shows "(s_init ~~ tr \<leadsto>* C) \<longleftrightarrow> (s_init ~~ compactTrace s tr \<leadsto>* C)"
proof (induct tr arbitrary: C rule: compactTrace.induct)
  case (1 s)
  then show ?case by simp
next
  case (2 s sa a tr)
(*
    \<lbrakk>s = sa \<and> isABeginAtomic a; ?x = splitTrace s tr; (?xa, ?y) = ?x; (?xb, ?ya) = ?y\<rbrakk> \<Longrightarrow> s_init ~~ ?ya \<leadsto>* ?C = s_init ~~ compactTrace s ?ya \<leadsto>* ?C
    \<not> (s = sa \<and> isABeginAtomic a) \<Longrightarrow> s_init ~~ tr \<leadsto>* ?C = s_init ~~ compactTrace s tr \<leadsto>* ?C
*)
  show ?case 
    apply auto
  sorry
qed
*)  

lemma steps_appendBack:
"(A ~~ tr @ [a] \<leadsto>* C) \<longleftrightarrow> (\<exists>B. (A ~~ tr \<leadsto>* B) \<and> (B ~~ a \<leadsto> C))"
apply auto
apply (metis snoc_eq_iff_butlast steps.cases)
using steps_step by blast


lemma steps_append: 
"(A ~~ tra@trb \<leadsto>* C) \<longleftrightarrow> (\<exists>B. (A ~~ tra \<leadsto>* B) \<and> (B ~~ trb \<leadsto>* C))"
proof (induct trb arbitrary: C rule: rev_induct)
  case Nil
  then show ?case 
    apply simp
    by (metis snoc_eq_iff_butlast steps.cases steps_refl)
next
  case (snoc a trb)
  show ?case
    by (metis (no_types, lifting) append_assoc snoc.hyps steps_appendBack) 
qed

lemma steps_single[simp]: "(A ~~ [a] \<leadsto>* B) \<longleftrightarrow> (A ~~ a \<leadsto> B)"
by (metis append_Nil steps_appendBack steps_refl traceDeterministic)

lemma steps_empty[simp]: "(A ~~ [] \<leadsto>* B) \<longleftrightarrow> (A = B)"
  using steps_refl traceDeterministic by blast


lemma steps_appendFront:
"(A ~~ a# tr \<leadsto>* C) \<longleftrightarrow> (\<exists>B. (A ~~ a \<leadsto> B) \<and> (B ~~ tr \<leadsto>* C))"
proof -
  have "(A ~~ a# tr \<leadsto>* C) 
                     = (A ~~ [a]@tr \<leadsto>* C)" by simp
  moreover have "... = (\<exists>B. (A ~~ [a] \<leadsto>* B) \<and> (B ~~ tr \<leadsto>* C))" by (rule steps_append)
  moreover have "... = (\<exists>B. (A ~~ a \<leadsto> B) \<and> (B ~~ tr \<leadsto>* C))" by (simp add: steps_single)
  ultimately show ?thesis by simp
qed  


definition state_wellFormed :: "state \<Rightarrow> bool" where
"state_wellFormed state \<equiv> \<exists>tr. initialState (prog state) ~~ tr \<leadsto>* state"

lemma step_prog_invariant:
"S ~~ tr \<leadsto>* S' \<Longrightarrow> prog S' = prog S"
apply (induct rule: steps.induct)
apply auto
apply (erule step.cases)
apply auto
done

thm full_nat_induct

lemma wellFormed_induct[consumes 1]:
"\<lbrakk>state_wellFormed s; P (initialState (prog s)); \<And>t a s. \<lbrakk>state_wellFormed t; P t; t ~~ a \<leadsto> s\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P s"
proof (auto simp add: state_wellFormed_def)
  fix tr
  assume a1: "P (initialState (prog s))"
  assume a2: "\<And>t a b s. \<lbrakk>\<exists>tr. initialState (prog t) ~~ tr \<leadsto>* t; P t; t ~~ (a, b) \<leadsto> s\<rbrakk> \<Longrightarrow> P s"
  assume a3: "initialState (prog s) ~~ tr \<leadsto>* s" 
  have "\<lbrakk>S ~~ tr \<leadsto>* s; P (initialState (prog s)); S = initialState (prog s); \<And>t a b. \<lbrakk>\<exists>tr. initialState (prog t) ~~ tr \<leadsto>* t; P t; t ~~ (a, b) \<leadsto> s\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P s" for S tr s
    proof (induct rule: steps.induct)
      case (steps_refl S)                        
      then show ?case by simp
    next
      case (steps_step S tr S' a S'')
      have "P S'"
        apply (rule steps_step(2))
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(1) steps_step.prems(2) apply auto[1]
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(2) apply auto[1]
        using a2 by blast
      then show ?case
        by (metis local.steps_step(3) local.steps_step(5) local.steps_step(6) prod.collapse step_prog_invariant steps.steps_step steps_step.hyps(1)) 
    qed
  thus ?thesis
    using a1 a2 a3 by blast
qed


lemma wellFormed_callOrigin_dom:
assumes a1: "state_wellFormed S"
shows "dom (callOrigin S) = dom (calls S)"
using a1 apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  by blast



lemma wellFormed_visibleCallsSubsetCalls_h:
assumes a1: "state_wellFormed S"
shows "happensBefore S \<subseteq> dom (calls S) \<times> dom (calls S)"
   and "\<And>vis s. visibleCalls S s \<triangleq> vis \<Longrightarrow> state_wellFormed S \<Longrightarrow> vis \<subseteq> dom (calls S)" 
using a1 apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  apply blast
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
  using wellFormed_callOrigin_dom downwardsClosure_subset2 apply fastforce
  apply blast
  apply blast
  apply blast
  apply blast
  apply blast
done  
  

    
lemma wellFormed_visibleCallsSubsetCalls:
assumes a1: "state_wellFormed A"
    and a2: "visibleCalls A s \<triangleq> vis"
shows "vis \<subseteq> dom (calls A)"
  using a1 a2 wellFormed_visibleCallsSubsetCalls_h(2) by auto

lemma wellFormed_currentTransaction_unique_h:
assumes a1: "state_wellFormed S"
shows "\<forall>sa sb t. currentTransaction S sa \<triangleq> t \<longrightarrow> currentTransaction S sb \<triangleq> t \<longrightarrow>  sa = sb"
  and "\<forall>sa t. currentTransaction S sa \<triangleq> t \<longrightarrow> transactionStatus S t \<triangleq> Uncommited"
using a1 apply (induct  rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
apply (erule step.cases)
apply (auto split: if_splits)
done   
  
lemmas wellFormed_currentTransaction_unique = wellFormed_currentTransaction_unique_h(1)[rule_format]
lemmas wellFormed_currentTransactionUncommited[simp] = wellFormed_currentTransaction_unique_h(2)[rule_format]
    
  
  

definition commutativeS :: "state \<Rightarrow> session \<times> action \<Rightarrow> session \<times> action \<Rightarrow> bool" where
"commutativeS s a b \<equiv> (\<forall>t. ((s ~~ [a,b] \<leadsto>*  t) \<longleftrightarrow> (s ~~ [b,a] \<leadsto>* t)))"


definition "precondition a C \<equiv> \<exists>C'. C ~~ a \<leadsto> C'"

lemma usePrecondition: "precondition a C \<Longrightarrow> \<exists>C'. C ~~ a \<leadsto> C'"
apply (simp add: precondition_def)
done

lemma usePrecondition2: "precondition a C \<Longrightarrow> (\<And>C'. C ~~ a \<leadsto> C' \<Longrightarrow> P C') \<Longrightarrow> \<exists>C'. (C ~~ a \<leadsto> C') \<and> P C'"
  using usePrecondition by blast


lemma existsAndH: "P x \<Longrightarrow> Q x \<Longrightarrow>   \<exists>x. P x \<and> Q x"
by auto

lemma preconditionI[simp]: "\<lbrakk>s ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> precondition a s"
by (auto simp add: precondition_def)

lemma show_commutativeS[case_names preAB preBA commute ]: 
assumes a1:  "\<And>s1 s2. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ b \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ a \<leadsto> s2)" 
    and a2:  "\<And>s1 s2. \<lbrakk>s ~~ b \<leadsto> s1; s1 ~~ a \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ a \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ b \<leadsto> s2)" 
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
shows "commutativeS s a b"
apply (auto simp add: commutativeS_def  steps_appendFront)
  using a1 a4 apply blast
  using a2 a4 by blast

lemma show_commutativeS_pres[case_names preBfront preAfront preAback preBback commute ]: 
assumes a1:  "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s1\<rbrakk> \<Longrightarrow> precondition b s"
    and a1': "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s1\<rbrakk> \<Longrightarrow> precondition a s"
    and a2:  "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s\<rbrakk> \<Longrightarrow> precondition a s1"
    and a2': "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s\<rbrakk> \<Longrightarrow> precondition b s1"
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
shows "commutativeS s a b"
apply (auto simp add: commutativeS_def precondition_def steps_appendFront)
apply (rule usePrecondition2)
  using a1 precondition_def apply blast 
  apply (frule a2)
  apply simp
  using a4 usePrecondition apply blast
apply (rule usePrecondition2)
  using a1' precondition_def apply blast 
  apply (frule a2')
  apply simp
  using a4 usePrecondition apply blast 
done  



lemma precondition_alocal:
"precondition (s, ALocal) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = LocalStep ls')"
apply (auto simp add: precondition_def intro: step.intros elim: step_elims)
done

lemma precondition_newid:
"precondition (s, ANewId uid) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = NewId ls' \<and> uid \<notin> generatedIds C)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_beginAtomic:
"precondition (s, ABeginAtomic tx) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = BeginAtomic ls' \<and> currentTransaction C s = None \<and> transactionStatus C tx = None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_endAtomic:
"precondition (s, AEndAtomic) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = EndAtomic ls' \<and> currentTransaction C s \<noteq> None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_invoc:
"precondition (s, AInvoc procName args) C = (\<exists>initialState impl. s \<notin> dom (invocationOp C) \<and> localState C s = None \<and> procedure (prog C) procName args \<triangleq> (initialState, impl) \<and> uniqueIdsInList args \<subseteq> knownIds C)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_dbop:
"precondition (s, ADbOp c operation args res) C = (\<exists>ls f ls' t vis. calls C c = None \<and> localState C s \<triangleq> ls 
    \<and> currentProc C s \<triangleq> f \<and> f ls = DbOperation operation args ls' \<and> currentTransaction C s \<triangleq> t \<and> querySpec (prog C) operation args (getContext C s) res \<and> visibleCalls C s \<triangleq> vis)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_pull:
"precondition (s, APull txs) C = (\<exists>ls vis. localState C s \<triangleq> ls \<and> currentTransaction C s = None \<and> visibleCalls C s \<triangleq> vis \<and> (\<forall>txn\<in>txs. transactionStatus C txn \<triangleq> Commited))"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done


lemma precondition_return:
"precondition (s, AReturn res) C = (\<exists>ls f. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = Return res \<and> currentTransaction C s = None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_fail:
"precondition (s, AFail) C = True" (* failures occur anywhere and anytime ;) *)
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_invcheck:
"precondition (s, AInvcheck b) C = (\<exists>vis. currentTransaction C s = None \<and> visibleCalls C s \<triangleq> vis \<and> invariant (prog C) (invContext C s) = b)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

(*
  | AInvcheck bool
*)



lemma step_existsH:
"\<lbrakk>precondition a A; \<And>B. A ~~ a \<leadsto> B \<Longrightarrow> P B \<rbrakk> \<Longrightarrow> \<exists>B. (A ~~ a \<leadsto> B) \<and> P B"
  using usePrecondition by blast

lemma unchangedInTransaction:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
shows
    "localState A sb = localState B sb"
 and "currentProc A sb = currentProc B sb"
 and "currentTransaction A sb = currentTransaction B sb"
 and "visibleCalls A sb = visibleCalls B sb"
 and "invocationOp A sb = invocationOp B sb"
 and "invocationRes A sb = invocationRes B sb"
 and "knownIds A = knownIds B"
apply (case_tac a)
using exec apply (auto simp add: differentSessions[symmetric] elim!: step_elims)
done

lemma getContext_updateLocal[simp]:
"getContext (A\<lparr>localState := x\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_currentTransaction[simp]:
"getContext (A\<lparr>currentTransaction := x\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_transactionStatus[simp]:
"getContext (A\<lparr>transactionStatus := x\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_happensBefore:
"getContext (A\<lparr>happensBefore := hb\<rparr>) s = (
    case visibleCalls A s of 
      None \<Rightarrow> emptyOperationContext 
    | Some vis \<Rightarrow> \<lparr>calls = calls A |` vis, happensBefore = hb |r vis\<rparr>)"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_invocationOp[simp]:
"getContext (A\<lparr>invocationOp := x\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_visibleCalls_other[simp]:
"s\<noteq>sa \<Longrightarrow> visibleCalls A = Vis \<Longrightarrow> getContext (A\<lparr>visibleCalls := Vis(sa := x)\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_visibleCalls_other2[simp]:
"sa\<noteq>s \<Longrightarrow> getContext (A\<lparr>visibleCalls := (visibleCalls A)(sa := x)\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma getContext_currentProc[simp]:
"getContext (A\<lparr>currentProc := x\<rparr>) s = getContext A s"
apply (auto simp add: getContext_def split: option.splits)
done

-- "getContext is not changed by actions in other transactions"
lemma unchangedInTransaction_getContext:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
shows
    "getContext A sb = getContext B sb"
proof (cases a)
  case ALocal
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ANewId x2)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ABeginAtomic x3)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AEndAtomic
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ADbOp callId operation args res)
  from this
  obtain ls f ls' vis 
    where 1: "localState A sa \<triangleq> ls"
      and 2: "currentProc A sa \<triangleq> f"
      and 3: "f ls = DbOperation operation args ls'"
      and 4: "querySpec (prog A) operation args (getContext A sa) res"
      and 5: "visibleCalls A sa \<triangleq> vis"
      and 6: "B = A\<lparr>localState := localState A(sa \<mapsto> ls' res), calls := calls A(callId \<mapsto> Call operation args res), callOrigin := callOrigin A(callId \<mapsto> tx), visibleCalls := visibleCalls A(sa \<mapsto> {callId} \<union> vis),
                happensBefore := happensBefore A \<union> vis \<times> {callId}\<rparr>"
    apply atomize_elim
    using exec apply (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
    done
  have case1: "getContext B sb = getContext A sb" if "visibleCalls A sb = None"
    apply (auto simp add: that getContext_def split: option.splits)
    using aIsInTransaction differentSessions exec that unchangedInTransaction(4) by fastforce+
    
  have case2: "getContext B sb = getContext A sb" if visi_def[simp]: "visibleCalls A sb \<triangleq> visi" for visi
  proof -
    from visi_def
    have [simp]: "visibleCalls B sb \<triangleq> visi"
      using aIsInTransaction differentSessions exec unchangedInTransaction(4) by fastforce
      
    hence "visi \<subseteq> dom (calls A)"  
      using visibleCalls_inv  using visi_def by blast 
    show "getContext B sb = getContext A sb"
      apply (simp add:  getContext_def split: option.splits)
      proof
        have "(calls B |` visi) c = (calls A |` visi) c" for c
          apply (auto simp add: restrict_map_def 6)
          by (smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD exec step_elim_ADbOp)
          
        thus "calls B |` visi = calls A |` visi" ..
      next
        show "happensBefore B |r visi = happensBefore A |r visi"
          apply (auto simp add: restrict_relation_def 6)
          by (smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD exec step_elim_ADbOp)
      qed    
    qed 
  from case1 case2 show ?thesis by force
next
  case (APull x6)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvoc x71 x72)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AReturn x8)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AFail
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvcheck x10)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
qed


lemma invContext_updateLocal[simp]:
"invContext (A\<lparr>localState := x\<rparr>) s = invContext A s"
apply (auto simp add: invContext_def commitedCalls_def split: option.splits)
done

lemma invContext_currentTransaction[simp]:
"invContext (A\<lparr>currentTransaction := x\<rparr>)s = invContext A s"
apply (auto simp add: invContext_def commitedCalls_def split: option.splits)
done


lemma invContext_visibleCalls_other[simp]:
"s\<noteq>sa \<Longrightarrow> visibleCalls A = Vis \<Longrightarrow> invContext (A\<lparr>visibleCalls := Vis(sa := x)\<rparr>) s = invContext A s"
apply (auto simp add: invContext_def  commitedCalls_def split: option.splits)
done

lemma invContext_currentProc[simp]:
"invContext (A\<lparr>currentProc := x\<rparr>) s = invContext A s"
apply (auto simp add: invContext_def  commitedCalls_def split: option.splits)
done


-- "invcontext is not changed by actions in other transactions"
lemma unchangedInTransaction_getInvContext:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and aIsInInvoc: "localState A sa \<triangleq> lsa"
    and txUncommited[simp]: "transactionStatus A tx \<triangleq> Uncommited" 
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    and origin_inv: "dom (callOrigin A) = dom (calls A)"
shows
    "invContext A sb = invContext B sb"
proof (cases a)
  case ALocal
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ANewId x2)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ABeginAtomic x3)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AEndAtomic
  then show ?thesis
    using aIsNotCommit by blast  
next
  case (ADbOp callId operation args res)
  with exec obtain ls f ls' vis
       where 1: "a = ADbOp callId operation args res"
         and B_def: "B = A\<lparr>localState := localState A(sa \<mapsto> ls' res), 
                calls := calls A(callId \<mapsto> Call operation args res), callOrigin := callOrigin A(callId \<mapsto> tx), visibleCalls := visibleCalls A(sa \<mapsto> {callId} \<union> vis),
                happensBefore := happensBefore A \<union> vis \<times> {callId}\<rparr>"
         and 3: "localState A sa \<triangleq> ls"
         and 4: "currentProc A sa \<triangleq> f"
         and 5: "f ls = DbOperation operation args ls'"
         and 6: "querySpec (prog A) operation args (getContext A sa) res"
         and 7: "visibleCalls A sa \<triangleq> vis"
         and 8: "callId \<notin> dom (calls A)"
         apply atomize_elim
        using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
  have commitedSame: "commitedCalls B = commitedCalls A"        
    apply (auto simp add: commitedCalls_def B_def)
    using "8" origin_inv by auto
  
  have commitedCallsSame: "\<And>x. x \<in> commitedCalls A \<Longrightarrow> calls A x = calls B x"
    apply (auto simp add: B_def)
    using "8" commitedCalls_def origin_inv by fastforce
  
  have [simp]: "callId \<notin> commitedCalls A"
    by (smt "8" commitedCalls_def domI mem_Collect_eq origin_inv) 
    
        
  show ?thesis 
    proof (rule invariantContext_eqI)
      show "i_calls (invContext A sb) = i_calls (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        done
      show "i_happensBefore (invContext A sb) = i_happensBefore (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: restrict_relation_def B_def)
        done
        
      show "i_visibleCalls (invContext A sb) = i_visibleCalls (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def differentSessions[symmetric] split: if_splits option.splits)
        done
      show "i_callOrigin (invContext A sb) = i_callOrigin (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
        
      show "i_knownIds (invContext A sb) = i_knownIds (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
      show "i_invocationOp (invContext A sb) = i_invocationOp (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
      show "i_invocationRes (invContext A sb) = i_invocationRes (invContext B sb)"
        apply (auto simp add: invContext_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
    qed
    
  
next
  case (APull x6)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvoc x71 x72)
  then show ?thesis  using exec 
    by (auto simp add: aIsInTransaction aIsInInvoc differentSessions[symmetric] elim!: step_elims split: option.splits)
    
next
  case (AReturn x8)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AFail
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvcheck x10)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
qed


lemma generatedIds_mono:
"\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> generatedIds A \<subseteq> generatedIds B"
apply (erule step.cases, auto)
done

lemma generatedIds_mono2:
"\<lbrakk>x\<in>generatedIds A; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> x\<in>generatedIds B"
  using generatedIds_mono by blast


lemma transactionStatus_mono:
"\<lbrakk>transactionStatus B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> transactionStatus A tx = None"
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma transactionStatus_mono2:
"\<lbrakk>transactionStatus B tx \<triangleq> Commited; A ~~ a \<leadsto> B; snd a\<noteq>AEndAtomic\<rbrakk> \<Longrightarrow> transactionStatus A tx \<triangleq> Commited"
apply (erule step.cases)
apply (auto split: if_splits)
done


lemma calls_mono:
"\<lbrakk>calls B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> calls A tx = None"
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma prog_inv:
"\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> prog B = prog A"
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma getContext_unchanged[simp]:
shows  "getContext (C\<lparr>invocationRes := x1\<rparr>) s = getContext C s"
and "getContext (C\<lparr>callOrigin := x2\<rparr>) s = getContext C s"
and "getContext (C\<lparr>generatedIds := x3\<rparr>) s = getContext C s"
and "getContext (C\<lparr>knownIds := x4\<rparr>) s = getContext C s"
and "getContext (C\<lparr>invocationOp := x5\<rparr>) s = getContext C s"
and "getContext (C\<lparr>invocationRes := x6\<rparr>) s = getContext C s"
and "getContext (C\<lparr>localState := x7\<rparr>) s = getContext C s"
and "getContext (C\<lparr>currentProc := x8\<rparr>) s = getContext C s"
and "getContext (C\<lparr>currentTransaction := x9\<rparr>) s = getContext C s"
and "getContext (C\<lparr>transactionStatus := x10\<rparr>) s = getContext C s"
apply (auto simp add: getContext_def split: option.splits)
done

lemma commitedCalls_unchanged[simp]:
shows  "commitedCalls (C\<lparr>invocationRes := x1\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>generatedIds := x3\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>knownIds := x4\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>invocationOp := x5\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>invocationRes := x6\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>localState := x7\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>currentProc := x8\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>currentTransaction := x9\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>happensBefore := x10\<rparr>) = commitedCalls C"
and "commitedCalls (C\<lparr>visibleCalls := x11\<rparr>) = commitedCalls C"
apply (auto simp add: commitedCalls_def split: option.splits)
done  


lemma commitedCalls_unchanged_callOrigin:
assumes a1: "transactionStatus S t \<triangleq> Uncommited"
    and a2: "X = callOrigin S"
    and a3: "calls S c = None"
    and a4: "state_wellFormed S"
shows "commitedCalls (S\<lparr>callOrigin := X(c \<mapsto> t)\<rparr>) = commitedCalls S"
proof -
  from a3 a4
  have origin[simp]: "callOrigin S c = None"
    using wellFormed_callOrigin_dom by force
  
  
  show "?thesis"
    by (auto simp add: a1 a2 commitedCalls_def split: option.splits)
qed      
  
lemma commitedCalls_unchanged_callOrigin2[simp]:
assumes a1: "transactionStatus S t \<triangleq> Uncommited"
    and a2: "X = callOrigin S"
    and a3: "callOrigin S c = None"
shows "commitedCalls (S\<lparr>callOrigin := X(c \<mapsto> t)\<rparr>) = commitedCalls S"  
using a1 a2 a3 by (auto simp add: commitedCalls_def)
  
lemma commutativePreservesPrecondition:
assumes preconditionHolds: "precondition (sb,b) B"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommited: "transactionStatus A tx \<triangleq> Uncommited"
    and aIsInLocal: "localState A sa \<triangleq> lsa"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
shows "precondition (sb,b) A"
proof -
  
  have origin_inv: "dom (callOrigin A) = dom (calls A)"
    by (simp add: wellFormed wellFormed_callOrigin_dom)
  
  have visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    by (simp add: wellFormed wellFormed_visibleCallsSubsetCalls_h(2))
  

show ?thesis
proof (cases b)
  case ALocal
  show ?thesis using precondition_alocal unchangedInTransaction
    by (metis ALocal aIsInTransaction differentSessions exec preconditionHolds) 
    
next
  case (ANewId x2)
  with preconditionHolds
  obtain ls f ls' 
    where 1: "localState B sb \<triangleq> ls" 
      and 2: "currentProc B sb \<triangleq> f" 
      and 3: "x2 \<notin> generatedIds B" 
      and 4: "f ls = NewId ls'"
    by (auto simp add: precondition_newid)
  have 5: "x2 \<notin> generatedIds A"
    using 3 exec generatedIds_mono2 by blast
  thus ?thesis
    by (metis "1" "2" "4" ANewId aIsInTransaction differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
next
  case (ABeginAtomic tx)
  with preconditionHolds obtain ls f ls' 
      where 1: "localState B sb \<triangleq> ls"
        and 2: "currentProc B sb \<triangleq> f"
        and 3: "f ls = BeginAtomic ls'"
        and 4: "currentTransaction B sb = None"
        and 5: "transactionStatus B tx = None"
    by (auto simp add: precondition_beginAtomic)
  moreover have "transactionStatus A tx = None" using transactionStatus_mono 5 exec by blast 
  ultimately show ?thesis using unchangedInTransaction
    by (metis ABeginAtomic aIsInTransaction differentSessions exec precondition_beginAtomic) 
next
  case AEndAtomic
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3))
next
  case (ADbOp callId operation args res)
  with preconditionHolds obtain ls f ls' vis t 
      where 1: "calls B callId = None"
        and 2: "localState B sb \<triangleq> ls"
        and 3: "currentProc B sb \<triangleq> f"
        and 4: "f ls = DbOperation operation args ls'"
        and 5: "currentTransaction B sb \<triangleq> t"
        and 6: "querySpec (prog B) operation args (getContext B sb) res"
        and 7: "visibleCalls B sb \<triangleq> vis"
    by (auto simp add: precondition_dbop)
  moreover have "calls A callId = None"
    using "1" calls_mono exec by blast   
  moreover have "prog B = prog A"
    using exec prog_inv by auto  
  moreover have "getContext B sb = getContext A sb"
    by (metis aIsInTransaction differentSessions exec unchangedInTransaction_getContext visibleCalls_inv) 
  ultimately show ?thesis  using unchangedInTransaction
    by (smt ADbOp aIsInTransaction differentSessions exec precondition_dbop)
    
next
  case (APull txns) 
  with preconditionHolds obtain ls vis
      where 1: "localState B sb \<triangleq> ls"
      and 2: "currentTransaction B sb = None"
      and 3: "visibleCalls B sb \<triangleq> vis"
      and 4: "\<forall>txn\<in>txns. transactionStatus B txn \<triangleq> Commited"
    by (auto simp add: precondition_pull)
  
  then show ?thesis
    by (metis APull aIsInTransaction aIsNotCommit differentSessions exec precondition_pull snd_conv transactionStatus_mono2 unchangedInTransaction(1) unchangedInTransaction(3) unchangedInTransaction(4))  
next
  case (AInvoc procName args)
  with preconditionHolds obtain initialState impl
      where "sb \<notin> dom (invocationOp B)"
      and "localState B sb = None"
      and "procedure (prog B) procName args \<triangleq> (initialState, impl)"
      and "uniqueIdsInList args \<subseteq> knownIds B"
    by (auto simp add: precondition_invoc)
  moreover have "sb \<notin> dom (invocationOp A)"
    by (metis \<open>sb \<notin> dom (invocationOp B)\<close> aIsInTransaction differentSessions dom_def exec mem_Collect_eq unchangedInTransaction(5))  
    
  ultimately show ?thesis using unchangedInTransaction
    by (metis (mono_tags, lifting) AInvoc aIsInTransaction differentSessions exec precondition_invoc prog_inv) 
next
  case (AReturn x8)
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case AFail
  then show ?thesis
    using precondition_fail by blast 
next
  case (AInvcheck b)
  with preconditionHolds obtain vis 
     where 1: "currentTransaction B sb = None"
       and 2: "visibleCalls B sb \<triangleq> vis"
       and 3: "invariant (prog B) (invContext B sb) = b"
    by (auto simp add: precondition_invcheck)
  
    
  moreover have "invContext A sb = invContext B sb"
    using unchangedInTransaction_getInvContext aIsInLocal aIsInTransaction aIsNotCommit differentSessions exec origin_inv txIsUncommited visibleCalls_inv by blast 

    ultimately show ?thesis  using unchangedInTransaction
    by (metis AInvcheck aIsInTransaction differentSessions exec precondition_invcheck prog_inv)
    
qed
qed

 (*
\<And>ls f ls' t vis visa.
       a = AInvcheck True \<Longrightarrow>
       currentTransaction S sb = None \<Longrightarrow>
       visibleCalls S sb \<triangleq> visa \<Longrightarrow>
       localState S sa \<triangleq> ls \<Longrightarrow>
       currentProc S sa \<triangleq> f \<Longrightarrow>
       f ls = DbOperation operation args ls' \<Longrightarrow>
       currentTransaction S sa \<triangleq> t \<Longrightarrow>
       querySpec (prog S) operation args (getContext S sa) res \<Longrightarrow>
       visibleCalls S sa \<triangleq> vis \<Longrightarrow>
       x10 \<Longrightarrow> invariant (prog S)
                (invContext
                  (S\<lparr>
  localState := localState S(sa \<mapsto> ls' res), 
    calls := calls S(c \<mapsto> Call operation args res), 
  
callOrigin := callOrigin S(c \<mapsto> t),
visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis), 
happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
                  sb) \<Longrightarrow>
               calls S c = None \<Longrightarrow> invariant (prog S) (invContext S sb)


*)
lemma invContext_unchanged_localState[simp]:
shows "invContext (S\<lparr> localState := X \<rparr>) s
     = invContext S s"  
  by (auto simp add: invContext_def) 
  
lemma invContext_unchanged_happensBefore[simp]:
assumes a1: "hbOld = happensBefore S"
    and a2: "calls S c = None"
    and a3: "state_wellFormed S" 
shows "invContext (S\<lparr> happensBefore := hbOld \<union> vis \<times> {c} \<rparr>) s
     = invContext S s"
using a1 apply (auto simp add: invContext_def)  
  apply (auto simp add: restrict_relation_def)
  by (smt a2 a3 commitedCalls_def domIff mem_Collect_eq option.simps(3) wellFormed_callOrigin_dom)

lemma commitedCalls_uncommitedNotIn:
assumes "callOrigin S c \<triangleq> t"
   and "transactionStatus S t \<triangleq> Uncommited"
shows  "c \<notin> commitedCalls S"
using assms by (auto simp add: commitedCalls_def)
    
lemma invContext_unchanged_happensBefore2[simp]:
assumes a1: "hbOld = happensBefore S"
    and a2: "callOrigin S c \<triangleq> t"
    and a4: "transactionStatus S t \<triangleq> Uncommited"
shows "invContext (S\<lparr> happensBefore := hbOld \<union> vis \<times> {c} \<rparr>) s
     = invContext S s"
using a1 apply (auto simp add: invContext_def)  
  apply (auto simp add: restrict_relation_def)
  using a2 a4 commitedCalls_uncommitedNotIn by blast
    
lemma invContext_changeVisibleCalls:
shows "invContext (S\<lparr> visibleCalls := X \<rparr>) s
     = (invContext S s)\<lparr>i_visibleCalls := case X s of None \<Rightarrow> {} | Some vis \<Rightarrow> vis\<rparr>"
by (auto simp add: invContext_def split: option.splits)  

lemma invContext_unchanged_visibleCalls[simp]:
assumes "X s = visibleCalls S s"
shows "invContext (S\<lparr> visibleCalls := X \<rparr>) s
     = (invContext S s)"
using assms by (auto simp add: invContext_def split: option.splits) 
  
lemma wellFormed_commitedCallsExist:
assumes a1: "calls S c = None"
    and a2: "state_wellFormed S"
shows "c \<notin> commitedCalls S"
using a1 a2
  by (smt commitedCalls_def domIff mem_Collect_eq option.simps(3) wellFormed_callOrigin_dom) 
    
lemma invContext_unchanged_callOrigin:
assumes a1: "transactionStatus S t \<triangleq> Uncommited"
    and a2: "X = callOrigin S"
    and a3: "calls S c = None"
    and a4: "state_wellFormed S"
shows "invContext (S\<lparr> callOrigin := X(c \<mapsto> t) \<rparr>) s
     = (invContext S s)"
apply (auto simp add: invContext_def split: option.splits)
apply (auto simp add: a1 a2 a3 a4 commitedCalls_unchanged_callOrigin)
using a3 a4 wellFormed_commitedCallsExist by blast 

lemma noOrigin_notCommited[simp]:
  "callOrigin S c = None \<Longrightarrow> c \<notin> commitedCalls S"  
by (auto simp add: commitedCalls_def)
  
lemma invContext_unchanged_callOrigin2:
assumes a1: "transactionStatus S t \<triangleq> Uncommited"
    and a2: "X = callOrigin S"
    and a4: "callOrigin S c = None"
shows "invContext (S\<lparr> callOrigin := X(c \<mapsto> t) \<rparr>) s
     = (invContext S s)"
apply (auto simp add: invContext_def split: option.splits)
apply (simp add: a1 a2  a4)
apply (simp add: a1 a2  a4)
apply (simp add: a1 a2  a4)
apply (subst (asm) commitedCalls_unchanged_callOrigin2)
apply (simp add: a1)
apply (simp add: a2)
apply (simp add: a4)
using a4 noOrigin_notCommited apply blast
apply (simp add: a1 a2  a4)+
done
  

lemma commitedCalls_unchanged_calls[simp]:
shows "commitedCalls (S\<lparr>calls := X(c \<mapsto> Y)\<rparr>)
    =  commitedCalls S"
apply (auto simp add: commitedCalls_def)
done
  
  
lemma invContext_unchanged_calls[simp]:
assumes a2: "X = calls S"
    and a3: "calls S c = None"
    and a4: "state_wellFormed S"
shows "invContext (S\<lparr> calls := X(c \<mapsto> Y) \<rparr>) s
     = (invContext S s)"
apply (auto simp add: invContext_def split: option.splits)
apply (auto simp add: a2)
using a3 a4 wellFormed_commitedCallsExist by blast  
  
    
lemma commutative_ALocal_other[simp]:
assumes a1: "sa \<noteq> sb"
shows "commutativeS S (sa, ALocal) (sb, a)"
apply (case_tac a)
apply (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist)
done


lemma commutative_other_ALocal[simp]:
assumes a1: "sa \<noteq> sb"
shows "commutativeS S (sa, a) (sb, ALocal)"
apply (case_tac a)
apply (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist)
done
  
lemma commitedCalls_update1:
"\<lbrakk>
currentTransaction S sa \<triangleq> t;
state_wellFormed S; 
calls S c = None
\<rbrakk> \<Longrightarrow>
     commitedCalls
           (S\<lparr>localState := localState S(sa \<mapsto> ls' res), 
              calls := calls S(c \<mapsto> Call operation args res),
              callOrigin := callOrigin S(c \<mapsto> t)\<rparr>)
    = commitedCalls S"
apply (auto simp add: commitedCalls_def)
using wellFormed_callOrigin_dom by force
    

lemma 
"\<lbrakk>a = AInvcheck True; 
currentTransaction S sb = None; 
visibleCalls S sb \<triangleq> visa; 
localState S sa \<triangleq> ls;
currentProc S sa \<triangleq> f; 
f ls = DbOperation operation args ls'; 
currentTransaction S sa \<triangleq> t;
querySpec (prog S) operation args (getContext S sa) res; 
visibleCalls S sa \<triangleq> vis; 
state_wellFormed S;
sb\<noteq>sa;
calls S c = None
\<rbrakk> \<Longrightarrow> invContext
           (S\<lparr>localState := localState S(sa \<mapsto> ls' res), calls := calls S(c \<mapsto> Call operation args res),
                callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis),
                happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
           sb
  = invContext (S::state) sb"
apply (auto simp add: invContext_def )
apply (auto simp add: commitedCalls_update1)[1]
  using wellFormed_commitedCallsExist apply blast
  using commitedCalls_update1 wellFormed_commitedCallsExist apply blast
  using commitedCalls_update1 wellFormed_commitedCallsExist apply blast
    using commitedCalls_update1 wellFormed_commitedCallsExist apply blast
    apply (simp add: commitedCalls_update1)
    
    thm commitedCalls_unchanged_callOrigin2
find_theorems "commitedCalls ?S - {?c}"
    

lemma commutative_Dbop_other:
assumes a1[simp]: "sa \<noteq> sb"
shows "commutativeS S (sa, ADbOp c operation args res) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis by simp
next
  case (ANewId x2)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case (ABeginAtomic x3)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case AEndAtomic
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case AFail
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist)
next
  case (AInvoc p a)
  show ?thesis 
    proof (induct rule: show_commutativeS_pres)
      case (preBfront s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_invoc step_simps split: if_splits)
    next
      case (preAfront s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_dbop step_simps)
    next
      case (preAback s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_dbop step_simps)
    next
      case (preBback s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_invoc step_simps)
    next
      case (commute s1 s2 s1' s2')
      then show ?case 
        by (auto simp add: AInvoc commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
    qed
    
next
  case (AReturn x8)
  then show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    apply (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
    done
    
next
  case (AInvcheck x10)
  then show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    apply (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
    sorry
next
  case (ADbOp c operation args res)
  then show ?thesis 
    apply (auto simp add: commutativeS_def steps_appendFront)  
next
  case (APull x6)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist)    
qed



lemma commutativePreservesPrecondition_rev:
assumes preconditionHolds: "precondition (sb,b) A"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommited: "transactionStatus A tx \<triangleq> Uncommited"
    and aIsInLocal: "localState A sa \<triangleq> lsa"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    and origin_inv: "dom (callOrigin A) = dom (calls A)"
shows "precondition (sb,b) B"
proof (cases b)
  case ALocal
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_alocal unchangedInTransaction(1) unchangedInTransaction(2)) 
next
  case (ANewId x2)
  then show ?thesis sorry
next
  case (ABeginAtomic x3)
  then show ?thesis sorry
next
  case AEndAtomic
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis sorry
next
  case (APull x6)
  then show ?thesis 
     sorry
next
  case (AInvoc x71 x72)
  then show ?thesis 
    sorry
next
  case (AReturn x8)
  then show ?thesis
    by (metis (full_types) aIsInTransaction differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
    
next
  case AFail
  then show ?thesis
    by (simp add: precondition_fail) 
next
  case (AInvcheck x10)
  then show ?thesis
  proof - (* hammered *)
    obtain CC :: "state \<Rightarrow> bool \<Rightarrow> session \<Rightarrow> callId set" where
      "\<forall>x0 x1 x2. (\<exists>v3. currentTransaction x0 x2 = None \<and> visibleCalls x0 x2 \<triangleq> v3 \<and> invariant (prog x0) (invContext x0 x2) = x1) = (currentTransaction x0 x2 = None \<and> visibleCalls x0 x2 \<triangleq> CC x0 x1 x2 \<and> invariant (prog x0) (invContext x0 x2) = x1)"
      by moura
    then have f1: "\<forall>s b z. (\<not> precondition (s, AInvcheck b) z \<or> currentTransaction z s = None \<and> visibleCalls z s \<triangleq> CC z b s \<and> (\<not> invariant (prog z) (invContext z s)) \<noteq> b) \<and> (precondition (s, AInvcheck b) z \<or> (\<forall>C. currentTransaction z s \<noteq> None \<or> visibleCalls z s \<noteq> Some C \<or> (\<not> invariant (prog z) (invContext z s)) = b))"
      by (metis precondition_invcheck)
    then have f2: "currentTransaction A sb = None \<and> visibleCalls A sb \<triangleq> CC A x10 sb \<and> (\<not> invariant (prog A) (invContext A sb)) \<noteq> x10"
      using AInvcheck preconditionHolds by blast
    then have f3: "currentTransaction B sb = None"
    using aIsInTransaction differentSessions exec unchangedInTransaction(3) by auto
  have f4: "visibleCalls B sb \<triangleq> CC A x10 sb"
    using f2 aIsInTransaction differentSessions exec unchangedInTransaction(4) by auto
  have "invContext A sb = invContext B sb"
    by (meson aIsInLocal aIsInTransaction aIsNotCommit differentSessions exec origin_inv txIsUncommited unchangedInTransaction_getInvContext visibleCalls_inv)
  then have "invariant (prog A) (invContext A sb) = invariant (prog B) (invContext B sb)"
    using exec prog_inv by force
  then show ?thesis
    using f4 f3 f2 f1 AInvcheck by blast
qed
    
qed  
  
lemma 
assumes order1: "\<And>B1 B2. \<lbrakk>A ~~ (sa,a) \<leadsto> B1; B1 ~~ (sb,b) \<leadsto> C1; A ~~ (sb,b) \<leadsto> B2; B2 ~~ (sa,a) \<leadsto> C2\<rbrakk> \<Longrightarrow> C1 = C2" 
 and a1: "sa \<noteq> sb"
 and a2: "currentTransaction A sa \<triangleq> tx"
 and a3: "transactionStatus A tx \<triangleq> Uncommited"
 and a4: "localState A sa \<triangleq> lsa"
 and a5: "a \<noteq> AEndAtomic"
 and a6: "A ~~ (sa, a) \<leadsto> B"
 and a7: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
 and a8: "dom (callOrigin A) = dom (calls A)"
shows "(A ~~ [(sa,a),(sb,b)] \<leadsto>* C) \<longleftrightarrow> (A ~~ [(sb,b),(sa,a)] \<leadsto>* C)"
proof (auto simp add: steps_appendFront)
  fix B
  assume a0: "A ~~ (sa, a) \<leadsto> B"
     and a1: "B ~~ (sb, b) \<leadsto> C"

  from a1
  have "precondition (sb, b) B"
    using precondition_def by blast
  with commutativePreservesPrecondition
  have "precondition (sb, b) A"
    using a0 a2 a3 a4 a5 a7 a8 assms(2) by blast
    
  thus "\<exists>B. (A ~~ (sb, b) \<leadsto> B) \<and> (B ~~ (sa, a) \<leadsto> C)"
    apply (rule step_existsH)
    (*
    what we need here is the other direction as well: preconditions are preserved when moving something into a transaction
    
    alternatively I could also just prove one direction first
    *)
    
    
find_theorems "precondition"

lemma swapCommutative:
assumes differentSessions[simp]: "sa \<noteq> sb"
   and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
shows "(A ~~ [(sa,a),(sb,b)] \<leadsto>* C) \<longleftrightarrow> (A ~~ [(sb,b),(sa,a)] \<leadsto>* C)"
proof -
  have differentSessions2[simp]: "sb \<noteq> sa"
    using differentSessions by blast 
  show "?thesis"
    apply (case_tac a; case_tac b)
    apply (auto simp add: steps_appendFront elim!: step_elims)[1]
    apply (rule step_existsH)
    




lemma one_compaction_step:
assumes splitTrace: "tr = (s, ABeginAtomic tx) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
    and xOutside: "fst x \<noteq> s"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx) # txa @ rest \<leadsto>* C)"
using splitTrace txaInTx xOutside proof (induct txa arbitrary: x rest rule: rev_induct)
  case Nil
  hence tr_def: "tr = (s, ABeginAtomic tx) # x # rest" by simp
  show ?case
  proof 
    assume a1: "s_init ~~ tr \<leadsto>* C"
    with tr_def
    obtain C1 C2 where
          "s_init ~~ (s, ABeginAtomic tx) \<leadsto> C1"
      and "C1 ~~ x \<leadsto> C2"
      and "C2 ~~ rest \<leadsto>* C"
      using steps_append steps_appendFront by auto
    
    
  
    show "s_init ~~ x # (s, ABeginAtomic tx) # [] @ rest \<leadsto>* C"

   sorry
next
  case (snoc x xs)
  then show ?case sorry
qed

lemma one_compaction_step:
assumes splitTrace: "tr = tr1 @ [(s, ABeginAtomic tx)] @ txa @ [x] @ rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr1 @ [x] @ [(s, ABeginAtomic tx)] @ txa @ rest \<leadsto>* C)"

end
