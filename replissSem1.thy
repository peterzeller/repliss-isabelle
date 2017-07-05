theory replissSem1
imports Main
  "~~/src/HOL/Library/Multiset"
  "~/work/afp/thys/Proof_Strategy_Language/PSL" 
begin

strategy Hammers =  RepeatN ( Ors [Hammer, Defer]  )

abbreviation todo ("???") where "??? \<equiv> undefined"

abbreviation eqsome :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<triangleq>" 69) where
 "x \<triangleq> y \<equiv> x = Some y"

abbreviation orElse :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "orElse" 70) where
"x orElse y \<equiv> case x of Some a \<Rightarrow> a | None \<Rightarrow> y"
 
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

record distributed_state = operationContext +
  prog :: prog
  callOrigin :: "callId \<rightharpoonup> txid"
  generatedIds :: "uniqueId set"
  knownIds :: "uniqueId set"
  invocationOp :: "session \<rightharpoonup> (procedureName \<times> any list)"
  invocationRes :: "session \<rightharpoonup> any"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

record state = distributed_state + 
  localState :: "session \<rightharpoonup> localState"
  currentProc :: "session \<rightharpoonup> procedureImpl"
  visibleCalls :: "session \<rightharpoonup> callId set"
  currentTransaction :: "session \<rightharpoonup> txid"
  
  
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

lemma state_ext_exI: 
fixes P :: "state \<Rightarrow> bool"
assumes "
\<exists>
s_calls
s_happensBefore
s_prog
s_localState
s_currentProc
s_visibleCalls
s_currentTransaction
s_transactionStatus
s_callOrigin
s_generatedIds
s_knownIds
s_invocationOp
s_invocationRes. P \<lparr>
calls = s_calls,
happensBefore = s_happensBefore,
prog = s_prog,
callOrigin = s_callOrigin,
generatedIds = s_generatedIds,
knownIds = s_knownIds,
invocationOp = s_invocationOp,
invocationRes = s_invocationRes,
transactionStatus = s_transactionStatus,
localState = s_localState,
currentProc = s_currentProc,
visibleCalls = s_visibleCalls,
currentTransaction = s_currentTransaction
\<rparr>"
shows "\<exists>s. P s"
  using assms by blast

thm state.defs  

definition restrict_relation :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "|r"  110)
where "r |r A \<equiv> r Int (A \<times> A)"
  
term restrict_map

abbreviation "emptyOperationContext \<equiv> \<lparr> calls = empty, happensBefore = {}\<rparr>"

  
  
definition "getContextH" where
"getContextH state_calls state_happensBefore state_vis = (case state_vis of
      None \<Rightarrow> emptyOperationContext
    | Some vis => \<lparr>
        calls = state_calls |` vis,
        happensBefore = state_happensBefore |r vis
      \<rparr>
  )"

abbreviation 
"getContext state s
 \<equiv> getContextH (calls state) (happensBefore state) (visibleCalls state s) "

abbreviation "emptyInvariantContext \<equiv> \<lparr>
        i_calls = empty,
        i_happensBefore = {},
        i_visibleCalls = {},
        i_callOrigin  = empty,
        i_knownIds = {},
        i_invocationOp = empty,
        i_invocationRes = empty
\<rparr>"


definition "commitedCallsH state_callOrigin state_transactionStatus \<equiv> 
   {c | c tx. state_callOrigin c \<triangleq> tx \<and> state_transactionStatus tx \<triangleq> Commited }"

abbreviation commitedCalls :: "state \<Rightarrow> callId set" where
"commitedCalls state \<equiv> commitedCallsH (callOrigin state) (transactionStatus state)"
  
definition invContextH  where
"invContextH state_callOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis = \<lparr>
        i_calls = state_calls |` commitedCallsH state_callOrigin state_transactionStatus , 
        i_happensBefore = state_happensBefore |r commitedCallsH state_callOrigin state_transactionStatus , 
        i_visibleCalls = (case vis of None \<Rightarrow> {} | Some vis \<Rightarrow> vis),
        i_callOrigin  = state_callOrigin |` commitedCallsH state_callOrigin state_transactionStatus,
        i_knownIds = state_knownIds,
        i_invocationOp = state_invocationOp,
        i_invocationRes = state_invocationRes
      \<rparr>"

abbreviation invContext where
"invContext state s \<equiv>
  invContextH
  (callOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)
  (visibleCalls state s)"

abbreviation invContextVis where
"invContextVis state vis \<equiv>
  invContextH
  (callOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)
  (Some vis)"
  
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
  
find_consts "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"

definition downwardsClosure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"  (infixr "\<down>" 100)  where 
"S \<down> R \<equiv> S \<union> {x | x y . (x,y)\<in>R \<and> y\<in>S}"

lemma downwardsClosure_in:
"x \<in> S \<down> R \<longleftrightarrow> (x\<in>S \<or> (\<exists>y\<in>S. (x,y)\<in>R))"
by (auto simp add: downwardsClosure_def)

lemma downwardsClosure_subset:
"S \<down> R \<subseteq> S \<union> fst ` R"
apply (auto simp add: downwardsClosure_in)
using image_iff tranclD by fastforce

lemma downwardsClosure_subset2:
"x \<in> S \<down> R \<Longrightarrow> x \<in> S \<union> fst ` R"
  by (meson downwardsClosure_subset subsetCE)

(*
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
*)

datatype action =
    ALocal
  | ANewId uniqueId
  | ABeginAtomic txid "txid set"
  | AEndAtomic
  | ADbOp callId operation "any list" any
  | AInvoc procedureName "any list"
  | AReturn any
  | AFail  
  | AInvcheck bool

definition callsInTransactionH :: "(callId \<rightharpoonup> txid) \<Rightarrow> txid set \<Rightarrow> callId set" where
"callsInTransactionH origins txns  \<equiv> {c. \<exists>txn\<in>txns. origins c \<triangleq> txn }"

lemma callsInTransactionH_contains:
"c\<in>callsInTransactionH origins txns \<longleftrightarrow> (case origins c of Some txn \<Rightarrow>  txn \<in> txns | None \<Rightarrow> False)"
by (auto simp add: callsInTransactionH_def split: option.splits)

abbreviation 
"callsInTransaction S txns \<equiv> callsInTransactionH (callOrigin S) txns"
  
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
   \<rbrakk> \<Longrightarrow> C ~~ (s, ANewId uid) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls' uid), 
                                   generatedIds := generatedIds C \<union> {uid} \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTransaction C s = None;   
   transactionStatus C t = None;
   visibleCalls C s \<triangleq> vis;
   (* choose a set of commited transactions to add to the snapshot *)
   newTxns \<subseteq> commitedTransactions C;
   (* determine new visible calls: downwards-closure wrt. causality  *)
   newCalls = callsInTransaction C newTxns \<down> happensBefore C;
   (* transaction snapshot *)
   snapshot = vis \<union> newCalls
   \<rbrakk> \<Longrightarrow> C ~~ (s, ABeginAtomic t newTxns) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C)(s \<mapsto> t),
                transactionStatus := (transactionStatus C)(t \<mapsto> Uncommited),
                visibleCalls := (visibleCalls C)(s \<mapsto> snapshot)\<rparr>)"
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
   calls C c = None;
   querySpec (prog C) Op args (getContext C s)  res;
   visibleCalls C s \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  C ~~ (s, ADbOp c Op args res) \<leadsto> (C\<lparr>localState := (localState C)(s \<mapsto> ls' res), 
                calls := (calls C)(c \<mapsto> Call Op args res ),
                callOrigin := (callOrigin C)(c \<mapsto> t),
                visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore C \<union> vis \<times> {c}  \<rparr>)"                
                     
| invocation:
  "\<lbrakk>localState C s = None;
   procedure (prog C) procName args \<triangleq> (initialState, impl);
   uniqueIdsInList args \<subseteq> knownIds C;
   invocationOp C s = None
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
                 invocationRes := (invocationRes C)(s \<mapsto> res),
                 knownIds := knownIds C \<union> uniqueIds res\<rparr>)"                
| fail:
  "localState C s \<triangleq> ls
   \<Longrightarrow> C ~~ (s, AFail) \<leadsto> (C\<lparr>localState := (localState C)(s := None),
                 currentTransaction := (currentTransaction C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None) \<rparr>)"                  
| invCheck:
  "\<lbrakk>currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   invariant (prog C) (invContext C s) = res
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvcheck res) \<leadsto> C"   

inductive_simps step_simp_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_simps step_simp_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_simps step_simp_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_simps step_simp_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_simps step_simp_ADbOp: "A ~~ (s, ADbOp c oper args res) \<leadsto> B "
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
  step_simp_AInvoc
  step_simp_AReturn
  step_simp_AFail
  step_simp_AInvcheck

inductive_cases step_elim_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_cases step_elim_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_cases step_elim_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_cases step_elim_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_cases step_elim_ADbOp: "A ~~ (s, ADbOp c oper args res) \<leadsto> B "
inductive_cases step_elim_AInvoc: "A ~~ (s, AInvoc procname args) \<leadsto> B "
inductive_cases step_elim_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_cases step_elim_AFail: "A ~~ (s, AFail) \<leadsto> B "
inductive_cases step_elim_AInvcheck: "A ~~ (s, AInvcheck i) \<leadsto> B "
inductive_cases step_elim_general: "A ~~ (s, a) \<leadsto> B "

lemmas step_elims = 
  step_elim_ALocal
  step_elim_ANewId
  step_elim_ABeginAtomic
  step_elim_AEndAtomic
  step_elim_ADbOp
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
  transactionStatus = empty,
  localState = empty,
  currentProc = empty,
  visibleCalls = empty,
  currentTransaction = empty
\<rparr>"

type_synonym trace = "(session\<times>action) list"

definition traces where
"traces program \<equiv> {tr | tr S' . initialState program ~~ tr \<leadsto>* S'}"

definition traceCorrect where
"traceCorrect trace \<equiv> (\<forall>s. (s, AInvcheck False) \<notin> set trace)"

definition programCorrect where
"programCorrect program \<equiv> (\<forall>trace\<in>traces program. traceCorrect trace)"

definition "isABeginAtomic action = (case action of ABeginAtomic x newTxns \<Rightarrow> True | _ \<Rightarrow> False)"

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
by (auto split: if_splits prod.splits)

lemma splitTrace_len[simp]: 
assumes a: "splitTrace s tr = (h,c,t)"
shows "length h \<le> length tr"
  and "length c \<le> length tr"
  and "length t \<le> length tr"
using a apply (induct arbitrary: h c t rule: splitTrace.induct)
by (auto simp add: le_SucI split: if_splits prod.splits)

lemma splitTrace_len2[simp]: 
assumes a: "(h,c,t) = splitTrace s tr"
shows "length h \<le> length tr"
  and "length c \<le> length tr"
  and "length t \<le> length tr"
using a by (metis splitTrace_len(1), metis splitTrace_len(2), metis splitTrace_len(3))
  
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

lemma steps_append2: 
assumes "A ~~ tra \<leadsto>* B"
shows "(A ~~ tra@trb \<leadsto>* C) \<longleftrightarrow> (B ~~ trb \<leadsto>* C)"
  using assms steps_append traceDeterministic by blast


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

lemma state_wellFormed_init[simp]:
"state_wellFormed (initialState program)"
  by (metis distributed_state.select_convs(1) initialState_def state_wellFormed_def steps_refl)

lemma state_wellFormed_combine:
assumes wf: "state_wellFormed S"
and steps: "S ~~ tr \<leadsto>* S'"
shows "state_wellFormed S'"
proof -
  from steps 
  have "prog S' = prog S"
    by (induct rule: steps.induct, auto simp add: step_simps)

 from wf obtain tr1 where "initialState (prog S) ~~ tr1 \<leadsto>* S"
   using state_wellFormed_def by blast 
 with steps
 have "initialState (prog S) ~~ tr1@tr \<leadsto>* S'"
   using steps_append by blast
 with `prog S' = prog S`
 have "initialState (prog S') ~~ tr1@tr \<leadsto>* S'" by simp
 thus "state_wellFormed S'"
  using state_wellFormed_def by auto 
qed  

lemma step_prog_invariant:
"S ~~ tr \<leadsto>* S' \<Longrightarrow> prog S' = prog S"
apply (induct rule: steps.induct)
apply auto
apply (erule step.cases)
apply auto
done

thm full_nat_induct


lemma steps_induct[consumes 1, case_names initial step[steps IH step]]:
assumes a1: "init ~~ tr \<leadsto>*  S"
    and a2: "P [] init"
    and a3: "\<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''"
shows "P tr S"
proof -
  have h: "\<lbrakk>S ~~ tr \<leadsto>* s; P [] init; S = init; 
      \<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''\<rbrakk> \<Longrightarrow> P tr s" for S tr s
    proof (induct rule: steps.induct)
      case (steps_refl S)                        
      then show ?case by simp
    next
      case (steps_step S tr S' a S'')
      have "P tr S'"
        apply (rule steps_step(2))
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(1) steps_step.prems(2) apply auto[1]
        using initialState_def step_prog_invariant steps_step.hyps(1) steps_step.prems(2) apply auto[1]
        by (simp add: steps_step.prems(3))
      show ?case
      proof (rule a3)
        show "init ~~ tr \<leadsto>* S'"
          using steps_step.hyps(1) steps_step.prems(2) by auto
        show "P tr S'" using `P tr S'` .
        show "S' ~~ a \<leadsto> S''"
          by (simp add: steps_step.hyps(3)) 
      qed
    qed
  show ?thesis
  using a1 a2
  proof (rule h)
    show "init = init" ..
    show "\<And>S' tr a S''. \<lbrakk>init ~~ tr \<leadsto>* S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr @ [a]) S''"
      using a3 by auto
  qed  
qed


lemma steps_induct2[consumes 1, case_names initial step[steps IH step]]:
assumes a1: "initialState progr ~~ tr \<leadsto>*  S"
    and a2: "P [] (initialState progr)"
    and a3: "\<And>S' tr a S''. \<lbrakk>initialState progr ~~ tr \<leadsto>*  S'; P tr S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> P (tr@[a]) S''"
shows "P tr S"
  using a1 a2 a3 steps_induct by blast


lemma wellFormed_induct[consumes 1]:
"\<lbrakk>state_wellFormed s; P (initialState (prog s)); \<And>t a s. \<lbrakk>state_wellFormed t; P t; t ~~ a \<leadsto> s\<rbrakk> \<Longrightarrow> P s\<rbrakk> \<Longrightarrow> P s"
apply (auto simp add: state_wellFormed_def)
apply (erule(1) steps_induct)
by (metis prod.collapse state_wellFormed_def state_wellFormed_init step_prog_invariant steps_append)



lemma wellFormed_callOrigin_dom:
assumes a1: "state_wellFormed S"
shows "dom (callOrigin S) = dom (calls S)"
using a1 apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
  apply blast
  by blast

lemma wellFormed_callOrigin_dom2[simp]: 
"\<lbrakk>calls S c = None; state_wellFormed S\<rbrakk> \<Longrightarrow>  callOrigin S c = None"
  using wellFormed_callOrigin_dom by force


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
  apply (auto simp add: callsInTransactionH_contains downwardsClosure_in split: option.splits)[1]
  apply (metis not_None_eq wellFormed_callOrigin_dom2)
  apply blast
  apply blast
  apply blast
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
    
  
  
end
