theory repliss_sem
  imports Main
    "~~/src/HOL/Library/Multiset"
    "~~/src/HOL/Library/Option_ord"
begin

section {* Semantics *}

text {* This theory describes the distributed semantics used by Repliss. *}


abbreviation todo ("???") where "??? \<equiv> undefined"

abbreviation eqsome :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<triangleq>" 69) where
  "x \<triangleq> y \<equiv> x = Some y"

abbreviation orElse :: "'a option \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "orElse" 70) where
  "x orElse y \<equiv> case x of Some a \<Rightarrow> a | None \<Rightarrow> y"

typedecl invocation

definition uniqueIds :: "'any \<Rightarrow> 'any set" where 
  "uniqueIds = ???"

definition 
  "uniqueIdsInList xs = (\<Union>x\<in>set xs. uniqueIds x)"


type_synonym operation = string



typedecl txid
typedecl callId

datatype 'any call = Call operation (call_args:"'any list") (call_res:"'any")

datatype ('localState, 'any) localAction =
  LocalStep 'localState
  | BeginAtomic 'localState
  | EndAtomic 'localState
  | NewId "'any \<Rightarrow> 'localState"
  | DbOperation operation "'any list" "'any \<Rightarrow> 'localState"
  | Return 'any

type_synonym procedureName = string

type_synonym ('localState, 'any) procedureImpl = "'localState \<Rightarrow> ('localState, 'any) localAction"

datatype transactionStatus = Uncommited | Commited 

instantiation transactionStatus :: linorder 
begin
definition "less_eq_transactionStatus x y \<equiv> x = Uncommited \<or> y = Commited"
definition "less_transactionStatus x y \<equiv> x = Uncommited \<and> y = Commited"
instance 
  apply standard
  using transactionStatus.exhaust by (auto simp add: less_eq_transactionStatus_def less_transactionStatus_def )
end  

lemmas transactionStatus_less_simps[simp] = less_eq_transactionStatus_def less_transactionStatus_def

lemma onlyCommitedGreater: "a \<triangleq> Commited" if "a\<ge>Some Commited" for a
  by (smt dual_order.antisym dual_order.trans less_eq_option_None_is_None less_eq_option_Some less_eq_transactionStatus_def order_refl split_option_ex that)



record 'any operationContext = 
  calls :: "callId \<rightharpoonup> 'any call"
  happensBefore :: "callId rel"

record 'any invariantContext = "'any operationContext" +
  i_visibleCalls :: "callId set"
  i_callOrigin :: "callId \<rightharpoonup> txid"
  i_transactionOrigin :: "txid \<rightharpoonup> invocation"
  i_knownIds :: "'any set"
  i_invocationOp :: "invocation \<rightharpoonup> (procedureName \<times> 'any list)"
  i_invocationRes :: "invocation \<rightharpoonup> 'any"

record ('localState, 'any) prog =
  querySpec :: "operation \<Rightarrow> 'any list \<Rightarrow> 'any operationContext \<Rightarrow> 'any \<Rightarrow> bool"
  procedure :: "procedureName \<Rightarrow> 'any list \<rightharpoonup> ('localState \<times> ('localState, 'any) procedureImpl)"
  invariant :: "'any invariantContext \<Rightarrow> bool"

record ('localState, 'any) distributed_state = "'any operationContext" +
  prog :: "('localState, 'any) prog"
  callOrigin :: "callId \<rightharpoonup> txid"
  transactionOrigin :: "txid \<rightharpoonup> invocation"
  generatedIds :: "'any set"
  knownIds :: "'any set"
  invocationOp :: "invocation \<rightharpoonup> (procedureName \<times> 'any list)"
  invocationRes :: "invocation \<rightharpoonup> 'any"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

record ('localState, 'any) state = "('localState, 'any) distributed_state" + 
  localState :: "invocation \<rightharpoonup> 'localState"
  currentProc :: "invocation \<rightharpoonup> ('localState, 'any) procedureImpl"
  visibleCalls :: "invocation \<rightharpoonup> callId set"
  currentTransaction :: "invocation \<rightharpoonup> txid"


lemma state_ext: "((x::('localState, 'any) state) = y) \<longleftrightarrow> (
    calls x = calls y
  \<and> happensBefore x = happensBefore y
  \<and> prog x = prog y
  \<and> localState x = localState y
  \<and> currentProc x = currentProc y
  \<and> visibleCalls x = visibleCalls y
  \<and> currentTransaction x = currentTransaction y
  \<and> transactionStatus x = transactionStatus y
  \<and> callOrigin x = callOrigin y
  \<and> transactionOrigin x = transactionOrigin y
  \<and> generatedIds x = generatedIds y
  \<and> knownIds x = knownIds y
  \<and> invocationOp x = invocationOp y
  \<and> invocationRes x = invocationRes y
)"
  by auto

lemma state_ext_exI: 
  fixes P :: "('localState, 'any) state \<Rightarrow> bool"
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
s_transactionOrigin
s_generatedIds
s_knownIds
s_invocationOp
s_invocationRes. P \<lparr>
calls = s_calls,
happensBefore = s_happensBefore,
prog = s_prog,
callOrigin = s_callOrigin,
transactionOrigin = s_transactionOrigin,
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
  where "r |r A \<equiv> r \<inter> (A \<times> A)"


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
        calls = empty,
        happensBefore = {},
        i_visibleCalls = {},
        i_callOrigin  = empty,
        i_transactionOrigin = empty,
        i_knownIds = {},
        i_invocationOp = empty,
        i_invocationRes = empty
\<rparr>"

definition isCommittedH where
  "isCommittedH state_callOrigin state_transactionStatus c \<equiv> \<exists>tx. state_callOrigin c \<triangleq> tx \<and> state_transactionStatus tx \<triangleq> Commited"

abbreviation isCommitted :: "('localState, 'any) state \<Rightarrow> callId \<Rightarrow> bool" where
  "isCommitted state \<equiv> isCommittedH (callOrigin state) (transactionStatus state)"

definition "commitedCallsH state_callOrigin state_transactionStatus \<equiv> 
   {c. isCommittedH state_callOrigin state_transactionStatus c}"

abbreviation commitedCalls :: "('localState, 'any) state \<Rightarrow> callId set" where
  "commitedCalls state \<equiv> commitedCallsH (callOrigin state) (transactionStatus state)"

definition invContextH  where
  "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis = \<lparr>
        calls = state_calls |` commitedCallsH state_callOrigin state_transactionStatus , 
        happensBefore = state_happensBefore |r commitedCallsH state_callOrigin state_transactionStatus , 
        i_visibleCalls = (case vis of None \<Rightarrow> {} | Some vis \<Rightarrow> vis),
        i_callOrigin  = state_callOrigin |` commitedCallsH state_callOrigin state_transactionStatus,
        i_transactionOrigin = state_transactionOrigin |` {t. state_transactionStatus t \<triangleq> Commited},
        i_knownIds = state_knownIds,
        i_invocationOp = state_invocationOp,
        i_invocationRes = state_invocationRes
      \<rparr>"


lemma invContextH_calls[simp]:
"calls (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= state_calls |` commitedCallsH state_callOrigin state_transactionStatus"
  by (auto simp add: invContextH_def)


lemma invContextH_happensBefore[simp]:
"happensBefore (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= state_happensBefore |r commitedCallsH state_callOrigin state_transactionStatus "
  by (auto simp add: invContextH_def)

lemma invContextH_i_visibleCalls[simp]:
"i_visibleCalls (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= (case vis of None \<Rightarrow> {} | Some vis \<Rightarrow> vis)"
  by (auto simp add: invContextH_def)

lemma invContextH_i_callOrigin[simp]:
"i_callOrigin (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= state_callOrigin |` commitedCallsH state_callOrigin state_transactionStatus"
by (auto simp add: invContextH_def)

lemma invContextH_i_transactionOrigin[simp]:
"i_transactionOrigin (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
=  state_transactionOrigin |` {t. state_transactionStatus t \<triangleq> Commited}"
  by (auto simp add: invContextH_def)

lemma invContextH_i_knownIds[simp]:
"i_knownIds (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= state_knownIds"
  by (auto simp add: invContextH_def)

lemma invContextH_i_invocationOp[simp]:
"i_invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
= state_invocationOp"
by (auto simp add: invContextH_def)


lemma invContextH_i_invocationRes[simp]:
"i_invocationRes (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes vis) 
=  state_invocationRes"
by (auto simp add: invContextH_def)

abbreviation invContext where
  "invContext state s \<equiv>
  invContextH
  (callOrigin state)
  (transactionOrigin state)
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
  (transactionOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)
  (Some vis)"

definition callsInTransactionH :: "(callId \<rightharpoonup> txid) \<Rightarrow> txid set \<Rightarrow> callId set" where
  "callsInTransactionH origins txns  \<equiv> {c. \<exists>txn\<in>txns. origins c \<triangleq> txn }"

lemma callsInTransactionH_contains:
  "c\<in>callsInTransactionH origins txns \<longleftrightarrow> (case origins c of Some txn \<Rightarrow>  txn \<in> txns | None \<Rightarrow> False)"
  by (auto simp add: callsInTransactionH_def split: option.splits)

abbreviation 
  "callsInTransaction S txns \<equiv> callsInTransactionH (callOrigin S) txns"  

abbreviation invContextSnapshot where
  "invContextSnapshot state txns \<equiv>
  invContextH
  (callOrigin state)
  (transactionOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)
  (Some (callsInTransaction state txns \<down> happensBefore state))"  

lemma invContextSnapshot_eq:
  assumes "c_calls = commitedCallsH (callOrigin state) (transactionStatus state)"
    and "c_txns = {t. transactionStatus state t \<triangleq> Commited}"
  shows
    "invContextSnapshot state snapshot =  \<lparr>
        calls = calls state |` c_calls , 
        happensBefore = happensBefore state |r c_calls , 
        i_visibleCalls = callsInTransaction state snapshot \<down> happensBefore state,
        i_callOrigin  = callOrigin state |` c_calls,
        i_transactionOrigin = transactionOrigin state |` c_txns,
        i_knownIds = knownIds state,
        i_invocationOp = invocationOp state,
        i_invocationRes = invocationRes state\<rparr>"
  by (auto simp add: assms  invContextH_def)



lemma invariantContext_eqI: "\<lbrakk>
calls x = calls y;
happensBefore x = happensBefore y;
i_visibleCalls x = i_visibleCalls y;
i_callOrigin x = i_callOrigin y;
i_transactionOrigin x = i_transactionOrigin y;
i_knownIds x = i_knownIds y;
i_invocationOp x = i_invocationOp y;
i_invocationRes x = i_invocationRes y
\<rbrakk> \<Longrightarrow> x = (y::'any invariantContext)"
  by auto


(*
abbreviation isUndef :: "'a option \<Rightarrow> bool" ("_ = \<bottom>" [0]60) where
 "x = \<bottom> \<equiv> x = None"
*)




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

datatype 'any action =
  ALocal
  | ANewId 'any
  | ABeginAtomic txid "txid set"
  | AEndAtomic
  | ADbOp callId operation "'any list" 'any
  | AInvoc procedureName "'any list"
  | AReturn 'any
  | AFail  
  | AInvcheck "txid set" bool


definition "is_AInvcheck a \<equiv> \<exists>txns r. a = AInvcheck txns r"

inductive step :: "('localState, 'any) state \<Rightarrow> (invocation \<times> 'any action) \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>" 60) where
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
                transactionOrigin := (transactionOrigin C)(t \<mapsto> s),
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
  "\<lbrakk>localState C s = None; (* TODO this might not be necessary *)
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
| invCheck: (* checks a snapshot*)
  "\<lbrakk>txns \<subseteq> commitedTransactions C;
   invariant (prog C) (invContextSnapshot C txns) = res
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvcheck txns res) \<leadsto> C"   

inductive_simps step_simp_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_simps step_simp_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_simps step_simp_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_simps step_simp_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_simps step_simp_ADbOp: "A ~~ (s, ADbOp c oper args res) \<leadsto> B "
inductive_simps step_simp_AInvoc: "A ~~ (s, AInvoc procname args) \<leadsto> B "
inductive_simps step_simp_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_simps step_simp_AFail: "A ~~ (s, AFail) \<leadsto> B "
inductive_simps step_simp_AInvcheck: "A ~~ (s, AInvcheck txns res) \<leadsto> B "
inductive_simps step_simps_all: "A ~~ b \<leadsto> B "

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
inductive_cases step_elim_AInvcheck: "A ~~ (s, AInvcheck t i) \<leadsto> B "
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

inductive steps :: "('localState, 'any) state \<Rightarrow> (invocation \<times> 'any action) list \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>*" 60) where         
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

definition initialState :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state" where
  "initialState program \<equiv> \<lparr>
  calls = empty,
  happensBefore = {},
  prog = program,
  callOrigin = empty,
  transactionOrigin = empty,
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

type_synonym 'any trace = "(invocation\<times>'any action) list"

definition traces where
  "traces program \<equiv> {tr | tr S' . initialState program ~~ tr \<leadsto>* S'}"

definition traceCorrect where
  "traceCorrect trace \<equiv> (\<forall>s txns. (s, AInvcheck txns False) \<notin> set trace)"

definition programCorrect where
  "programCorrect program \<equiv> (\<forall>trace\<in>traces program. traceCorrect trace)"

definition "isABeginAtomic action = (case action of ABeginAtomic x newTxns \<Rightarrow> True | _ \<Rightarrow> False)"

definition "isAInvoc action = (case action of AInvoc _ _  \<Rightarrow> True | _ \<Rightarrow> False)"

(*
 splits a trace into three parts
  
1. part until first (s, EndAtomic) on different sessions
2. part until and including (s, EndAtomic); same invocation
3. rest
*)
fun splitTrace :: "invocation \<Rightarrow> 'any trace \<Rightarrow> ('any trace \<times> 'any trace \<times> 'any trace)" where
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


fun compactTrace :: "invocation \<Rightarrow> 'any trace \<Rightarrow> 'any trace" where
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



end
