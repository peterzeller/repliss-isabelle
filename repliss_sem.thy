section \<open>Interleaving Semantics\<close>

theory repliss_sem
  imports Main
    "HOL-Library.Multiset"
    "HOL-Library.Option_ord"
    "HOL-Eisbach.Eisbach"
    "HOL-Library.Countable"
    utils
begin


text \<open>This theory describes the distributed semantics used by Repliss.
We use a fine grained interleaving semantics.
\<close>


datatype invocId = InvocId int
datatype txId = txId int
datatype callId = CallId int

text "A value type is a type that contains unique identifiers.
Since higher kinded classes are not supported, we represent unique ids using natural numbers.
The countable type class can then be used to convert other countable types to nat.

We also expect a default value, which does not include any unique ids. 
This will be used for database operations with no result value."

type_synonym uniqueId = nat
class valueType = countable + default +
  fixes uniqueIds :: "'a \<Rightarrow> uniqueId set"
  assumes default_none[simp]: "uniqueIds default = {}"

definition 
  "uniqueIdsInList xs = (\<Union>x\<in>set xs. uniqueIds x)"

instantiation bool :: valueType begin
definition [simp]: "uniqueIds_bool \<equiv> \<lambda>b::bool. {}::uniqueId set"
definition [simp]: "default_bool \<equiv> False"
instance by standard auto
end

instantiation unit :: valueType begin
definition [simp]: "uniqueIds_unit \<equiv> \<lambda>b::unit. {}::uniqueId set"
instance by standard auto
end



text_raw \<open>\DefineSnippet{call}{\<close>
datatype ('op, 'any) call = Call (call_operation: 'op) (call_res:"'any")
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{localAction}{\<close>
datatype ('ls, 'op, 'any) localAction =
    LocalStep bool 'ls
  | BeginAtomic 'ls
  | EndAtomic 'ls
  | NewId "'any \<rightharpoonup> 'ls"
  | DbOperation 'op "'any \<Rightarrow> 'ls"
  | Return 'any
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{procedureImpl}{\<close>
type_synonym ('ls, 'op, 'any) procedureImpl = 
  "'ls \<Rightarrow> ('ls, 'op, 'any) localAction"
text_raw \<open>}%EndSnippet\<close>

datatype txStatus = Uncommitted | Committed 

instantiation txStatus :: linorder
begin
definition "less_eq_txStatus x y \<equiv> x = Uncommitted \<or> y = Committed"
definition "less_txStatus x y \<equiv> x = Uncommitted \<and> y = Committed"
instance
   by (standard; insert txStatus.exhaust;  auto simp add: less_eq_txStatus_def less_txStatus_def)
end

lemmas txStatus_less_simps = less_eq_txStatus_def less_txStatus_def

lemma onlyCommittedGreater: "a \<triangleq> Committed" if "a\<ge>Some Committed" for a
  by (smt dual_order.antisym dual_order.trans less_eq_option_None_is_None less_eq_option_Some less_eq_txStatus_def order_refl split_option_ex that)



text_raw \<open>\DefineSnippet{operationContext}{\<close>
record ('op, 'any) operationContext = 
  calls :: "callId \<rightharpoonup> ('op, 'any) call"
  happensBefore :: "callId rel"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{invContext}{\<close>
record ('proc, 'op, 'any) invContext = "('op, 'any) operationContext" +
  callOrigin :: "callId \<rightharpoonup> txId"
  txOrigin :: "txId \<rightharpoonup> invocId"
  knownIds :: "uniqueId set"
  invocOp :: "invocId \<rightharpoonup> 'proc"
  invocRes :: "invocId \<rightharpoonup> 'any"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{prog}{\<close>
record ('proc, 'ls, 'op, 'any) prog =
  querySpec :: "'op \<Rightarrow> ('op, 'any) operationContext \<Rightarrow> 'any \<Rightarrow> bool"
  procedure :: "'proc \<Rightarrow> ('ls \<times> ('ls, 'op, 'any) procedureImpl)"
  invariant :: "('proc, 'op, 'any) invContext \<Rightarrow> bool"
text_raw \<open>}%EndSnippet\<close>


text_raw \<open>\DefineSnippet{state}{\<close>
record ('proc, 'ls, 'op, 'any) state = "('proc, 'op, 'any) invContext" +
  prog :: "('proc, 'ls, 'op, 'any) prog"
  txStatus :: "txId \<rightharpoonup> txStatus"
  generatedIds :: "uniqueId \<rightharpoonup> invocId"
  localState :: "invocId \<rightharpoonup> 'ls"
  currentProc :: "invocId \<rightharpoonup> ('ls, 'op, 'any) procedureImpl"
  visibleCalls :: "invocId \<rightharpoonup> callId set"
  currentTx :: "invocId \<rightharpoonup> txId"
text_raw \<open>}%EndSnippet\<close>


lemma operationContext_ext: "((x::('op, 'any) operationContext) = y) \<longleftrightarrow> (
    calls x = calls y
  \<and> happensBefore x = happensBefore y)"
  by auto

lemma state_ext: "((x::('proc, 'ls, 'op, 'any) state) = y) \<longleftrightarrow> (
    calls x = calls y
  \<and> happensBefore x = happensBefore y
  \<and> prog x = prog y
  \<and> localState x = localState y
  \<and> currentProc x = currentProc y
  \<and> visibleCalls x = visibleCalls y
  \<and> currentTx x = currentTx y
  \<and> txStatus x = txStatus y
  \<and> callOrigin x = callOrigin y
  \<and> txOrigin x = txOrigin y
  \<and> generatedIds x = generatedIds y
  \<and> knownIds x = knownIds y
  \<and> invocOp x = invocOp y
  \<and> invocRes x = invocRes y
)"
  by auto


lemmas stateEqI = state_ext[THEN iffToImp, simplified imp_conjL, rule_format]

lemma state_ext_exI:
  fixes P :: "('proc, 'ls, 'op, 'any) state \<Rightarrow> bool"
  assumes "
\<exists>
s_calls
s_happensBefore
s_prog
s_localState
s_currentProc
s_visibleCalls
s_currentTx
s_txStatus
s_callOrigin
s_txOrigin
s_generatedIds
s_knownIds
s_invocOp
s_invocRes. P \<lparr>
calls = s_calls,
happensBefore = s_happensBefore,
callOrigin = s_callOrigin,
txOrigin = s_txOrigin,
knownIds = s_knownIds,
invocOp = s_invocOp,
invocRes = s_invocRes,
prog = s_prog,
txStatus = s_txStatus,
generatedIds = s_generatedIds,
localState = s_localState,
currentProc = s_currentProc,
visibleCalls = s_visibleCalls,
currentTx = s_currentTx
\<rparr>"
  shows "\<exists>s. P s"
  using assms by blast


lemma show_state_calls_eq:
  assumes "A = B"
  shows "\<And>x y. x = y \<Longrightarrow> A\<lparr>calls := x\<rparr> = B\<lparr>calls := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>happensBefore := x\<rparr> = B\<lparr>happensBefore := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>callOrigin := x\<rparr> = B\<lparr>callOrigin := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>txOrigin := x\<rparr> = B\<lparr>txOrigin := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>knownIds := x\<rparr> = B\<lparr>knownIds := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>invocOp := x\<rparr> = B\<lparr>invocOp := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>invocRes := x\<rparr> = B\<lparr>invocRes := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>prog := x\<rparr> = B\<lparr>prog := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>txStatus := x\<rparr> = B\<lparr>txStatus := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>generatedIds := x\<rparr> = B\<lparr>generatedIds := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>localState := x\<rparr> = B\<lparr>localState := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>currentProc := x\<rparr> = B\<lparr>currentProc := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>visibleCalls := x\<rparr> = B\<lparr>visibleCalls := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>currentTx := x\<rparr> = B\<lparr>currentTx := y\<rparr>"
  using assms  by auto

lemma state_updates_normalize:
  shows "\<And>x y. S\<lparr>happensBefore := y, calls := x\<rparr> = S\<lparr>calls := x,  happensBefore := y\<rparr>"
and "\<And>x y. S\<lparr>callOrigin := y, calls := x\<rparr> = S\<lparr>calls := x,  callOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>txOrigin := y, calls := x\<rparr> = S\<lparr>calls := x,  txOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, calls := x\<rparr> = S\<lparr>calls := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocOp := y, calls := x\<rparr> = S\<lparr>calls := x,  invocOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, calls := x\<rparr> = S\<lparr>calls := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, calls := x\<rparr> = S\<lparr>calls := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, calls := x\<rparr> = S\<lparr>calls := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, calls := x\<rparr> = S\<lparr>calls := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, calls := x\<rparr> = S\<lparr>calls := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, calls := x\<rparr> = S\<lparr>calls := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, calls := x\<rparr> = S\<lparr>calls := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, calls := x\<rparr> = S\<lparr>calls := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>callOrigin := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  callOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>txOrigin := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  txOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocOp := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  invocOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>txOrigin := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  txOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocOp := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  invocOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocOp := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  invocOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, txOrigin := x\<rparr> = S\<lparr>txOrigin := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>invocOp := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  invocOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>invocRes := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  invocRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, invocOp := x\<rparr> = S\<lparr>invocOp := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, invocRes := x\<rparr> = S\<lparr>invocRes := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>txStatus := y, prog := x\<rparr> = S\<lparr>prog := x,  txStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, prog := x\<rparr> = S\<lparr>prog := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, prog := x\<rparr> = S\<lparr>prog := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, prog := x\<rparr> = S\<lparr>prog := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, prog := x\<rparr> = S\<lparr>prog := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, prog := x\<rparr> = S\<lparr>prog := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, txStatus := x\<rparr> = S\<lparr>txStatus := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, txStatus := x\<rparr> = S\<lparr>txStatus := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, txStatus := x\<rparr> = S\<lparr>txStatus := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, txStatus := x\<rparr> = S\<lparr>txStatus := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, txStatus := x\<rparr> = S\<lparr>txStatus := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, localState := x\<rparr> = S\<lparr>localState := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, localState := x\<rparr> = S\<lparr>localState := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, localState := x\<rparr> = S\<lparr>localState := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, currentProc := x\<rparr> = S\<lparr>currentProc := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, currentProc := x\<rparr> = S\<lparr>currentProc := x,  currentTx := y\<rparr>"
and "\<And>x y. S\<lparr>currentTx := y, visibleCalls := x\<rparr> = S\<lparr>visibleCalls := x,  currentTx := y\<rparr>"
  by auto
  






abbreviation "committedTransactions C \<equiv> {txn. txStatus C txn \<triangleq> Committed }"



abbreviation "emptyOperationContext \<equiv> \<lparr> calls = Map.empty, happensBefore = {}\<rparr>"



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
        calls = Map.empty,
        happensBefore = {},
        callOrigin  = Map.empty,
        txOrigin = Map.empty,
        knownIds = {},
        invocOp = Map.empty,
        invocRes = Map.empty
\<rparr>"

definition isCommittedH where
  "isCommittedH state_callOrigin state_txStatus c \<equiv> \<exists>tx. state_callOrigin c \<triangleq> tx \<and> state_txStatus tx \<triangleq> Committed"

abbreviation isCommitted :: "('proc, 'ls, 'op, 'any) state \<Rightarrow> callId \<Rightarrow> bool" where
  "isCommitted state \<equiv> isCommittedH (callOrigin state) (txStatus state)"

definition "committedCallsH state_callOrigin state_txStatus \<equiv> 
   {c. isCommittedH state_callOrigin state_txStatus c}"

abbreviation committedCalls :: "('proc, 'ls, 'op, 'any) state \<Rightarrow> callId set" where
  "committedCalls state \<equiv> committedCallsH (callOrigin state) (txStatus state)"

definition invContextH  where
  "invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
   state_calls state_knownIds state_invocOp state_invocRes = \<lparr>
        calls = state_calls |` committedCallsH state_callOrigin state_txStatus , 
        happensBefore = state_happensBefore |r committedCallsH state_callOrigin state_txStatus , 
        callOrigin  = state_callOrigin |` committedCallsH state_callOrigin state_txStatus,
        txOrigin = state_txOrigin |` {t. state_txStatus t \<triangleq> Committed},
        knownIds = state_knownIds,
        invocOp = state_invocOp,
        invocRes = state_invocRes
      \<rparr>"


lemma invContextH_calls:
"calls (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_calls |` committedCallsH state_callOrigin state_txStatus"
  by (auto simp add: invContextH_def)


lemma invContextH_happensBefore:
"happensBefore (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes) 
= state_happensBefore |r committedCallsH state_callOrigin state_txStatus "
  by (auto simp add: invContextH_def)


lemma invContextH_i_callOrigin:
"callOrigin (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_callOrigin |` committedCallsH state_callOrigin state_txStatus"
by (auto simp add: invContextH_def)

lemma invContextH_i_txOrigin:
"txOrigin (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
=  state_txOrigin |` {t. state_txStatus t \<triangleq> Committed}"
  by (auto simp add: invContextH_def)

lemma invContextH_i_knownIds:
"knownIds (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_knownIds"
  by (auto simp add: invContextH_def)

lemma invContextH_i_invocOp:
"invocOp (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_invocOp"
by (auto simp add: invContextH_def)


lemma invContextH_i_invocRes:
"invocRes (invContextH state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
=  state_invocRes"
by (auto simp add: invContextH_def)

abbreviation invContext where
  "invContext state \<equiv>
  invContextH
  (callOrigin state)
  (txOrigin state)
  (txStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocOp state)
  (invocRes state)"



definition invContextH2  where
  "invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
   state_calls state_knownIds state_invocOp state_invocRes = \<lparr>
        calls = state_calls , 
        happensBefore = state_happensBefore, 
        callOrigin  = state_callOrigin,
        txOrigin = state_txOrigin,
        knownIds = state_knownIds,
        invocOp = state_invocOp,
        invocRes = state_invocRes
      \<rparr>"


lemma invContextH2_calls:
"calls (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_calls"
  by (auto simp add: invContextH2_def)


lemma invContextH2_happensBefore:
"happensBefore (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes) 
= state_happensBefore"
  by (auto simp add: invContextH2_def)


lemma invContextH2_i_callOrigin:
"callOrigin (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_callOrigin "
by (auto simp add: invContextH2_def)

lemma invContextH2_i_txOrigin:
"txOrigin (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
=  state_txOrigin "
  by (auto simp add: invContextH2_def)

lemma invContextH2_i_knownIds:
"knownIds (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_knownIds"
  by (auto simp add: invContextH2_def)

lemma invContextH2_i_invocOp:
"invocOp (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
= state_invocOp"
by (auto simp add: invContextH2_def)


lemma invContextH2_i_invocRes:
"invocRes (invContextH2 state_callOrigin state_txOrigin state_txStatus state_happensBefore 
      state_calls state_knownIds state_invocOp state_invocRes ) 
=  state_invocRes"
by (auto simp add: invContextH2_def)


lemmas invContextH2_simps =
invContextH_calls
invContextH_happensBefore
invContextH_i_callOrigin
invContextH_i_txOrigin
invContextH_i_knownIds
invContextH_i_invocOp
invContextH_i_invocRes
invContextH2_calls
invContextH2_happensBefore
invContextH2_i_callOrigin
invContextH2_i_txOrigin
invContextH2_i_knownIds
invContextH2_i_invocOp
invContextH2_i_invocRes

abbreviation invContext' where
  "invContext' state \<equiv>
  invContextH2
  (callOrigin state)
  (txOrigin state)
  (txStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocOp state)
  (invocRes state)"

lemma invContext'_truncate: "invContext' state = invContext.truncate state"
  by (auto simp add: invContextH2_def invContext.defs)


definition callsInTransactionH :: "(callId \<rightharpoonup> txId) \<Rightarrow> txId set \<Rightarrow> callId set" where
  "callsInTransactionH origins txns  \<equiv> {c. \<exists>txn\<in>txns. origins c \<triangleq> txn }"

lemma callsInTransactionH_contains:
  "c\<in>callsInTransactionH origins txns \<longleftrightarrow> (case origins c of Some txn \<Rightarrow>  txn \<in> txns | None \<Rightarrow> False)"
  by (auto simp add: callsInTransactionH_def split: option.splits)

abbreviation 
  "callsInTransaction S txns \<equiv> callsInTransactionH (callOrigin S) txns"  


lemma invContextSnapshot_eq:
  assumes "c_calls = committedCallsH (callOrigin state) (txStatus state)"
    and "c_txns = {t. txStatus state t \<triangleq> Committed}"
  shows
    "invContext state =  \<lparr>
        calls = calls state |` c_calls , 
        happensBefore = happensBefore state |r c_calls , 
        callOrigin  = callOrigin state |` c_calls,
        txOrigin = txOrigin state |` c_txns,
        knownIds = knownIds state,
        invocOp = invocOp state,
        invocRes = invocRes state\<rparr>"
  by (auto simp add: assms  invContextH_def)



lemma invContext_eqI: "\<lbrakk>
calls x = calls y;
happensBefore x = happensBefore y;
callOrigin x = callOrigin y;
txOrigin x = txOrigin y;
knownIds x = knownIds y;
invocOp x = invocOp y;
invocRes x = invocRes y
\<rbrakk> \<Longrightarrow> x = (y::('proc, 'op, 'any) invContext)"
  by auto



text_raw \<open>\DefineSnippet{repliss_sem_action}{\<close>
datatype ('proc, 'op, 'any) action =
    ALocal bool
  | ANewId 'any
  | ABeginAtomic txId "(callId set)"
  | AEndAtomic
  | ADbOp callId 'op 'any
  | AInvoc 'proc
  | AReturn 'any
  | ACrash  
  | AInvcheck bool
text_raw \<open>}%EndSnippet\<close>



definition "is_AInvcheck a \<equiv> \<exists>r. a = AInvcheck r"


definition 
  "isACrash a \<equiv> case a of ACrash \<Rightarrow> True | _ \<Rightarrow> False"

schematic_goal [simp]: "isACrash (ALocal b) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (ANewId u) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (ABeginAtomic t newTxns) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (AEndAtomic) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (ADbOp c oper res) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (AInvoc proc) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (AReturn res) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (ACrash) = ?x" by (auto simp add: isACrash_def)
schematic_goal [simp]: "isACrash (AInvcheck c) = ?x" by (auto simp add: isACrash_def) 


definition chooseSnapshot_h where
"chooseSnapshot_h snapshot vis txSt cOrigin hb \<equiv>
  \<exists>newTxns newCalls.
  \<comment> \<open>  choose a set of committed transactions to add to the snapshot  \<close>
   (\<forall>txn\<in>newTxns. txSt txn \<triangleq> Committed)
   \<comment> \<open>  determine new visible calls: downwards-closure wrt. causality   \<close>
   \<and> newCalls = callsInTransactionH cOrigin newTxns \<down> hb
   \<comment> \<open>  transaction snapshot  \<close>
   \<and> snapshot = vis \<union> newCalls"

abbreviation chooseSnapshot :: "callId set \<Rightarrow> callId set \<Rightarrow> ('proc::valueType, 'ls, 'op, 'any::valueType) state \<Rightarrow> bool" where 
"chooseSnapshot snapshot vis S \<equiv> chooseSnapshot_h snapshot vis (txStatus S) (callOrigin S) (happensBefore S)"

lemma chooseSnapshot_def: \<comment> \<open>old definition\<close>
"chooseSnapshot snapshot vis S = (
  \<exists>newTxns newCalls.
  \<comment> \<open>  choose a set of committed transactions to add to the snapshot  \<close>
   newTxns \<subseteq> committedTransactions S
   \<comment> \<open>  determine new visible calls: downwards-closure wrt. causality   \<close>
   \<and> newCalls = callsInTransaction S newTxns \<down> happensBefore S
   \<comment> \<open>  transaction snapshot  \<close>
   \<and> snapshot = vis \<union> newCalls)"
  by (auto simp add: chooseSnapshot_h_def)

schematic_goal chooseSnapshot_def2:
"chooseSnapshot snapshot vis S = ?x"
  by (subst chooseSnapshot_h_def, rule refl)

thm chooseSnapshot_def2

schematic_goal callsInTransaction_def:
"callsInTransaction S newTxns = ?x"
  by (subst callsInTransactionH_def, rule refl)


 text \<open>
\DefineSnippet{chooseSnapshot_def}{
  @{thm [display] chooseSnapshot_def}
}%EndSnippet

\DefineSnippet{chooseSnapshot_def2}{
  @{thm [display] chooseSnapshot_def2}
}%EndSnippet

\DefineSnippet{downwardsClosure_in}{
  @{thm [display] downwardsClosure_in}
}%EndSnippet

\DefineSnippet{callsInTransaction_def}{
  @{thm [display] callsInTransaction_def}
}%EndSnippet

 \<close>






inductive step :: "('proc::valueType, 'ls, 'op, 'any::valueType) state \<Rightarrow> (invocId \<times> ('proc, 'op, 'any) action) \<Rightarrow> ('proc, 'ls, 'op, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>" 60) where
  local: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = LocalStep ok ls' 
   \<rbrakk> \<Longrightarrow> S ~~ (i, ALocal ok)  \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls') \<rparr>)"
| newId: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = NewId ls';
   generatedIds S (uid) = None;
   uniqueIds uidv = {uid}; \<comment> \<open>  there is exactly one unique id  \<close>
   ls' uidv \<triangleq> ls'';
   uid = to_nat uidv
   \<rbrakk> \<Longrightarrow> S ~~ (i, ANewId uidv) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls''), 
                                   generatedIds := (generatedIds S)(uid \<mapsto> i)  \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTx S i = None;   
   txStatus S t = None;
   visibleCalls S i \<triangleq> vis;
   chooseSnapshot snapshot vis S
   \<rbrakk> \<Longrightarrow> S ~~ (i, ABeginAtomic t snapshot) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls'), 
                currentTx := (currentTx S)(i \<mapsto> t),
                txStatus := (txStatus S)(t \<mapsto> Uncommitted),
                txOrigin := (txOrigin S)(t \<mapsto> i),
                visibleCalls := (visibleCalls S)(i \<mapsto> snapshot)\<rparr>)" 
| endAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTx S i \<triangleq> t
   \<rbrakk> \<Longrightarrow> S ~~ (i, AEndAtomic) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls'), 
                currentTx := (currentTx S)(i := None),
                txStatus := (txStatus S)(t \<mapsto> Committed) \<rparr>)"
| dbop: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = DbOperation Op ls';
   currentTx S i \<triangleq> t;
   calls S c = None;
   querySpec (prog S) Op (getContext S i)  res;
   visibleCalls S i \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  S ~~ (i, ADbOp c Op res) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls' res), 
                calls := (calls S)(c \<mapsto> Call Op res ),
                callOrigin := (callOrigin S)(c \<mapsto> t),
                visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>)"              

| invocation:
  "\<lbrakk>localState S i = None;
   procedure (prog S) proc = (initialState, impl);
   uniqueIds proc \<subseteq> knownIds S;
   invocOp S i = None
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvoc proc) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> initialState),
                 currentProc := (currentProc S)(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S)(i \<mapsto> {}),
                 invocOp := (invocOp S)(i \<mapsto> proc) \<rparr>)"                  
| return:
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = Return res;
   currentTx S i = None
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AReturn res) \<leadsto> (S\<lparr>localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocRes := (invocRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>)"                
| crash:
  "localState S i \<triangleq> ls
   \<Longrightarrow> S ~~ (i, ACrash) \<leadsto> (S\<lparr>localState := (localState S)(i := None),
                 currentTx := (currentTx S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None) \<rparr>)"                  
| invCheck: \<comment> \<open>checks a snapshot\<close>
  "\<lbrakk>invariant (prog S) (invContext S) = res
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvcheck res) \<leadsto> S"   




inductive_simps step_simp_ALocal: "A ~~ (s, ALocal ok) \<leadsto> B "
inductive_simps step_simp_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_simps step_simp_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_simps step_simp_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_simps step_simp_ADbOp: "A ~~ (s, ADbOp c oper res) \<leadsto> B "
inductive_simps step_simp_AInvoc: "A ~~ (s, AInvoc proc) \<leadsto> B "
inductive_simps step_simp_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_simps step_simp_ACrash: "A ~~ (s, ACrash) \<leadsto> B "
inductive_simps step_simp_AInvcheck: "A ~~ (s, AInvcheck res) \<leadsto> B "
inductive_simps step_simps_all: "A ~~ b \<leadsto> B "

lemmas step_simps = 
  step_simp_ALocal
  step_simp_ANewId
  step_simp_ABeginAtomic
  step_simp_AEndAtomic
  step_simp_ADbOp
  step_simp_AInvoc
  step_simp_AReturn
  step_simp_ACrash
  step_simp_AInvcheck



lemmas step_intros = 
  step_simps[THEN iffToImp, simplified imp_conjL imp_ex, rule_format]


inductive_cases step_elim_ALocal: "A ~~ (s, ALocal ok) \<leadsto> B "
inductive_cases step_elim_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_cases step_elim_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_cases step_elim_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_cases step_elim_ADbOp: "A ~~ (s, ADbOp c oper res) \<leadsto> B "
inductive_cases step_elim_AInvoc: "A ~~ (s, AInvoc procname) \<leadsto> B "
inductive_cases step_elim_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_cases step_elim_ACrash: "A ~~ (s, ACrash) \<leadsto> B "
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
  step_elim_ACrash
  step_elim_AInvcheck




inductive steps :: "('proc::valueType, 'ls, 'op, 'any::valueType) state \<Rightarrow> (invocId \<times> ('proc, 'op, 'any) action) list \<Rightarrow> ('proc, 'ls, 'op, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>*" 60) where         
  steps_refl:
  "S ~~ [] \<leadsto>* S"
| steps_step:
  "\<lbrakk>S ~~ tr \<leadsto>* S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> S ~~ tr@[a] \<leadsto>* S''"


\<comment> \<open>Add some nicer syntax for Latex output:\<close>


notation (latex output)
  step ("(_) \<^latex>\<open>$\\step{\\text{\<close> (\<open>unbreakable\<close>_) \<^latex>\<open>}}$\<close> (1_)" [5,5,5]65)
notation (latex output)
  steps  ("(_) \<^latex>\<open>\\steps{\\text{\<close> (\<open>unbreakable\<close> _) \<^latex>\<open>}}\<close> (1_)" [5,5,5]65)



\<comment> \<open>with a given trace, the execution is deterministic\<close>
lemma stepDeterministic:
  assumes e1: "S ~~ tr \<leadsto> Sa" 
    and e2: "S ~~ tr \<leadsto> Sb"
  shows "Sa = Sb"
  using e1 e2 proof (induct rule: step.induct)
  qed (erule step.cases; force)+


lemma traceDeterministic:
  assumes e1: "S ~~ tr \<leadsto>* Sa" 
    and e2: "S ~~ tr \<leadsto>* Sb"
  shows "Sa = Sb"
  using e1 e2 proof (induct S tr Sa arbitrary: Sb rule: steps.induct)
  case (steps_refl S)
  then show ?case
    using steps.cases by fastforce 
next
  case (steps_step S tr S' a S'')
  then show ?case
    by (metis snoc_eq_iff_butlast stepDeterministic steps.cases) 
qed

definition initialState :: "('proc, 'ls, 'op, 'any) prog \<Rightarrow> ('proc, 'ls, 'op, 'any) state" where
  "initialState program \<equiv> \<lparr>
  calls = Map.empty,
  happensBefore = {},
  callOrigin = Map.empty,
  txOrigin = Map.empty,
  knownIds = {},
  invocOp = Map.empty,
  invocRes = Map.empty,
  prog = program,
  txStatus = Map.empty,
  generatedIds = Map.empty,
  localState = Map.empty,
  currentProc = Map.empty,
  visibleCalls = Map.empty,
  currentTx = Map.empty
\<rparr>"

type_synonym ('proc, 'op, 'any) trace = "(invocId\<times>('proc, 'op, 'any) action) list"

abbreviation get_invoc :: "invocId\<times>('proc, 'op, 'any) action \<Rightarrow> invocId" where 
"get_invoc \<equiv> fst"
abbreviation get_action :: "invocId\<times>('proc, 'op, 'any) action \<Rightarrow> ('proc, 'op, 'any) action" where 
"get_action \<equiv> snd"

definition traces where
  "traces program \<equiv> {tr. \<exists>S'. initialState program ~~ tr \<leadsto>* S'}"

definition
  "actionCorrect a \<equiv> a \<noteq> AInvcheck False \<and> a \<noteq> ALocal False"

definition traceCorrect where
  "traceCorrect trace \<equiv> (\<forall>(i,a)\<in>set trace. actionCorrect a)"

lemma traceCorrect_def': 
  "traceCorrect trace = (\<forall>e\<in>set trace. actionCorrect (get_action e))"
  by (auto simp add: traceCorrect_def)


definition programCorrect :: "('proc::valueType, 'ls, 'op::valueType, 'any::valueType) prog \<Rightarrow> bool" where
  "programCorrect program \<equiv> (\<forall>trace\<in>traces program. traceCorrect trace)"

definition "isABeginAtomic action = (case action of ABeginAtomic x newTxns \<Rightarrow> True | _ \<Rightarrow> False)"

definition "isAInvoc action = (case action of AInvoc _   \<Rightarrow> True | _ \<Rightarrow> False)"

lemma traceCorrect_append:
"traceCorrect (xs@ys) \<longleftrightarrow> traceCorrect xs \<and> traceCorrect ys"
  by (auto simp add: traceCorrect_def)

lemma traceCorrect_cons:
"traceCorrect (x#ys) \<longleftrightarrow> actionCorrect (get_action x) \<and> traceCorrect ys"
  by (auto simp add: traceCorrect_def)

lemma traceCorrect_empty:
"traceCorrect []"
  by (auto simp add: traceCorrect_def)

lemma show_programCorrect:
  assumes "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s \<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
  by (auto simp add: assms programCorrect_def traces_def)

(*
 splits a trace into three parts
  
1. part until first (s, EndAtomic) on different sessions
2. part until and including (s, EndAtomic); same invocId
3. rest
*)
fun splitTrace :: "invocId \<Rightarrow> ('proc, 'op, 'any) trace \<Rightarrow> (('proc, 'op, 'any) trace \<times> ('proc, 'op, 'any) trace \<times> ('proc, 'op, 'any) trace)" where
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
  proof (induct arbitrary: h c t rule: splitTrace.induct)
  qed (auto split: if_splits prod.splits)

lemma splitTrace_len: 
  assumes a: "splitTrace s tr = (h,c,t)"
  shows "length h \<le> length tr"
    and "length c \<le> length tr"
    and "length t \<le> length tr"
  using a proof (induct arbitrary: h c t rule: splitTrace.induct)
qed (auto simp add: le_SucI split: if_splits prod.splits)

lemma splitTrace_len2: 
  assumes a: "(h,c,t) = splitTrace s tr"
  shows "length h \<le> length tr"
    and "length c \<le> length tr"
    and "length t \<le> length tr"
  using a by (metis splitTrace_len(1), metis splitTrace_len(2), metis splitTrace_len(3))

declare splitTrace.simps[simp del]

  
function (sequential) compactTrace :: "invocId \<Rightarrow> ('proc, 'op, 'any) trace \<Rightarrow> ('proc, 'op, 'any) trace" where
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
by pat_completeness auto
termination
  by (lexicographic_order simp add: splitTrace_len2 )

lemma compactTrace_complete: 
  "mset (compactTrace s tr) = mset tr"
proof (induct rule: compactTrace.induct)
qed (auto simp add: splitTrace_complete split: prod.splits)

declare compactTrace_step[simp del]


lemma steps_appendBack:
  "(A ~~ tr @ [a] \<leadsto>* C) \<longleftrightarrow> (\<exists>B. (A ~~ tr \<leadsto>* B) \<and> (B ~~ a \<leadsto> C))"
  by (auto simp add: steps_step, (metis snoc_eq_iff_butlast steps.cases))



lemma steps_append: 
  "(A ~~ tra@trb \<leadsto>* C) \<longleftrightarrow> (\<exists>B. (A ~~ tra \<leadsto>* B) \<and> (B ~~ trb \<leadsto>* C))"
proof (induct trb arbitrary: C rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_Nil2 snoc_eq_iff_butlast steps.cases steps_refl) 
next
  case (snoc a trb)
  show ?case
    by (metis (no_types, lifting) append_assoc snoc.hyps steps_appendBack) 
qed

lemma steps_append2: 
  assumes "A ~~ tra \<leadsto>* B"
  shows "(A ~~ tra@trb \<leadsto>* C) \<longleftrightarrow> (B ~~ trb \<leadsto>* C)"
  using assms steps_append traceDeterministic by blast


lemma steps_single: "(A ~~ [a] \<leadsto>* B) \<longleftrightarrow> (A ~~ a \<leadsto> B)"
  by (metis append_Nil steps_appendBack steps_refl traceDeterministic)

lemma steps_empty: "(A ~~ [] \<leadsto>* B) \<longleftrightarrow> (A = B)"
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

lemma move_exists_outside_and: "((\<exists>x. P x) \<and> Q) \<longleftrightarrow> (\<exists>x. P x \<and> Q) "
  by auto

lemma exists_eq_rewrite:
  shows "(\<exists>x. x = y \<and> Q x y) \<longleftrightarrow> Q y y"
  by (metis )

lemma exists_reorder1: "(\<exists>x a. P x a) \<longleftrightarrow> (\<exists>a x. P x a)"  by metis
lemma exists_reorder2: "(\<exists>x a b. P x a b) \<longleftrightarrow> (\<exists>a b x. P x a b)"  by metis
lemma exists_reorder3: "(\<exists>x a b c. P x a b c) \<longleftrightarrow> (\<exists>a b c x. P x a b c)"  by metis
lemma exists_reorder4: "(\<exists>x a b c d. P x a b c d) \<longleftrightarrow> (\<exists>a b c d x. P x a b c d)"  by metis
lemma exists_reorder5: "(\<exists>x a b c d e. P x a b c d e) \<longleftrightarrow> (\<exists>a b c d e x. P x a b c d e)"  by metis
lemma exists_reorder6: "(\<exists>x a b c d e f. P x a a b c d e f) \<longleftrightarrow> (\<exists>a a b c d e f x. P x a a b c d e f)"  by metis

method create_step_simp_rule =
  (subst steps_appendFront,
  subst step_simps,
   (subst move_exists_outside_and conj_assoc)+,
  ((subst exists_reorder6 
      | subst exists_reorder5
      | subst exists_reorder4
      | subst exists_reorder3
      | subst exists_reorder2
      | subst exists_reorder1)?
    , subst exists_eq_rewrite),
  simp)

schematic_goal steps_simp_ALocal: "(A ~~ (i, ALocal ok)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ANewId: "(A ~~ (i, ANewId n)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ABeginAtomic: "(A ~~ (i, ABeginAtomic t newTxns)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AEndAtomic: "(A ~~ (i, AEndAtomic)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ADbOp: "(A ~~ (i, ADbOp c oper res)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AInvoc: "(A ~~ (i, AInvoc procname)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AReturn: "(A ~~ (i, AReturn res)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ACrash: "(A ~~ (i, ACrash)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AInvcheck: "(A ~~ (i, AInvcheck invi)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule

lemmas steps_simps =
  steps_simp_ALocal
  steps_simp_ANewId
  steps_simp_ABeginAtomic
  steps_simp_AEndAtomic
  steps_simp_ADbOp
  steps_simp_AInvoc
  steps_simp_AReturn
  steps_simp_ACrash
  steps_simp_AInvcheck


end
