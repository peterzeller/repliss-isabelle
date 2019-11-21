theory repliss_sem
  imports Main
    "HOL-Library.Multiset"
    "HOL-Library.Option_ord"
    "~~/src/HOL/Eisbach/Eisbach"
    "HOL-Library.Countable"
    utils
begin

section \<open>Semantics\<close>

text \<open>This theory describes the distributed semantics used by Repliss.
We use a fine grained interleaving semantics.
\<close>


typedecl invocId
typedecl txid
typedecl callId

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




datatype ('operation, 'any) call = Call (call_operation: 'operation) (call_res:"'any")

datatype ('ls, 'operation, 'any) localAction =
  LocalStep 'ls
  | BeginAtomic 'ls
  | EndAtomic 'ls
  | NewId "'any \<rightharpoonup> 'ls"
  | DbOperation 'operation "'any \<Rightarrow> 'ls"
  | Return 'any


type_synonym ('ls, 'operation, 'any) procedureImpl = "'ls \<Rightarrow> ('ls, 'operation, 'any) localAction"

datatype transactionStatus = Uncommitted | Committed 

instantiation transactionStatus :: linorder
begin
definition "less_eq_transactionStatus x y \<equiv> x = Uncommitted \<or> y = Committed"
definition "less_transactionStatus x y \<equiv> x = Uncommitted \<and> y = Committed"
instance
   by (standard; insert transactionStatus.exhaust;  auto simp add: less_eq_transactionStatus_def less_transactionStatus_def)
end

lemmas transactionStatus_less_simps = less_eq_transactionStatus_def less_transactionStatus_def

lemma onlyCommittedGreater: "a \<triangleq> Committed" if "a\<ge>Some Committed" for a
  by (smt dual_order.antisym dual_order.trans less_eq_option_None_is_None less_eq_option_Some less_eq_transactionStatus_def order_refl split_option_ex that)



record ('operation, 'any) operationContext = 
  calls :: "callId \<rightharpoonup> ('operation, 'any) call"
  happensBefore :: "callId rel"

record ('proc, 'operation, 'any) invariantContext = "('operation, 'any) operationContext" +
  callOrigin :: "callId \<rightharpoonup> txid"
  transactionOrigin :: "txid \<rightharpoonup> invocId"
  knownIds :: "uniqueId set"
  invocationOp :: "invocId \<rightharpoonup> 'proc"
  invocationRes :: "invocId \<rightharpoonup> 'any"

record ('proc, 'ls, 'operation, 'any) prog =
  querySpec :: "'operation \<Rightarrow> ('operation, 'any) operationContext \<Rightarrow> 'any \<Rightarrow> bool"
  procedure :: "'proc \<Rightarrow> ('ls \<times> ('ls, 'operation, 'any) procedureImpl)"
  invariant :: "('proc, 'operation, 'any) invariantContext \<Rightarrow> bool"

record ('proc, 'ls, 'operation, 'any) distributed_state = "('proc, 'operation, 'any) invariantContext" +
  prog :: "('proc, 'ls, 'operation, 'any) prog"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"
  generatedIds :: "uniqueId \<rightharpoonup> invocId" \<comment> \<open>unique identifiers and which invocId generated them\<close>

record ('proc, 'ls, 'operation, 'any) state = "('proc, 'ls, 'operation, 'any) distributed_state" + 
  localState :: "invocId \<rightharpoonup> 'ls"
  currentProc :: "invocId \<rightharpoonup> ('ls, 'operation, 'any) procedureImpl"
  visibleCalls :: "invocId \<rightharpoonup> callId set"
  currentTransaction :: "invocId \<rightharpoonup> txid"


lemma state_ext: "((x::('proc, 'ls, 'operation, 'any) state) = y) \<longleftrightarrow> (
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

lemma stateEqI: 
  assumes "calls x = calls y"
  and "happensBefore x = happensBefore y"
  and "prog x = prog y"
  and "localState x = localState y"
  and "currentProc x = currentProc y"
  and "visibleCalls x = visibleCalls y"
  and "currentTransaction x = currentTransaction y"
  and "transactionStatus x = transactionStatus y"
  and "callOrigin x = callOrigin y"
  and "transactionOrigin x = transactionOrigin y"
  and "generatedIds x = generatedIds y"
  and "knownIds x = knownIds y"
  and "invocationOp x = invocationOp y"
  and "invocationRes x = invocationRes y"
shows "(x::('proc, 'ls, 'operation, 'any) state) = y"
  using assms by (auto simp add: state_ext)

lemma state_ext_exI:
  fixes P :: "('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool"
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
callOrigin = s_callOrigin,
transactionOrigin = s_transactionOrigin,
knownIds = s_knownIds,
invocationOp = s_invocationOp,
invocationRes = s_invocationRes,
prog = s_prog,
transactionStatus = s_transactionStatus,
generatedIds = s_generatedIds,
localState = s_localState,
currentProc = s_currentProc,
visibleCalls = s_visibleCalls,
currentTransaction = s_currentTransaction
\<rparr>"
  shows "\<exists>s. P s"
  using assms by blast


lemma show_state_calls_eq:
  assumes "A = B"
  shows "\<And>x y. x = y \<Longrightarrow> A\<lparr>calls := x\<rparr> = B\<lparr>calls := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>happensBefore := x\<rparr> = B\<lparr>happensBefore := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>callOrigin := x\<rparr> = B\<lparr>callOrigin := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>transactionOrigin := x\<rparr> = B\<lparr>transactionOrigin := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>knownIds := x\<rparr> = B\<lparr>knownIds := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>invocationOp := x\<rparr> = B\<lparr>invocationOp := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>invocationRes := x\<rparr> = B\<lparr>invocationRes := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>prog := x\<rparr> = B\<lparr>prog := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>transactionStatus := x\<rparr> = B\<lparr>transactionStatus := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>generatedIds := x\<rparr> = B\<lparr>generatedIds := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>localState := x\<rparr> = B\<lparr>localState := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>currentProc := x\<rparr> = B\<lparr>currentProc := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>visibleCalls := x\<rparr> = B\<lparr>visibleCalls := y\<rparr>"
and "\<And>x y. x = y \<Longrightarrow> A\<lparr>currentTransaction := x\<rparr> = B\<lparr>currentTransaction := y\<rparr>"
  using assms  by auto

lemma state_updates_normalize:
  shows "\<And>x y. S\<lparr>happensBefore := y, calls := x\<rparr> = S\<lparr>calls := x,  happensBefore := y\<rparr>"
and "\<And>x y. S\<lparr>callOrigin := y, calls := x\<rparr> = S\<lparr>calls := x,  callOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>transactionOrigin := y, calls := x\<rparr> = S\<lparr>calls := x,  transactionOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, calls := x\<rparr> = S\<lparr>calls := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocationOp := y, calls := x\<rparr> = S\<lparr>calls := x,  invocationOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, calls := x\<rparr> = S\<lparr>calls := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, calls := x\<rparr> = S\<lparr>calls := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, calls := x\<rparr> = S\<lparr>calls := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, calls := x\<rparr> = S\<lparr>calls := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, calls := x\<rparr> = S\<lparr>calls := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, calls := x\<rparr> = S\<lparr>calls := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, calls := x\<rparr> = S\<lparr>calls := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, calls := x\<rparr> = S\<lparr>calls := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>callOrigin := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  callOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>transactionOrigin := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  transactionOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocationOp := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  invocationOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, happensBefore := x\<rparr> = S\<lparr>happensBefore := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>transactionOrigin := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  transactionOrigin := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocationOp := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  invocationOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, callOrigin := x\<rparr> = S\<lparr>callOrigin := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>knownIds := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  knownIds := y\<rparr>"
and "\<And>x y. S\<lparr>invocationOp := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  invocationOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, transactionOrigin := x\<rparr> = S\<lparr>transactionOrigin := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>invocationOp := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  invocationOp := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, knownIds := x\<rparr> = S\<lparr>knownIds := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>invocationRes := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  invocationRes := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, invocationOp := x\<rparr> = S\<lparr>invocationOp := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>prog := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  prog := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, invocationRes := x\<rparr> = S\<lparr>invocationRes := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>transactionStatus := y, prog := x\<rparr> = S\<lparr>prog := x,  transactionStatus := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, prog := x\<rparr> = S\<lparr>prog := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, prog := x\<rparr> = S\<lparr>prog := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, prog := x\<rparr> = S\<lparr>prog := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, prog := x\<rparr> = S\<lparr>prog := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, prog := x\<rparr> = S\<lparr>prog := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>generatedIds := y, transactionStatus := x\<rparr> = S\<lparr>transactionStatus := x,  generatedIds := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, transactionStatus := x\<rparr> = S\<lparr>transactionStatus := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, transactionStatus := x\<rparr> = S\<lparr>transactionStatus := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, transactionStatus := x\<rparr> = S\<lparr>transactionStatus := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, transactionStatus := x\<rparr> = S\<lparr>transactionStatus := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>localState := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  localState := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, generatedIds := x\<rparr> = S\<lparr>generatedIds := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>currentProc := y, localState := x\<rparr> = S\<lparr>localState := x,  currentProc := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, localState := x\<rparr> = S\<lparr>localState := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, localState := x\<rparr> = S\<lparr>localState := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>visibleCalls := y, currentProc := x\<rparr> = S\<lparr>currentProc := x,  visibleCalls := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, currentProc := x\<rparr> = S\<lparr>currentProc := x,  currentTransaction := y\<rparr>"
and "\<And>x y. S\<lparr>currentTransaction := y, visibleCalls := x\<rparr> = S\<lparr>visibleCalls := x,  currentTransaction := y\<rparr>"
  by auto
  




definition restrict_relation :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" (infixl "|r"  110)
  where "r |r A \<equiv> r \<inter> (A \<times> A)"


abbreviation "committedTransactions C \<equiv> {txn. transactionStatus C txn \<triangleq> Committed }"

find_consts "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set"

definition downwardsClosure :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a set"  (infixr "\<down>" 100)  where 
  "S \<down> R \<equiv> S \<union> {x | x y . (x,y)\<in>R \<and> y\<in>S}"

lemma downwardsClosure_in:
  "x \<in> S \<down> R \<longleftrightarrow> (x\<in>S \<or> (\<exists>y\<in>S. (x,y)\<in>R))"
  by (auto simp add: downwardsClosure_def)

lemma downwardsClosure_subset:
  "S \<down> R \<subseteq> S \<union> fst ` R"
  by (auto simp add: downwardsClosure_in Domain.DomainI fst_eq_Domain)




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
        transactionOrigin = Map.empty,
        knownIds = {},
        invocationOp = Map.empty,
        invocationRes = Map.empty
\<rparr>"

definition isCommittedH where
  "isCommittedH state_callOrigin state_transactionStatus c \<equiv> \<exists>tx. state_callOrigin c \<triangleq> tx \<and> state_transactionStatus tx \<triangleq> Committed"

abbreviation isCommitted :: "('proc, 'ls, 'operation, 'any) state \<Rightarrow> callId \<Rightarrow> bool" where
  "isCommitted state \<equiv> isCommittedH (callOrigin state) (transactionStatus state)"

definition "committedCallsH state_callOrigin state_transactionStatus \<equiv> 
   {c. isCommittedH state_callOrigin state_transactionStatus c}"

abbreviation committedCalls :: "('proc, 'ls, 'operation, 'any) state \<Rightarrow> callId set" where
  "committedCalls state \<equiv> committedCallsH (callOrigin state) (transactionStatus state)"

definition invContextH  where
  "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes = \<lparr>
        calls = state_calls |` committedCallsH state_callOrigin state_transactionStatus , 
        happensBefore = state_happensBefore |r committedCallsH state_callOrigin state_transactionStatus , 
        callOrigin  = state_callOrigin |` committedCallsH state_callOrigin state_transactionStatus,
        transactionOrigin = state_transactionOrigin |` {t. state_transactionStatus t \<triangleq> Committed},
        knownIds = state_knownIds,
        invocationOp = state_invocationOp,
        invocationRes = state_invocationRes
      \<rparr>"


lemma invContextH_calls:
"calls (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_calls |` committedCallsH state_callOrigin state_transactionStatus"
  by (auto simp add: invContextH_def)


lemma invContextH_happensBefore:
"happensBefore (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes) 
= state_happensBefore |r committedCallsH state_callOrigin state_transactionStatus "
  by (auto simp add: invContextH_def)


lemma invContextH_i_callOrigin:
"callOrigin (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_callOrigin |` committedCallsH state_callOrigin state_transactionStatus"
by (auto simp add: invContextH_def)

lemma invContextH_i_transactionOrigin:
"transactionOrigin (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
=  state_transactionOrigin |` {t. state_transactionStatus t \<triangleq> Committed}"
  by (auto simp add: invContextH_def)

lemma invContextH_i_knownIds:
"knownIds (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_knownIds"
  by (auto simp add: invContextH_def)

lemma invContextH_i_invocationOp:
"invocationOp (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_invocationOp"
by (auto simp add: invContextH_def)


lemma invContextH_i_invocationRes:
"invocationRes (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
=  state_invocationRes"
by (auto simp add: invContextH_def)

abbreviation invContext where
  "invContext state \<equiv>
  invContextH
  (callOrigin state)
  (transactionOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)"



definition invContextH2  where
  "invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes = \<lparr>
        calls = state_calls , 
        happensBefore = state_happensBefore, 
        callOrigin  = state_callOrigin,
        transactionOrigin = state_transactionOrigin,
        knownIds = state_knownIds,
        invocationOp = state_invocationOp,
        invocationRes = state_invocationRes
      \<rparr>"


lemma invContextH2_calls:
"calls (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_calls"
  by (auto simp add: invContextH2_def)


lemma invContextH2_happensBefore:
"happensBefore (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes) 
= state_happensBefore"
  by (auto simp add: invContextH2_def)


lemma invContextH2_i_callOrigin:
"callOrigin (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_callOrigin "
by (auto simp add: invContextH2_def)

lemma invContextH2_i_transactionOrigin:
"transactionOrigin (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
=  state_transactionOrigin "
  by (auto simp add: invContextH2_def)

lemma invContextH2_i_knownIds:
"knownIds (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_knownIds"
  by (auto simp add: invContextH2_def)

lemma invContextH2_i_invocationOp:
"invocationOp (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
= state_invocationOp"
by (auto simp add: invContextH2_def)


lemma invContextH2_i_invocationRes:
"invocationRes (invContextH2 state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
      state_calls state_knownIds state_invocationOp state_invocationRes ) 
=  state_invocationRes"
by (auto simp add: invContextH2_def)


lemmas invContextH2_simps =
invContextH_calls
invContextH_happensBefore
invContextH_i_callOrigin
invContextH_i_transactionOrigin
invContextH_i_knownIds
invContextH_i_invocationOp
invContextH_i_invocationRes
invContextH2_calls
invContextH2_happensBefore
invContextH2_i_callOrigin
invContextH2_i_transactionOrigin
invContextH2_i_knownIds
invContextH2_i_invocationOp
invContextH2_i_invocationRes

abbreviation invContext' where
  "invContext' state \<equiv>
  invContextH2
  (callOrigin state)
  (transactionOrigin state)
  (transactionStatus state)
  (happensBefore state)
  (calls state)
  (knownIds state)
  (invocationOp state)
  (invocationRes state)"




definition callsInTransactionH :: "(callId \<rightharpoonup> txid) \<Rightarrow> txid set \<Rightarrow> callId set" where
  "callsInTransactionH origins txns  \<equiv> {c. \<exists>txn\<in>txns. origins c \<triangleq> txn }"

lemma callsInTransactionH_contains:
  "c\<in>callsInTransactionH origins txns \<longleftrightarrow> (case origins c of Some txn \<Rightarrow>  txn \<in> txns | None \<Rightarrow> False)"
  by (auto simp add: callsInTransactionH_def split: option.splits)

abbreviation 
  "callsInTransaction S txns \<equiv> callsInTransactionH (callOrigin S) txns"  


lemma invContextSnapshot_eq:
  assumes "c_calls = committedCallsH (callOrigin state) (transactionStatus state)"
    and "c_txns = {t. transactionStatus state t \<triangleq> Committed}"
  shows
    "invContext state =  \<lparr>
        calls = calls state |` c_calls , 
        happensBefore = happensBefore state |r c_calls , 
        callOrigin  = callOrigin state |` c_calls,
        transactionOrigin = transactionOrigin state |` c_txns,
        knownIds = knownIds state,
        invocationOp = invocationOp state,
        invocationRes = invocationRes state\<rparr>"
  by (auto simp add: assms  invContextH_def)



lemma invariantContext_eqI: "\<lbrakk>
calls x = calls y;
happensBefore x = happensBefore y;
callOrigin x = callOrigin y;
transactionOrigin x = transactionOrigin y;
knownIds x = knownIds y;
invocationOp x = invocationOp y;
invocationRes x = invocationRes y
\<rbrakk> \<Longrightarrow> x = (y::('proc, 'operation, 'any) invariantContext)"
  by auto



datatype ('proc, 'operation, 'any) action =
  ALocal
  | ANewId 'any
  | ABeginAtomic txid "callId set"
  | AEndAtomic
  | ADbOp callId 'operation 'any
  | AInvoc 'proc
  | AReturn 'any
  | AFail  
  | AInvcheck bool


definition "is_AInvcheck a \<equiv> \<exists>r. a = AInvcheck r"


definition 
  "isAFail a \<equiv> case a of AFail \<Rightarrow> True | _ \<Rightarrow> False"

schematic_goal [simp]: "isAFail (ALocal) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ANewId u) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ABeginAtomic t newTxns) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AEndAtomic) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ADbOp c oper res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvoc proc) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AReturn res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AFail) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvcheck c) = ?x" by (auto simp add: isAFail_def) 


definition chooseSnapshot :: "callId set \<Rightarrow> callId set \<Rightarrow> ('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> bool" where
"chooseSnapshot snapshot vis S \<equiv>
  \<exists>newTxns newCalls.
  \<comment> \<open>  choose a set of committed transactions to add to the snapshot  \<close>
   newTxns \<subseteq> committedTransactions S
   \<comment> \<open>  determine new visible calls: downwards-closure wrt. causality   \<close>
   \<and> newCalls = callsInTransaction S newTxns \<down> happensBefore S
   \<comment> \<open>  transaction snapshot  \<close>
   \<and> snapshot = vis \<union> newCalls"


inductive step :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> (invocId \<times> ('proc, 'operation, 'any) action) \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>" 60) where
  local: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = LocalStep ls' 
   \<rbrakk> \<Longrightarrow> S ~~ (i, ALocal)  \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls') \<rparr>)"
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
   currentTransaction S i = None;   
   transactionStatus S t = None;
   visibleCalls S i \<triangleq> vis;
   chooseSnapshot snapshot vis S
   \<rbrakk> \<Longrightarrow> S ~~ (i, ABeginAtomic t snapshot) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls'), 
                currentTransaction := (currentTransaction S)(i \<mapsto> t),
                transactionStatus := (transactionStatus S)(t \<mapsto> Uncommitted),
                transactionOrigin := (transactionOrigin S)(t \<mapsto> i),
                visibleCalls := (visibleCalls S)(i \<mapsto> snapshot)\<rparr>)" 
| endAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTransaction S i \<triangleq> t
   \<rbrakk> \<Longrightarrow> S ~~ (i, AEndAtomic) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls'), 
                currentTransaction := (currentTransaction S)(i := None),
                transactionStatus := (transactionStatus S)(t \<mapsto> Committed) \<rparr>)"
| dbop: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = DbOperation Op ls';
   currentTransaction S i \<triangleq> t;
   calls S c = None;
   querySpec (prog S) Op (getContext S i)  res;
   visibleCalls S i \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  S ~~ (i, ADbOp c Op res) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> ls' res), 
                calls := (calls S)(c \<mapsto> Call Op res ),
                callOrigin := (callOrigin S)(c \<mapsto> t),
                visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>)"              

| invocation:
  "\<lbrakk>localState S i = None; \<comment> \<open>  TODO this might not be necessary  \<close>
   procedure (prog S) proc = (initialState, impl);
   uniqueIds proc \<subseteq> knownIds S;
   invocationOp S i = None
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvoc proc) \<leadsto> (S\<lparr>localState := (localState S)(i \<mapsto> initialState),
                 currentProc := (currentProc S)(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S)(i \<mapsto> {}),
                 invocationOp := (invocationOp S)(i \<mapsto> proc) \<rparr>)"                  
| return:
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = Return res;
   currentTransaction S i = None
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AReturn res) \<leadsto> (S\<lparr>localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>)"                
| fail:
  "localState S i \<triangleq> ls
   \<Longrightarrow> S ~~ (i, AFail) \<leadsto> (S\<lparr>localState := (localState S)(i := None),
                 currentTransaction := (currentTransaction S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None) \<rparr>)"                  
| invCheck: \<comment> \<open>checks a snapshot\<close>
  "\<lbrakk>invariant (prog S) (invContext S) = res
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvcheck res) \<leadsto> S"   

inductive_simps step_simp_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_simps step_simp_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_simps step_simp_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_simps step_simp_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_simps step_simp_ADbOp: "A ~~ (s, ADbOp c oper res) \<leadsto> B "
inductive_simps step_simp_AInvoc: "A ~~ (s, AInvoc proc) \<leadsto> B "
inductive_simps step_simp_AReturn: "A ~~ (s, AReturn res) \<leadsto> B "
inductive_simps step_simp_AFail: "A ~~ (s, AFail) \<leadsto> B "
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
  step_simp_AFail
  step_simp_AInvcheck

inductive_cases step_elim_ALocal: "A ~~ (s, ALocal) \<leadsto> B "
inductive_cases step_elim_ANewId: "A ~~ (s, ANewId n) \<leadsto> B "
inductive_cases step_elim_ABeginAtomic: "A ~~ (s, ABeginAtomic t newTxns) \<leadsto> B "
inductive_cases step_elim_AEndAtomic: "A ~~ (s, AEndAtomic) \<leadsto> B "
inductive_cases step_elim_ADbOp: "A ~~ (s, ADbOp c oper res) \<leadsto> B "
inductive_cases step_elim_AInvoc: "A ~~ (s, AInvoc procname) \<leadsto> B "
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

inductive steps :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> (invocId \<times> ('proc, 'operation, 'any) action) list \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>*" 60) where         
  steps_refl:
  "S ~~ [] \<leadsto>* S"
| steps_step:
  "\<lbrakk>S ~~ tr \<leadsto>* S'; S' ~~ a \<leadsto> S''\<rbrakk> \<Longrightarrow> S ~~ tr@[a] \<leadsto>* S''"





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
  thm steps.induct
  case (steps_refl S)
  then show ?case
    using steps.cases by fastforce 
next
  case (steps_step S tr S' a S'')
  then show ?case
    by (metis snoc_eq_iff_butlast stepDeterministic steps.cases) 
qed

definition initialState :: "('proc, 'ls, 'operation, 'any) prog \<Rightarrow> ('proc, 'ls, 'operation, 'any) state" where
  "initialState program \<equiv> \<lparr>
  calls = Map.empty,
  happensBefore = {},
  callOrigin = Map.empty,
  transactionOrigin = Map.empty,
  knownIds = {},
  invocationOp = Map.empty,
  invocationRes = Map.empty,
  prog = program,
  transactionStatus = Map.empty,
  generatedIds = Map.empty,
  localState = Map.empty,
  currentProc = Map.empty,
  visibleCalls = Map.empty,
  currentTransaction = Map.empty
\<rparr>"

type_synonym ('proc, 'operation, 'any) trace = "(invocId\<times>('proc, 'operation, 'any) action) list"

definition traces where
  "traces program \<equiv> {tr | tr S' . initialState program ~~ tr \<leadsto>* S'}"

definition traceCorrect where
  "traceCorrect trace \<equiv> (\<forall>s. (s, AInvcheck False) \<notin> set trace)"

definition programCorrect :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) prog \<Rightarrow> bool" where
  "programCorrect program \<equiv> (\<forall>trace\<in>traces program. traceCorrect trace)"

definition "isABeginAtomic action = (case action of ABeginAtomic x newTxns \<Rightarrow> True | _ \<Rightarrow> False)"

definition "isAInvoc action = (case action of AInvoc _   \<Rightarrow> True | _ \<Rightarrow> False)"


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
fun splitTrace :: "invocId \<Rightarrow> ('proc, 'operation, 'any) trace \<Rightarrow> (('proc, 'operation, 'any) trace \<times> ('proc, 'operation, 'any) trace \<times> ('proc, 'operation, 'any) trace)" where
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

  
function (sequential) compactTrace :: "invocId \<Rightarrow> ('proc, 'operation, 'any) trace \<Rightarrow> ('proc, 'operation, 'any) trace" where
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

schematic_goal steps_simp_ALocal: "(A ~~ (i, ALocal)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ANewId: "(A ~~ (i, ANewId n)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ABeginAtomic: "(A ~~ (i, ABeginAtomic t newTxns)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AEndAtomic: "(A ~~ (i, AEndAtomic)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_ADbOp: "(A ~~ (i, ADbOp c oper res)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AInvoc: "(A ~~ (i, AInvoc procname)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AReturn: "(A ~~ (i, AReturn res)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AFail: "(A ~~ (i, AFail)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule
schematic_goal steps_simp_AInvcheck: "(A ~~ (i, AInvcheck invi)#rest \<leadsto>* B) \<longleftrightarrow> ?R"  by create_step_simp_rule

lemmas steps_simps =
  steps_simp_ALocal
  steps_simp_ANewId
  steps_simp_ABeginAtomic
  steps_simp_AEndAtomic
  steps_simp_ADbOp
  steps_simp_AInvoc
  steps_simp_AReturn
  steps_simp_AFail
  steps_simp_AInvcheck


end
