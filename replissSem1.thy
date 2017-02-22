theory replissSem1
imports Main
  "~~/src/HOL/Library/LaTeXsugar"
(*  "~/work/afp/thys/Proof_Strategy_Language/PSL" *)
begin

abbreviation todo ("???") where "??? \<equiv> undefined"

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

record prog =
  querySpec :: "operation \<Rightarrow> any list \<Rightarrow> operationContext \<Rightarrow> any \<Rightarrow> bool"
  procedure :: "procedureName \<Rightarrow> any list \<rightharpoonup> (localState \<times> procedureImpl)"



record state = operationContext +
  prog :: prog
  localState :: "session \<rightharpoonup> localState"
  currentProc :: "session \<rightharpoonup> procedureImpl"
  visibleCalls :: "session \<rightharpoonup> callId set"
  currentTransaction :: "session \<rightharpoonup> txid"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"
  callOrigin :: "callId \<rightharpoonup> txid"
  generatedIds :: "uniqueId set"
  knownIds :: "uniqueId set"
  invocationOp :: "session \<rightharpoonup> (procedureName \<times> any list)"
  invocationRes :: "session \<rightharpoonup> any"

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

definition restrictMap :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"restrictMap S m = (\<lambda>x. if x\<in>S then m x else None)"

  
  
abbreviation eqsome :: "'a option \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<triangleq>" 69) where
 "x \<triangleq> y \<equiv> x = Some y"

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
   currentTransaction C s = None;
   querySpec (prog C) Op args (getContext C s)  res;
   visibleCalls C s \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AReturn res) \<leadsto> (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None),
                 invocationRes := (invocationRes C)(s \<mapsto> res) \<rparr>)"                
| fail:
  "      C ~~ (s, AFail) \<leadsto> (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None) \<rparr>)"                  

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



end
