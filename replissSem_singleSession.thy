theory replissSem_singleSession
imports replissSem1
begin

section {* Single session semantics *}

text {*
The single session semantics only work on a single session.
All other sessions are simulated by nondeterministic state changes, with respect to the invariant.
*}

  
inductive step_s :: "state \<Rightarrow> (session \<times> action \<times> bool) \<Rightarrow> state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S" 60) where
  local: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = LocalStep ls' 
   \<rbrakk> \<Longrightarrow> C ~~ (s, ALocal, True)  \<leadsto>\<^sub>S (C\<lparr>localState := (localState C)(s \<mapsto> ls') \<rparr>)"
| newId: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = NewId ls';
   uid \<notin> generatedIds C
   \<rbrakk> \<Longrightarrow> C ~~ (s, ANewId uid, True) \<leadsto>\<^sub>S (C\<lparr>localState := (localState C)(s \<mapsto> ls' uid), 
                                   generatedIds := generatedIds C \<union> {uid} \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTransaction C s = None;
   transactionStatus C t = None;
   (* we assume a nondeterministic state change to C' here *)
   (* new transaction has no calls yet *)
   (* well formed history *)
   (* invariant maintained *)
   \<And>s'. invariant (prog C) (invContext C' s')
   (* causally consistent *)
   (* transaction consistent *)
   (* monotonic growth of visible calls*)
   (* monotonic growth of callops *)
   (* monotonic growth of happens-before *)
   (*  --> no new calls can be added before*)
   (* monotonic growth of sameTransaction *)
   (* monotonic growth of origin *)
   (* monotonic growth of invocations *)
   (* monotonic growth of invocation result *)
   (* monotonic growth of invocation happens-before *)
   (*  --> no new calls can be added before*)
   \<rbrakk> \<Longrightarrow> C ~~ (s, ABeginAtomic t, True) \<leadsto>\<^sub>S (C'\<lparr>localState := (localState C')(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C')(s \<mapsto> t),
                transactionStatus := (transactionStatus C')(t \<mapsto> Uncommited) \<rparr>)"
| endAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTransaction C s \<triangleq> t;
   C' = (C\<lparr>localState := (localState C)(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C)(s := None),
                transactionStatus := (transactionStatus C)(t \<mapsto> Commited) \<rparr>);
   valid = invariant (prog C) (invContext C s)
   \<rbrakk> \<Longrightarrow> C ~~ (s, AEndAtomic, valid) \<leadsto>\<^sub>S C'"
| dbop: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = DbOperation Op args ls';
   currentTransaction C s \<triangleq> t;
   calls C c = None;
   querySpec (prog C) Op args (getContext C s)  res;
   visibleCalls C s \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  C ~~ (s, ADbOp c Op args res, True) \<leadsto>\<^sub>S (C\<lparr>localState := (localState C)(s \<mapsto> ls' res), 
                calls := (calls C)(c \<mapsto> Call Op args res ),
                callOrigin := (callOrigin C)(c \<mapsto> t),
                visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore C \<union> vis \<times> {c}  \<rparr>)"                
(* TODO integrate pull into beginAtomic
| pull:
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   (* choose a set of commited transactions to pull in*)
   newTxns \<subseteq> commitedTransactions C;
   (* pull in calls from the transactions and their dependencies *)
   newCalls = callsInTransaction C newTxns \<down> happensBefore C
   \<rbrakk> \<Longrightarrow>  C ~~ (s, APull newTxns) \<leadsto>\<^sub>S (C\<lparr> visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> newCalls)\<rparr>)"                         
*)
| invocation:
  "\<lbrakk>localState C s = None;
   procedure (prog C) procName args \<triangleq> (initState, impl);
   uniqueIdsInList args \<subseteq> knownIds C;
   invocationOp C s = None;
   C' = (C\<lparr>localState := (localState C)(s \<mapsto> initState),
                 currentProc := (currentProc C)(s \<mapsto> impl),
                 visibleCalls := (visibleCalls C)(s \<mapsto> {}),
                 invocationOp := (invocationOp C)(s \<mapsto> (procName, args)) \<rparr>);
   valid = invariant (prog C) (invContext C s)              
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvoc procName args, valid) \<leadsto>\<^sub>S C'"       
(* TODO do we have to consider concurrent actions here? *)                 
| return:
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = Return res;
   currentTransaction C s = None;
   C' = (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None),
                 invocationRes := (invocationRes C)(s \<mapsto> res),
                 knownIds := knownIds C \<union> uniqueIds res\<rparr>);
   valid = invariant (prog C) (invContext C s)                   
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AReturn res, valid) \<leadsto>\<^sub>S C'"
(*                  
| fail:
  "      C ~~ (s, AFail) \<leadsto>\<^sub>S (C\<lparr>localState := (localState C)(s := None),
                 currentProc := (currentProc C)(s := None),
                 visibleCalls := (visibleCalls C)(s := None) \<rparr>)"                  
*)
(* TODO integrate invariant check at right places
| invCheck:
  "\<lbrakk>currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   invariant (prog C) (invContext C s) = res
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvcheck res) \<leadsto>\<^sub>S C"   
*)
  
inductive steps_s :: "state \<Rightarrow> session \<times> (action \<times> bool) list \<Rightarrow> state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S*" 60) where         
  steps_refl:
  "S ~~ (s, []) \<leadsto>\<^sub>S* S"
| steps_step:
  "\<lbrakk>S ~~ (s, tr) \<leadsto>\<^sub>S* S'; S' ~~ (s,a) \<leadsto>\<^sub>S S''\<rbrakk> \<Longrightarrow> S ~~ (s, tr@[a]) \<leadsto>\<^sub>S* S''"
  

definition traceCorrect_s where
"traceCorrect_s program trace \<equiv> (\<forall>a. (a, False) \<notin> set trace)"

definition programCorrect_s where
"programCorrect_s program \<equiv> (\<forall>init trace s S. 
      invariant program (invContext init s) 
    \<and> prog init = program
    \<and> (init ~~ (s, trace) \<leadsto>\<^sub>S* S)
    \<longrightarrow> traceCorrect_s program trace)"
  
  



end
