theory replissSem_singleSession
imports replissSem1
begin

section {* Single session semantics *}

definition 
"causallyConsistent hb vis \<equiv>
  (\<forall>c1 c2. c1\<in>vis \<and> (c2,c1)\<in> hb \<longrightarrow> c2\<in>vis)"

definition 
"transactionConsistent origin txStatus vis \<equiv>
    (\<forall>c tx. c\<in>vis \<and> origin c \<triangleq> tx \<longrightarrow> txStatus tx \<triangleq> Commited)
  \<and> (\<forall>c1 c2. c1\<in>vis \<and> origin c1 = origin c2 \<longrightarrow> c2\<in>vis)"

lemma transactionConsistent_Commited:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c\<in>vis \<and> origin c \<triangleq> tx; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus tx \<triangleq> Commited"
by (auto simp add:  transactionConsistent_def) 

lemma transactionConsistent_all_from_same:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
by (auto simp add:  transactionConsistent_def) 

definition consistentSnapshot where
"consistentSnapshot state vis \<equiv>
  vis \<subseteq> dom (calls state)
 (* causally consistent *) 
 \<and> (causallyConsistent (happensBefore state) vis)
 (*transaction consistent *)
 \<and> (transactionConsistent (callOrigin state) (transactionStatus state) vis)
"




text {* Invariant holds for all possible (causally + transaction consistent) states *}
definition invariant_all :: "state \<Rightarrow> bool" where
"invariant_all state \<equiv> 
 \<forall>vis. consistentSnapshot state vis
 \<longrightarrow> invariant (prog state) (invContextVis state vis)"


 
lemma show_invariant_all_changes:
assumes "\<And>vis. invContextVis S' vis = invContextVis S vis"
    and "prog S' = prog S"
    and "consistentSnapshot S' = consistentSnapshot S"
shows "invariant_all S' = invariant_all S"
using assms by (auto simp add: invariant_all_def)
      

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
   (* we assume a nondeterministic state change to C' here *) (* TODO add more restrictions *)
   prog C' = prog C;
   (* new transaction has no calls yet *)
   (* well formed history *)
   (* invariant maintained *)
   invariant_all C';
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
   
   (* local changes: *)
   localState C' s \<triangleq> ls';
   currentTransaction C' s \<triangleq> t;
   transactionStatus C' t \<triangleq> Uncommited
   \<rbrakk> \<Longrightarrow> C ~~ (s, ABeginAtomic t txns, True) \<leadsto>\<^sub>S C'"
| endAtomic: 
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentProc C s \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTransaction C s \<triangleq> t;
   C' = (C\<lparr>localState := (localState C)(s \<mapsto> ls'), 
                currentTransaction := (currentTransaction C)(s := None),
                transactionStatus := (transactionStatus C)(t \<mapsto> Commited) \<rparr>);
   valid = invariant_all C'
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
   uniqueIdsInList args \<subseteq> knownIds C';
   invariant_all C';
   invocationOp C' s = None;
   (* TODO some connection between C and C' or allow anything that preserves invariant? *)
   C'' = (C'\<lparr>localState := (localState C')(s \<mapsto> initState),
                 currentProc := (currentProc C')(s \<mapsto> impl),
                 visibleCalls := (visibleCalls C')(s \<mapsto> {}),
                 invocationOp := (invocationOp C')(s \<mapsto> (procName, args)) \<rparr>);
   valid = invariant_all C''  (* TODO check invariant in C ? *)            
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvoc procName args, valid) \<leadsto>\<^sub>S C''"       
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
   valid = invariant_all C'                   
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
  steps_s_refl:
  "S ~~ (s, []) \<leadsto>\<^sub>S* S"
| steps_s_step:
  "\<lbrakk>S ~~ (s, tr) \<leadsto>\<^sub>S* S'; S' ~~ (s,a) \<leadsto>\<^sub>S S''\<rbrakk> \<Longrightarrow> S ~~ (s, tr@[a]) \<leadsto>\<^sub>S* S''"
  

definition traceCorrect_s where
"traceCorrect_s program trace \<equiv> (\<forall>a. (a, False) \<notin> set trace)"

definition programCorrect_s where
"programCorrect_s program \<equiv> (\<forall>init trace s S. 
      invariant program (invContext init s) (* TODO change to inv_all ??*)
    \<and> prog init = program
    \<and> (init ~~ (s, trace) \<leadsto>\<^sub>S* S)
    \<longrightarrow> traceCorrect_s program trace)"
  
  thm steps_append
    
lemma steps_s_append: 
assumes a1: "S ~~ (s, tra) \<leadsto>\<^sub>S* S'"
    and a2: "S' ~~ (s, trb) \<leadsto>\<^sub>S* S''"
shows "S ~~ (s, tra@trb) \<leadsto>\<^sub>S* S''"
using a1 a2 proof (induct trb arbitrary: S'' rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_Nil2 snd_conv snoc_eq_iff_butlast steps_s.simps) 
next
  case (snoc x xs)
  
  
  obtain S_mid 
   where  steps_xs: "S' ~~ (s, xs) \<leadsto>\<^sub>S* S_mid"
   and step_x: "S_mid ~~ (s,x) \<leadsto>\<^sub>S S''"
    apply (atomize_elim)
    apply (rule steps_s.cases[OF `S' ~~ (s, xs @ [x]) \<leadsto>\<^sub>S* S''`]) 
    by auto
    
  
  have "S ~~ (s, (tra @ xs) @ [x]) \<leadsto>\<^sub>S* S''" 
  proof (rule steps_s_step)
    show "S_mid ~~ (s, x) \<leadsto>\<^sub>S S''" using step_x .
    show "S ~~ (s, tra @ xs) \<leadsto>\<^sub>S* S_mid"
      using steps_xs
      by (simp add: a1 snoc.hyps) 
  qed
  thus "S ~~ (s, tra @ xs @ [x]) \<leadsto>\<^sub>S* S''"
    by simp
qed


end
