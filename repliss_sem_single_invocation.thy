theory repliss_sem_single_invocation
  imports repliss_sem execution_invariants
begin


section {* Single invocation semantics *}

text {* This theory describes the single-invocation semantics used for our proof approach. *}

definition 
"causallyConsistent hb vis \<equiv>
  (\<forall>c1 c2. c1\<in>vis \<and> (c2,c1)\<in> hb \<longrightarrow> c2\<in>vis)"

definition 
"transactionConsistent origin txStatus vis \<equiv>
    (\<forall>c tx. c\<in>vis \<and> origin c \<triangleq> tx \<longrightarrow> txStatus tx \<triangleq> Commited)
  \<and> (\<forall>c1 c2. c1\<in>vis \<and> origin c1 = origin c2 \<longrightarrow> c2\<in>vis)"

lemma transactionConsistent_Commited:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c\<in>vis; origin c \<triangleq> tx; origin c \<triangleq> tx\<rbrakk> \<Longrightarrow> txStatus tx \<triangleq> Commited"
by (auto simp add:  transactionConsistent_def) 

lemma transactionConsistent_all_from_same:
shows "\<lbrakk>transactionConsistent origin txStatus vis; c1\<in>vis; origin c1 = origin c2\<rbrakk> \<Longrightarrow> c2\<in>vis"
by (auto simp add:  transactionConsistent_def) 

definition consistentSnapshotH where
"consistentSnapshotH s_calls s_happensBefore s_callOrigin s_transactionStatus vis \<equiv>
  vis \<subseteq> dom s_calls
 (* causally consistent *) 
 \<and> (causallyConsistent s_happensBefore vis)
 (*transaction consistent *)
 \<and> (transactionConsistent s_callOrigin s_transactionStatus vis)
"

abbreviation consistentSnapshot where
"consistentSnapshot state vis \<equiv>
consistentSnapshotH (calls state) (happensBefore state) (callOrigin state) (transactionStatus state) vis"

lemma show_consistentSnapshot:
  assumes "vis \<subseteq> dom s_calls"
and "causallyConsistent s_happensBefore vis"
and "transactionConsistent s_callOrigin s_transactionStatus vis"
  shows "consistentSnapshotH s_calls s_happensBefore s_callOrigin s_transactionStatus vis"
  using assms by (auto simp add: consistentSnapshotH_def)

definition 
"state_monotonicGrowth_txStable callOrigin_S callOrigin_S' transactionStatus_S' \<equiv> (\<forall>c tx. callOrigin_S c \<triangleq> tx \<and> transactionStatus_S' tx \<triangleq> Commited \<longrightarrow> callOrigin_S' c \<triangleq> tx)"

(* TODO add definitions *)
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
definition state_monotonicGrowth :: "('localState, 'any::valueType) state \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" where
"state_monotonicGrowth S' S \<equiv> 
      (* both states are wellformed *)
        state_wellFormed S'
      \<and> state_wellFormed S
      (*monotonic growth of calls*)
      \<and>  (\<forall>c i. calls S' c \<triangleq> i \<longrightarrow> calls S c \<triangleq> i)
      (*monotonic growth of happensBefore 
         --> no new calls can be added before existing calls *)
      \<and> (\<forall>c1 c2. c2\<in>dom (calls S') \<longrightarrow> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'))
      (* monotonic growth of callOrigin *)
      \<and> (\<forall>c t. callOrigin S' c \<triangleq> t \<longrightarrow> callOrigin S c \<triangleq> t)
      (* monotonic growth of generatedIds *)
      \<and> generatedIds S' \<subseteq> generatedIds S
      (* growth of known ids *)
      \<and> knownIds S' \<subseteq> knownIds S
      (* monotonic growth of invocationOp *)
      \<and> (\<forall>s i. invocationOp S' s \<triangleq> i \<longrightarrow> invocationOp S s \<triangleq> i)
      (* monotonic growth of invocationRes *)
      \<and> (\<forall>s i. invocationRes S' s \<triangleq> i \<longrightarrow> invocationRes S s \<triangleq> i)
      (* transactionStatus ??? may change, irrelevant *)
      \<and> (\<forall>tx. transactionStatus S' tx \<le> transactionStatus S tx )
      (* no new calls are added to committed transactions *)
      \<and> state_monotonicGrowth_txStable (callOrigin S) (callOrigin S') (transactionStatus S')
      (* monotonic growth of transaction origin  *)
      \<and> (\<forall>t i . transactionOrigin S' t \<triangleq> i \<longrightarrow> transactionOrigin S t \<triangleq> i)
      (* no new calls are added before existing calls *)
      \<and> (\<forall>c c' x y. calls S' c = None \<and> calls S c \<triangleq> x \<and> calls S' c' \<triangleq> y  \<longrightarrow> (c,c') \<notin> happensBefore S')
      (* no new calls are added to committed transactions *)
      \<and> (\<forall>c tx. callOrigin S c \<triangleq> tx \<and> calls S' c = None  \<longrightarrow> transactionStatus S' tx \<noteq> Some Commited)
      (* Program unchanged *)
      \<and> prog S = prog S'"


lemma state_monotonicGrowth_wf1: 
  assumes "state_monotonicGrowth S' S"
  shows "state_wellFormed S'"
    using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_wf2: 
  assumes "state_monotonicGrowth S' S"
  shows "state_wellFormed S"
    using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_no_new_calls_before_existing: 
  assumes "state_monotonicGrowth S' S"
    and "calls S' c = None"
    and "calls S c \<triangleq> x"
    and "calls S' c \<triangleq> y"
  shows "(c,c') \<notin> happensBefore S'"
    using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_no_new_calls_in_committed_transactions: 
  assumes "state_monotonicGrowth S' S"
    and "callOrigin S c \<triangleq> tx"
    and "calls S' c = None"
  shows "transactionStatus S' tx \<noteq> Some Commited"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_transactionOrigin: 
  assumes "state_monotonicGrowth S' S" 
    and "transactionOrigin S' t \<triangleq> i"
  shows "transactionOrigin S t \<triangleq> i"
  using assms by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_calls:
  assumes "state_monotonicGrowth S' S"
  shows "calls S' c \<triangleq> info \<Longrightarrow> calls S c \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_happensBefore:
  assumes "state_monotonicGrowth S' S"
  shows "c2\<in>dom (calls S') \<Longrightarrow> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S')"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_callOrigin:
  assumes "state_monotonicGrowth S' S"
  shows "callOrigin S' c \<triangleq> t \<Longrightarrow> callOrigin S c \<triangleq> t"
  using assms state_monotonicGrowth_def by fastforce 

lemma state_monotonicGrowth_callOrigin2:
  assumes "state_monotonicGrowth S' S"
  shows "callOrigin S c = None \<Longrightarrow> callOrigin S' c = None"
  using assms domIff state_monotonicGrowth_callOrigin by fastforce 

lemma state_monotonicGrowth_generatedIds:
  assumes "state_monotonicGrowth S' S"
  shows "generatedIds S' \<subseteq> generatedIds S"
  using assms by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_knownIds:
  assumes "state_monotonicGrowth S' S"
  shows "knownIds S' \<subseteq> knownIds S"
  using assms by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_invocationOp:
  assumes "state_monotonicGrowth S' S"
  shows "invocationOp S' s \<triangleq> info \<Longrightarrow> invocationOp S s \<triangleq> info"
  using assms state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_invocationRes:
  assumes "state_monotonicGrowth S' S"
  shows "invocationRes S' s \<triangleq> info \<Longrightarrow> invocationRes S s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_transactionStatus:
  assumes "state_monotonicGrowth S' S"
  shows "transactionStatus S' tx \<le> transactionStatus S tx"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_transactionStatus2:
  assumes "state_monotonicGrowth S' S"
  shows "transactionStatus S' tx \<triangleq> Commited \<Longrightarrow>  transactionStatus S tx \<triangleq> Commited"
  by (smt assms onlyCommitedGreater state_monotonicGrowth_def)


lemma state_monotonicGrowth_prog:
  assumes "state_monotonicGrowth  S' S"
  shows "prog S = prog S'"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_invocationOp2:
  assumes "state_monotonicGrowth  S' S"
  shows "(invocationOp S' \<subseteq>\<^sub>m invocationOp S) "
  using assms by (auto simp add: state_monotonicGrowth_def map_le_def)

lemma state_monotonicGrowth_committed_transactions_fixed:
  assumes "state_monotonicGrowth S' S"
and "transactionStatus S' tx \<triangleq> Commited"
and "callOrigin S x \<triangleq> tx"
shows "callOrigin S' x \<triangleq> tx"
proof -
  have "x \<in> dom (callOrigin S')"
    by (meson assms(1) assms(2) assms(3) domIff state_monotonicGrowth_no_new_calls_in_committed_transactions state_monotonicGrowth_wf1 wellFormed_callOrigin_dom3)
  then show ?thesis
    by (metis (no_types) assms(1) assms(3) domD state_monotonicGrowth_callOrigin)
qed 
  

lemma state_monotonicGrowth_committed_transactions_fixed1:
  assumes "state_monotonicGrowth S' S"
  shows "state_monotonicGrowth_txStable (callOrigin S) (callOrigin S') (transactionStatus S')"
  using assms  by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_committed_transactions_fixed2:
  assumes "state_monotonicGrowth S' S"
and "transactionStatus S' tx \<triangleq> Commited"
shows "{c. callOrigin S' c \<triangleq> tx} = {c. callOrigin S c \<triangleq> tx}"
  using assms state_monotonicGrowth_callOrigin state_monotonicGrowth_committed_transactions_fixed by blast

lemma state_monotonicGrowth_refl[simp]: 
  assumes "state_wellFormed S"
  shows "state_monotonicGrowth S S"
  by (auto simp add: assms state_monotonicGrowth_def  state_monotonicGrowth_txStable_def)


schematic_goal show_state_monotonicGrowth: "?X \<Longrightarrow> state_monotonicGrowth S S'"
  apply (unfold state_monotonicGrowth_def)
  apply assumption
  done



lemmas state_monotonicGrowth_lemmas = 
state_monotonicGrowth_calls
state_monotonicGrowth_happensBefore
state_monotonicGrowth_callOrigin
state_monotonicGrowth_callOrigin2
state_monotonicGrowth_generatedIds
state_monotonicGrowth_knownIds
state_monotonicGrowth_invocationOp
state_monotonicGrowth_invocationRes
state_monotonicGrowth_transactionStatus
state_monotonicGrowth_prog
state_monotonicGrowth_invocationOp2
state_monotonicGrowth_committed_transactions_fixed
state_monotonicGrowth_committed_transactions_fixed1
state_monotonicGrowth_committed_transactions_fixed2
state_monotonicGrowth_wf1 
state_monotonicGrowth_wf2
state_monotonicGrowth_no_new_calls_before_existing
state_monotonicGrowth_no_new_calls_in_committed_transactions
state_monotonicGrowth_transactionOrigin


(* TODO remove definition *)
text {* Invariant holds for state *}
abbreviation invariant_all :: "('localState, 'any) state \<Rightarrow> bool" where
"invariant_all state \<equiv>  invariant (prog state) (invContext state)"


 
lemma show_invariant_all_changes:
assumes "invContext S'  = invContext S "
    and "prog S' = prog S"
shows "invariant_all S' = invariant_all S"
using assms by (auto simp add: )
      

text {*
The single invocation semantics only work on a single session.
All other sessions are simulated by nondeterministic state changes, with respect to the invariant.
*}


  
inductive step_s :: "('localState, 'any::valueType) state \<Rightarrow> (invocation \<times> 'any action \<times> bool) \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S" 60) where
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
   state_monotonicGrowth C C';   
   \<And>t. transactionOrigin C t \<triangleq> s \<longleftrightarrow> transactionOrigin C' t \<triangleq> s;
   (* new transaction has no calls yet *)
   (* invariant maintained *)
   invariant_all C';
   \<And>tx. transactionStatus C' tx \<noteq> Some Uncommited;
   (* well formed history *)
   state_wellFormed C';
   state_wellFormed C'';
   (* local changes: *)
   localState C' s \<triangleq> ls;
   currentProc C' s \<triangleq> f;
   currentTransaction C' s = None;
   visibleCalls C s \<triangleq> vis;
   visibleCalls C' s \<triangleq> vis;
   vis' = vis \<union> callsInTransaction C' newTxns \<down> happensBefore C';
   newTxns \<subseteq> dom (transactionStatus C');
   consistentSnapshot C' vis';
   transactionStatus C' t = None;
   \<And>c. callOrigin C' c \<noteq> Some t;
   transactionOrigin C' t = None;
   (C'' = C'\<lparr>transactionStatus := (transactionStatus C')(t \<mapsto> Uncommited),
              transactionOrigin := (transactionOrigin C')(t \<mapsto> s),
              currentTransaction := (currentTransaction C')(s \<mapsto> t),
              localState := (localState C')(s \<mapsto> ls'),
              visibleCalls := (visibleCalls C')(s \<mapsto> vis')
    \<rparr>)
   \<rbrakk> \<Longrightarrow> C ~~ (s, ABeginAtomic t txns, True) \<leadsto>\<^sub>S C''"
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
  "\<lbrakk>(*localState C s = None;*)
   invocationOp C s = None;
   procedure (prog C) procName args \<triangleq> (initState, impl);
   uniqueIdsInList args \<subseteq> knownIds C';
   (*  TODO add welformedness? *)
   state_wellFormed C';
   \<And>tx. transactionStatus C' tx \<noteq> Some Uncommited;
   invariant_all C';
   invocationOp C' s = None;
   prog C' = prog C;
   (* TODO some connection between C and C' or allow anything that preserves invariant? maybe C is not needed at all? *)
   C'' = (C'\<lparr>localState := (localState C')(s \<mapsto> initState),
                 currentProc := (currentProc C')(s \<mapsto> impl),
                 visibleCalls := (visibleCalls C')(s \<mapsto> {}),
                 invocationOp := (invocationOp C')(s \<mapsto> (procName, args)) \<rparr>);
   valid = invariant_all C'';  (* TODO check invariant in C ? *)            
   \<And>tx. transactionOrigin C'' tx \<noteq> Some s
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvoc procName args, valid) \<leadsto>\<^sub>S C''"       
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

inductive steps_s :: "('localState, 'any::valueType) state \<Rightarrow> invocation \<times> ('any action \<times> bool) list \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S*" 60) where         
  steps_s_refl:
  "S ~~ (s, []) \<leadsto>\<^sub>S* S"
| steps_s_step:
  "\<lbrakk>S ~~ (s, tr) \<leadsto>\<^sub>S* S'; S' ~~ (s,a) \<leadsto>\<^sub>S S''\<rbrakk> \<Longrightarrow> S ~~ (s, tr@[a]) \<leadsto>\<^sub>S* S''"
  

definition traceCorrect_s where
"traceCorrect_s program trace \<equiv> (\<forall>a. (a, False) \<notin> set trace)"

definition programCorrect_s where
"programCorrect_s program \<equiv> (\<forall>trace s S. 
   (initialState program ~~ (s, trace) \<leadsto>\<^sub>S* S)
    \<longrightarrow> traceCorrect_s program trace)"
  
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

lemma steps_s_append_simp:
"(S ~~ (s, tra@trb) \<leadsto>\<^sub>S* S'') \<longleftrightarrow> (\<exists>S'. (S ~~ (s, tra) \<leadsto>\<^sub>S* S') \<and> (S' ~~ (s, trb) \<leadsto>\<^sub>S* S''))"
proof
  show "\<exists>S'. (S ~~ (s, tra) \<leadsto>\<^sub>S* S') \<and> (S' ~~ (s, trb) \<leadsto>\<^sub>S* S'') \<Longrightarrow> S ~~ (s, tra @ trb) \<leadsto>\<^sub>S* S''"
    using steps_s_append by blast
  
  show "S ~~ (s, tra @ trb) \<leadsto>\<^sub>S* S'' \<Longrightarrow> \<exists>S'. (S ~~ (s, tra) \<leadsto>\<^sub>S* S') \<and> (S' ~~ (s, trb) \<leadsto>\<^sub>S* S'')"
  proof (induct trb arbitrary: S'' rule: rev_induct)
    case Nil
    then show ?case by (auto simp add: steps_s_refl)
  next
    case (snoc a trb')
    
    from `S ~~ (s, tra @ trb' @ [a]) \<leadsto>\<^sub>S* S''`
    obtain S1 where "S ~~ (s, tra @ trb') \<leadsto>\<^sub>S* S1" and "S1 ~~ (s, a) \<leadsto>\<^sub>S S''"
      using Pair_inject steps_s.cases by force
    
    moreover from `S ~~ (s, tra @ trb') \<leadsto>\<^sub>S* S1` 
    obtain S2 where "S ~~ (s, tra) \<leadsto>\<^sub>S* S2" and "S2 ~~ (s, trb') \<leadsto>\<^sub>S* S1"
      using snoc.hyps by blast
    
    ultimately show ?case
      using steps_s_step by blast 
  qed
qed    

lemma steps_s_empty:
"(S ~~ (s, []) \<leadsto>\<^sub>S* S') \<longleftrightarrow> (S' = S)"
apply (auto simp add: step_s.simps steps_s_refl)
  using steps_s.cases by fastforce

    
lemma steps_s_single: 
"(S ~~ (s, [a]) \<leadsto>\<^sub>S* S') \<longleftrightarrow> (S ~~ (s, a) \<leadsto>\<^sub>S S')"
apply (subst steps_s.simps)
by (auto simp add:  steps_s_empty)


lemma steps_s_cons_simp:
"(S ~~ (s, a#tr) \<leadsto>\<^sub>S* S'') \<longleftrightarrow> (\<exists>S'. (S ~~ (s, a) \<leadsto>\<^sub>S S') \<and> (S' ~~ (s, tr) \<leadsto>\<^sub>S* S''))"
proof -
  have "(S ~~ (s, a#tr) \<leadsto>\<^sub>S* S'') \<longleftrightarrow> (S ~~ (s, [a]@tr) \<leadsto>\<^sub>S* S'')" 
    by simp
  moreover have "... \<longleftrightarrow>  (\<exists>S'. (S ~~ (s, [a]) \<leadsto>\<^sub>S* S') \<and> (S' ~~ (s, tr) \<leadsto>\<^sub>S* S''))"
    using steps_s_append_simp by blast 
  moreover have "... \<longleftrightarrow>  (\<exists>S'. (S ~~ (s, a) \<leadsto>\<^sub>S S') \<and> (S' ~~ (s, tr) \<leadsto>\<^sub>S* S''))"
    using steps_s_single by blast
  ultimately show ?thesis by blast 
qed  


lemma step_s_induct[consumes 1, case_names initial step[IH step]]:
assumes steps: "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S"
    and initial: "P [] S_init"
    and step: "\<And>tr S a S'. \<lbrakk>P tr S; S_init ~~ (i,tr) \<leadsto>\<^sub>S* S;  S ~~ (i, a) \<leadsto>\<^sub>S S'\<rbrakk> \<Longrightarrow> P (tr@[a]) S'"
shows "P tr S"
proof -
  (*have "(S_init ~~ (i, tr) \<leadsto>\<^sub>S* S) \<and> P S_init \<longrightarrow> P S"*)
  
  
  from steps initial have "P tr S \<and> S_init ~~ (i, tr) \<leadsto>\<^sub>S* S"
  proof (induct tr arbitrary:  S rule: rev_induct)
    case Nil
    hence "S = S_init"
      using steps_s.cases by fastforce
    with `P [] S_init` `S_init ~~ (i, []) \<leadsto>\<^sub>S* S`
    show ?case by auto
    
  next
    case (snoc a tr)
    from `S_init ~~ (i, tr@[a]) \<leadsto>\<^sub>S* S`
    obtain S1 
      where S1a: "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1"
        and S1b: "S1 ~~ (i, a) \<leadsto>\<^sub>S S"
      using steps_s_cons_simp
      by (meson steps_s_append_simp steps_s_single)   
      
    thm snoc.hyps
    from `S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1` and `P [] S_init`
    have "P tr S1 \<and> S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1" 
      by (rule snoc.hyps)
    
    with S1b have "P (tr@[a]) S"
      using local.step by blast
      
    with `S_init ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S`
    show ?case by auto
      
  qed
  
  thus "P tr S" by simp
qed  

lemma step_s_no_Fail: 
  assumes "S ~~ (i, a) \<leadsto>\<^sub>S S'"
  shows "a \<noteq> (AFail, t)"
  using assms  by (auto simp add: step_s.simps)

lemma steps_s_no_Fail: 
  assumes "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
  shows "(AFail, t) \<notin> set tr"
  using assms apply (induct rule: step_s_induct)
  using step_s_no_Fail by (auto, blast)

end
