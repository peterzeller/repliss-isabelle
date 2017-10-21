theory replissSem_singleSession
imports replissSem1 execution_invariants
begin

section {* Single invocation semantics *}

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

definition consistentSnapshot where
"consistentSnapshot state vis \<equiv>
  vis \<subseteq> dom (calls state)
 (* causally consistent *) 
 \<and> (causallyConsistent (happensBefore state) vis)
 (*transaction consistent *)
 \<and> (transactionConsistent (callOrigin state) (transactionStatus state) vis)
"


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
definition state_monotonicGrowth :: "('localState, 'any) state \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" where
"state_monotonicGrowth S' S \<equiv> 
        
      (*monotonic growth of calls*)
        (\<forall>c i. calls S' c \<triangleq> i \<longrightarrow> calls S c \<triangleq> i)
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
      \<and> prog S = prog S'"


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
  using assms by (auto simp add: state_monotonicGrowth_def)

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


lemma state_monotonicGrowth_prog:
  assumes "state_monotonicGrowth  S' S"
  shows "prog S = prog S'"
  using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_invocationOp2:
  assumes "state_monotonicGrowth  S' S"
  shows "(invocationOp S' \<subseteq>\<^sub>m invocationOp S) "
  using assms by (auto simp add: state_monotonicGrowth_def map_le_def)



text {* Invariant holds for all possible (causally + transaction consistent) states *}
definition invariant_all :: "('localState, 'any) state \<Rightarrow> bool" where
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
The single invocation semantics only work on a single session.
All other sessions are simulated by nondeterministic state changes, with respect to the invariant.
*}


  
inductive step_s :: "('localState, 'any) state \<Rightarrow> (invocation \<times> 'any action \<times> bool) \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S" 60) where
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
   (* invariant maintained *)
   invariant_all C';
   \<And>tx. tx\<noteq>t \<Longrightarrow> transactionStatus C' tx \<noteq> Some Uncommited;
   (* well formed history *)
   state_wellFormed C';
   state_monotonicGrowth C C';   
   (* local changes: *)
   localState C' s \<triangleq> ls';
   currentProc C' s \<triangleq> f;
   currentTransaction C' s \<triangleq> t;
   transactionStatus C' t \<triangleq> Uncommited;
   \<And>c. callOrigin C' c \<noteq> Some t;
   transactionOrigin C' t \<triangleq> s
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
  "\<lbrakk>(*localState C s = None;*)
   invocationOp C s = None;
   procedure (prog C) procName args \<triangleq> (initState, impl);
   uniqueIdsInList args \<subseteq> knownIds C';
   (*  TODO add welformedness? *)
   state_wellFormed C';
   \<And>tx. tx\<noteq>t \<Longrightarrow> transactionStatus C' tx \<noteq> Some Uncommited;
   invariant_all C';
   invocationOp C' s = None;
   prog C' = prog C;
   (* TODO some connection between C and C' or allow anything that preserves invariant? maybe C is not needed at all? *)
   C'' = (C'\<lparr>localState := (localState C')(s \<mapsto> initState),
                 currentProc := (currentProc C')(s \<mapsto> impl),
                 visibleCalls := (visibleCalls C')(s \<mapsto> {}),
                 invocationOp := (invocationOp C')(s \<mapsto> (procName, args)) \<rparr>);
   valid = invariant_all C''  (* TODO check invariant in C ? *)            
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
  
inductive steps_s :: "('localState, 'any) state \<Rightarrow> invocation \<times> ('any action \<times> bool) list \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S*" 60) where         
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


end
