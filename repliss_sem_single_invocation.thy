theory repliss_sem_single_invocation
  imports repliss_sem execution_invariants consistency
begin


section \<open>Single invocId semantics\<close>

text \<open>This theory describes the single-invocId semantics used for our proof approach.\<close>

definition 
"state_monotonicGrowth_txStable callOrigin_S callOrigin_S' transactionStatus_S' \<equiv> (\<forall>c tx. callOrigin_S c \<triangleq> tx \<and> transactionStatus_S' tx \<triangleq> Committed \<longrightarrow> callOrigin_S' c \<triangleq> tx)"

definition state_monotonicGrowth :: "invocId \<Rightarrow> ('localState, 'any::valueType) state \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" where
"state_monotonicGrowth i S S' \<equiv> state_wellFormed S \<and> (\<exists>tr. (S ~~ tr \<leadsto>* S') \<and> (\<forall>(i',a)\<in>set tr. i' \<noteq> i) \<and> (\<forall>i. (i, AFail) \<notin> set tr))"

\<comment> \<open>TODO add definitions\<close>
   \<comment> \<open>monotonic growth of visible calls\<close>
   \<comment> \<open>monotonic growth of callops\<close>
   \<comment> \<open>monotonic growth of happens-before\<close>
   \<comment> \<open>--> no new calls can be added before\<close>
   \<comment> \<open>monotonic growth of sameTransaction\<close>
   \<comment> \<open>monotonic growth of origin\<close>
   \<comment> \<open>monotonic growth of invocations\<close>
   \<comment> \<open>monotonic growth of invocId result\<close>
   \<comment> \<open>monotonic growth of invocId happens-before\<close>
   \<comment> \<open>--> no new calls can be added before\<close>
(*
definition state_monotonicGrowth :: "('localState, 'any::valueType) state \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" where
"state_monotonicGrowth S' S \<equiv> 
      \<comment> \<open> monotonic growth of i calls \<close>
      \<and>  (\<forall>c i. calls S' c \<triangleq> i \<longrightarrow> calls S c \<triangleq> i)
      (*monotonic growth of happensBefore 
         --> no new calls can be added before existing calls *)
      \<and> (\<forall>c1 c2. c2\<in>dom (calls S') \<longrightarrow> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'))
      \<comment> \<open>  monotonic growth of callOrigin  \<close>
      \<and> (\<forall>c t. callOrigin S' c \<triangleq> t \<longrightarrow> callOrigin S c \<triangleq> t)
      \<comment> \<open>  monotonic growth of generatedIds  \<close>
      \<and> (\<forall>uid i. generatedIds S' uid \<triangleq> i \<longrightarrow> generatedIds S uid \<triangleq> i)
      \<comment> \<open>  growth of known ids  \<close>
      \<and> knownIds S' \<subseteq> knownIds S
      \<comment> \<open>  monotonic growth of invocationOp  \<close>
      \<and> (\<forall>s i. invocationOp S' s \<triangleq> i \<longrightarrow> invocationOp S s \<triangleq> i)
      \<comment> \<open>  monotonic growth of invocationRes  \<close>
      \<and> (\<forall>s i. invocationRes S' s \<triangleq> i \<longrightarrow> invocationRes S s \<triangleq> i)
      \<comment> \<open>  transactionStatus ??? may change, irrelevant  \<close>
      \<and> (\<forall>tx. transactionStatus S' tx \<le> transactionStatus S tx )
      \<comment> \<open>  no new calls are added to committed transactions  \<close>
      \<and> state_monotonicGrowth_txStable (callOrigin S) (callOrigin S') (transactionStatus S')
      \<comment> \<open>  monotonic growth of transaction origin   \<close>
      \<and> (\<forall>t i . transactionOrigin S' t \<triangleq> i \<longrightarrow> transactionOrigin S t \<triangleq> i)
      \<comment> \<open>  no new calls are added before existing calls  \<close>
      \<and> (\<forall>c c' x y. calls S' c = None \<and> calls S c \<triangleq> x \<and> calls S' c' \<triangleq> y  \<longrightarrow> (c,c') \<notin> happensBefore S')
      \<comment> \<open>  no new calls are added to committed transactions  \<close>
      \<and> (\<forall>c tx. callOrigin S c \<triangleq> tx \<and> calls S' c = None  \<longrightarrow> transactionStatus S' tx \<noteq> Some Committed)
      \<comment> \<open>  Program unchanged  \<close>
      \<and> prog S = prog S'"
*)

lemma state_monotonicGrowth_refl: "state_wellFormed S \<Longrightarrow> state_monotonicGrowth i S S"
  by (auto simp add: state_monotonicGrowth_def exI[where x="[]"] steps_empty)


lemma state_monotonicGrowth_step: 
  assumes "state_wellFormed S"
    and "state_monotonicGrowth i S S'"
    and "S' ~~ (i',a) \<leadsto> S''"
    and "i' \<noteq> i"
    and "a \<noteq> AFail"
  shows "state_monotonicGrowth i S S''"
  using assms apply (auto simp add: state_monotonicGrowth_def )
  apply (rule_tac x="tr@[(i',a)]" in exI)
  by (auto simp add: steps_step)


lemma state_monotonicGrowth_wf1: 
  assumes "state_monotonicGrowth i S' S"
  shows "state_wellFormed S'"
    using assms by (auto simp add: state_monotonicGrowth_def)

lemma state_monotonicGrowth_wf2: 
  assumes "state_monotonicGrowth i  S' S"
  shows "state_wellFormed S"
  using assms state_wellFormed_combine by (auto simp add: state_monotonicGrowth_def)


lemma state_monotonicGrowth_no_new_calls_before_existing1:
  assumes "state_monotonicGrowth i S' S"
    and "c2\<in>dom (calls S')"
  shows "(c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S'"
  using assms no_new_calls_before_existing_h state_monotonicGrowth_def by blast

lemma state_monotonicGrowth_no_new_calls_before_existing: 
  assumes "state_monotonicGrowth i S' S"
    and "calls S' c = None"
    and "calls S c \<triangleq> x"
    and "calls S' c' \<triangleq> y"
  shows "(c,c') \<notin> happensBefore S'"
  using assms
  by (meson domIff mem_Sigma_iff rev_subsetD state_monotonicGrowth_wf1 wellFormed_visibleCallsSubsetCalls_h(1)) 

lemma state_monotonicGrowth_no_new_calls_in_committed_transactions: 
  assumes "state_monotonicGrowth i S' S"
    and "callOrigin S c \<triangleq> tx"
    and "calls S' c = None"
  shows "transactionStatus S' tx \<noteq> Some Committed"
  using assms by (auto simp add: state_monotonicGrowth_def no_new_calls_in_committed_transactions)

lemma state_monotonicGrowth_transactionOrigin: 
  assumes "state_monotonicGrowth i S' S" 
    and "transactionOrigin S' t \<triangleq> i"
  shows "transactionOrigin S t \<triangleq> i"
  using assms by (auto simp add: state_monotonicGrowth_def transactionOrigin_mono)


lemma state_monotonicGrowth_calls:
  assumes "state_monotonicGrowth i S' S"
  shows "calls S' c \<triangleq> info \<Longrightarrow> calls S c \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def calls_mono)

lemma state_monotonicGrowth_happensBefore:
  assumes "state_monotonicGrowth i S' S"
  shows "c2\<in>dom (calls S') \<Longrightarrow> ((c1,c2)\<in>happensBefore S \<longleftrightarrow> (c1,c2)\<in>happensBefore S')"
  using assms by (auto simp add: state_monotonicGrowth_def domIff no_new_calls_before_existing)

lemma state_monotonicGrowth_callOrigin:
  assumes "state_monotonicGrowth i S' S"
  shows "callOrigin S' c \<triangleq> t \<Longrightarrow> callOrigin S c \<triangleq> t"
  using assms by (auto simp add: state_monotonicGrowth_def callOrigin_mono)

lemma state_monotonicGrowth_callOrigin2:
  assumes "state_monotonicGrowth i S' S"
  shows "callOrigin S c = None \<Longrightarrow> callOrigin S' c = None"
  using assms domIff state_monotonicGrowth_callOrigin by fastforce 

lemma state_monotonicGrowth_generatedIds:
  assumes "state_monotonicGrowth i S' S"
  shows "generatedIds S' uid \<triangleq> i \<Longrightarrow> generatedIds S uid \<triangleq> i"
  using assms by (auto simp add: state_monotonicGrowth_def generatedIds_mono)


lemma state_monotonicGrowth_knownIds:
  assumes "state_monotonicGrowth i S' S"
  shows "knownIds S' \<subseteq> knownIds S"
  using assms by (auto simp add: state_monotonicGrowth_def knownIds_mono2)


lemma state_monotonicGrowth_invocationOp:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationOp S' s \<triangleq> info \<Longrightarrow> invocationOp S s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_invocationOp)

lemma state_monotonicGrowth_invocationOp_i:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationOp S i = invocationOp S' i"
  using assms proof (auto simp add: state_monotonicGrowth_def)
  fix tr
  assume a0: "state_wellFormed S'"
    and steps: "S' ~~ tr \<leadsto>* S"
    and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
    and a3: "\<forall>i. (i, AFail) \<notin> set tr"

  from steps no_i
  show "invocationOp S i = invocationOp S' i"
    by (induct rule: steps.induct, auto simp add: step.simps)
qed

lemma state_monotonicGrowth_invocationRes:
  assumes "state_monotonicGrowth i S' S"
  shows "invocationRes S' s \<triangleq> info \<Longrightarrow> invocationRes S s \<triangleq> info"
  using assms by (auto simp add: state_monotonicGrowth_def invocationRes_mono)

lemma state_monotonicGrowth_transactionStatus:
  assumes "state_monotonicGrowth i S' S"
  shows "transactionStatus S' tx \<le> transactionStatus S tx"
  using assms by (auto simp add: state_monotonicGrowth_def transactionStatus_mono)

lemma state_monotonicGrowth_transactionStatus2:
  assumes "state_monotonicGrowth i S' S"
  shows "transactionStatus S' tx \<triangleq> Committed \<Longrightarrow>  transactionStatus S tx \<triangleq> Committed"
  using assms by (auto simp add: state_monotonicGrowth_def transactionStatus_mono1)


lemma state_monotonicGrowth_prog:
  assumes "state_monotonicGrowth i S' S"
  shows "prog S = prog S'"
  using assms by (auto simp add: state_monotonicGrowth_def steps_do_not_change_prog)

lemma state_monotonicGrowth_invocationOp2:
  assumes "state_monotonicGrowth i S' S"
  shows "(invocationOp S' \<subseteq>\<^sub>m invocationOp S) "
  using assms by (auto simp add: map_le_def state_monotonicGrowth_def invocationOp_mono)

lemma state_monotonicGrowth_committed_transactions_fixed:
  assumes "state_monotonicGrowth i S' S"
and "transactionStatus S' tx \<triangleq> Committed"
and "callOrigin S x \<triangleq> tx"
shows "callOrigin S' x \<triangleq> tx"
proof -
  have "x \<in> dom (callOrigin S')"
    by (meson assms(1) assms(2) assms(3) domIff state_monotonicGrowth_no_new_calls_in_committed_transactions state_monotonicGrowth_wf1 wellFormed_callOrigin_dom3)
  then show ?thesis
    by (metis (no_types) assms(1) assms(3) domD state_monotonicGrowth_callOrigin)
qed 
  

lemma state_monotonicGrowth_committed_transactions_fixed1:
  assumes "state_monotonicGrowth i S' S"
  shows "state_monotonicGrowth_txStable (callOrigin S) (callOrigin S') (transactionStatus S')"
  using assms  apply (auto simp add: state_monotonicGrowth_def state_monotonicGrowth_txStable_def)
  using assms state_monotonicGrowth_committed_transactions_fixed by blast


lemma state_monotonicGrowth_committed_transactions_fixed2:
  assumes "state_monotonicGrowth i S' S"
and "transactionStatus S' tx \<triangleq> Committed"
shows "{c. callOrigin S' c \<triangleq> tx} = {c. callOrigin S c \<triangleq> tx}"
  using assms state_monotonicGrowth_callOrigin state_monotonicGrowth_committed_transactions_fixed by blast


schematic_goal show_state_monotonicGrowth: "?X \<Longrightarrow> state_monotonicGrowth i S S'"
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


\<comment> \<open>TODO remove definition\<close>
text \<open>Invariant holds for state\<close>
abbreviation invariant_all :: "('localState, 'any) state \<Rightarrow> bool" where
"invariant_all state \<equiv>  invariant (prog state) (invContext state)"


 
lemma show_invariant_all_changes:
assumes "invContext S'  = invContext S "
    and "prog S' = prog S"
shows "invariant_all S' = invariant_all S"
using assms by (auto simp add: )
      

text \<open>
The single invocId semantics only work on a single session.
All other sessions are simulated by nondeterministic state changes, with respect to the invariant.
\<close>


definition chooseSnapshot' where 
"chooseSnapshot' snapshot vis S \<equiv>
\<exists> newTxns newCalls.
     newTxns \<subseteq> dom (transactionStatus S)
   \<and> newCalls = callsInTransaction S newTxns \<down> happensBefore S
   \<and> snapshot = vis \<union> newCalls"

lemma in_dom:
  assumes "S \<subseteq> dom T" and "x \<in> S" 
  shows "\<exists>y. T x \<triangleq> y"
  using assms by blast

lemma not_uncommitted_cases:
  shows "(x \<noteq> Some Uncommitted) \<longleftrightarrow> (\<forall>y. x = Some y \<longrightarrow> x = Some Committed)"
  using transactionStatus.exhaust by auto


lemma chooseSnapshot_same_if_everything_committed:
  assumes "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "chooseSnapshot' snapshot vis S \<longleftrightarrow> chooseSnapshot snapshot vis S"
  apply (auto simp add: chooseSnapshot'_def chooseSnapshot_def )
  apply (rule_tac x=newTxns in exI)
  using assms by (auto simp add: not_uncommitted_cases dest!: in_dom)

  
inductive step_s :: "('localState, 'any::valueType) state \<Rightarrow> (invocId \<times> 'any action \<times> bool) \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S" 60) where
  local: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = LocalStep ls' 
   \<rbrakk> \<Longrightarrow> S ~~ (i, ALocal, True)  \<leadsto>\<^sub>S (S\<lparr>localState := (localState S)(i \<mapsto> ls') \<rparr>)"
| newId: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = NewId ls';
   generatedIds S uid = None;
   uniqueIds uid = {uid}; \<comment> \<open> there is exactly one unique id \<close>
   ls' uid \<triangleq> ls''
   \<rbrakk> \<Longrightarrow> S ~~ (i, ANewId uid, True) \<leadsto>\<^sub>S (S\<lparr>localState := (localState S)(i \<mapsto> ls''), 
                                   generatedIds := (generatedIds S)( uid \<mapsto> i) \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTransaction S i = None;
   transactionStatus S t = None;
   \<comment> \<open> we assume a nondeterministic state change to C' here TODO add more restrictions \<close>
   prog S' = prog S;
   state_monotonicGrowth i S S';
   \<And>t. transactionOrigin S t \<triangleq> i \<longleftrightarrow> transactionOrigin S' t \<triangleq> i; \<comment> \<open>No new transactions are added to current invocId.\<close>
   \<comment> \<open> new transaction has no calls yet \<close>
   \<comment> \<open> invariant maintained \<close>
   invariant_all S';
   \<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted;
   \<comment> \<open>  well formed history  \<close>
   state_wellFormed S';
   state_wellFormed S'';
   \<comment> \<open>  local changes:  \<close>
   localState S' i \<triangleq> ls;
   currentProc S' i \<triangleq> f;
   currentTransaction S' i = None;
   visibleCalls S i \<triangleq> vis;
   visibleCalls S' i \<triangleq> vis;
   chooseSnapshot vis' vis S';
   consistentSnapshot S' vis';
   transactionStatus S' t = None;
   \<And>c. callOrigin S' c \<noteq> Some t;
   transactionOrigin S' t = None;
   (S'' = S'\<lparr>transactionStatus := (transactionStatus S')(t \<mapsto> Uncommitted),
              transactionOrigin := (transactionOrigin S')(t \<mapsto> i),
              currentTransaction := (currentTransaction S')(i \<mapsto> t),
              localState := (localState S')(i \<mapsto> ls'),
              visibleCalls := (visibleCalls S')(i \<mapsto> vis')
    \<rparr>)
   \<rbrakk> \<Longrightarrow> S ~~ (i, ABeginAtomic t txns, True) \<leadsto>\<^sub>S S''"
| endAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = EndAtomic ls';
   currentTransaction S i \<triangleq> t;
   S' = (S\<lparr>localState := (localState S)(i \<mapsto> ls'), 
                currentTransaction := (currentTransaction S)(i := None),
                transactionStatus := (transactionStatus S)(t \<mapsto> Committed) \<rparr>);
   state_wellFormed S';
   valid = invariant_all S'
   \<rbrakk> \<Longrightarrow> S ~~ (i, AEndAtomic, valid) \<leadsto>\<^sub>S S'"
| dbop: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = DbOperation Op args ls';
   currentTransaction S i \<triangleq> t;
   calls S c = None;
   querySpec (prog S) Op args (getContext S i)  res;
   visibleCalls S i \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  S ~~ (i, ADbOp c Op args res, True) \<leadsto>\<^sub>S (S\<lparr>localState := (localState S)(i \<mapsto> ls' res), 
                calls := (calls S)(c \<mapsto> Call Op args res ),
                callOrigin := (callOrigin S)(c \<mapsto> t),
                visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>)"                
(* TODO integrate pull into beginAtomic
| pull:
  "\<lbrakk>localState C s \<triangleq> ls; 
   currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   \<comment> \<open>  choose a set of committed transactions to pull in \<close>
   newTxns \<subseteq> committedTransactions C;
   \<comment> \<open>  pull in calls from the transactions and their dependencies  \<close>
   newCalls = callsInTransaction C newTxns \<down> happensBefore C
   \<rbrakk> \<Longrightarrow>  C ~~ (s, APull newTxns) \<leadsto>\<^sub>S (C\<lparr> visibleCalls := (visibleCalls C)(s \<mapsto> vis \<union> newCalls)\<rparr>)"                         
*)
| invocId:
  "\<lbrakk>\<comment> \<open> localState C s = None; \<close>
   invocationOp S i = None;
   procedure (prog S) procName args \<triangleq> (initState, impl);
   uniqueIdsInList args \<subseteq> knownIds S';
   \<comment> \<open>   TODO add welformedness?  \<close>
   state_wellFormed S';
   \<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted;
   invariant_all S';
   invocationOp S' i = None;
   prog S' = prog S;
   \<comment> \<open>  TODO some connection between C and C' or allow anything that preserves invariant? maybe C is not needed at all?  \<close>
   S'' = (S'\<lparr>localState := (localState S')(i \<mapsto> initState),
                 currentProc := (currentProc S')(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S')(i \<mapsto> {}),
                 invocationOp := (invocationOp S')(i \<mapsto> (procName, args)) \<rparr>);
   valid = invariant_all S'';  \<comment> \<open>  TODO check invariant in C ?  \<close>            
   \<And>tx. transactionOrigin S'' tx \<noteq> Some i
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvoc procName args, valid) \<leadsto>\<^sub>S S''"       
| return:
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = Return res;
   currentTransaction S i = None; \<comment> \<open>  TODO maybe we can assume invariant_all for C?  \<close>
   S' = (S\<lparr>localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>);
   valid = invariant_all S'                   
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AReturn res, valid) \<leadsto>\<^sub>S S'"

inductive steps_s :: "('localState, 'any::valueType) state \<Rightarrow> invocId \<times> ('any action \<times> bool) list \<Rightarrow> ('localState, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S*" 60) where         
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
    apply (rule steps_s.cases[OF \<open>S' ~~ (s, xs @ [x]) \<leadsto>\<^sub>S* S''\<close>]) 
    by auto
    
  
  have "S ~~ (s, (tra @ xs) @ [x]) \<leadsto>\<^sub>S* S''" 
  proof (rule steps_s_step)
    show "S_mid ~~ (s, x) \<leadsto>\<^sub>S S''" using step_x .
    show "S ~~ (s, tra @ xs) \<leadsto>\<^sub>S* S_mid"
      using steps_xs
      by (simp add: a1 snoc.hyps) 
  qed
  then show "S ~~ (s, tra @ xs @ [x]) \<leadsto>\<^sub>S* S''"
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
    
    from \<open>S ~~ (s, tra @ trb' @ [a]) \<leadsto>\<^sub>S* S''\<close>
    obtain S1 where "S ~~ (s, tra @ trb') \<leadsto>\<^sub>S* S1" and "S1 ~~ (s, a) \<leadsto>\<^sub>S S''"
      using Pair_inject steps_s.cases by force
    
    moreover from \<open>S ~~ (s, tra @ trb') \<leadsto>\<^sub>S* S1\<close> 
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
    then have "S = S_init"
      using steps_s.cases by fastforce
    with \<open>P [] S_init\<close> \<open>S_init ~~ (i, []) \<leadsto>\<^sub>S* S\<close>
    show ?case by auto
    
  next
    case (snoc a tr)
    from \<open>S_init ~~ (i, tr@[a]) \<leadsto>\<^sub>S* S\<close>
    obtain S1 
      where S1a: "S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1"
        and S1b: "S1 ~~ (i, a) \<leadsto>\<^sub>S S"
      using steps_s_cons_simp
      by (meson steps_s_append_simp steps_s_single)   
      
    thm snoc.hyps
    from \<open>S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1\<close> and \<open>P [] S_init\<close>
    have "P tr S1 \<and> S_init ~~ (i, tr) \<leadsto>\<^sub>S* S1" 
      by (rule snoc.hyps)
    
    with S1b have "P (tr@[a]) S"
      using local.step by blast
      
    with \<open>S_init ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S\<close>
    show ?case by auto
      
  qed
  
  then show "P tr S" by simp
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
