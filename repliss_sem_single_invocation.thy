section \<open>Single Invocation Semantics\<close>
theory repliss_sem_single_invocation
  imports repliss_sem execution_invariants consistency
begin



text \<open>This theory describes the single-invocation semantics used for our proof approach.\<close>

definition 
"state_monotonicGrowth_txStable callOrigin_S callOrigin_S' transactionStatus_S' \<equiv> (\<forall>c tx. callOrigin_S c \<triangleq> tx \<and> transactionStatus_S' tx \<triangleq> Committed \<longrightarrow> callOrigin_S' c \<triangleq> tx)"

definition state_monotonicGrowth :: "invocId \<Rightarrow> ('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" where
"state_monotonicGrowth i S S' \<equiv> state_wellFormed S \<and> (\<exists>tr. (S ~~ tr \<leadsto>* S') \<and> (\<forall>(i',a)\<in>set tr. i' \<noteq> i) \<and> (\<forall>i. (i, ACrash) \<notin> set tr))"




text \<open>Invariant holds for state\<close>
abbreviation invariant_all :: "('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" where
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



lemma chooseSnapshot_same_if_everything_committed:
  assumes "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
  shows "chooseSnapshot' snapshot vis S \<longleftrightarrow> chooseSnapshot snapshot vis S"
  unfolding chooseSnapshot'_def chooseSnapshot_def proof (intro iff_exI, auto)
  show "\<And>newTxns x.
       \<lbrakk>newTxns \<subseteq> dom (transactionStatus S);
        snapshot = vis \<union> callsInTransaction S newTxns \<down> happensBefore S; x \<in> newTxns\<rbrakk>
       \<Longrightarrow> transactionStatus S x \<triangleq> Committed"
    using assms not_uncommitted_cases by auto
qed
  
inductive step_s :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> (invocId \<times> ('proc, 'operation, 'any) action \<times> bool) \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S" 60) where
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
   uniqueIds uidv = {uid}; \<comment> \<open> there is exactly one unique id \<close>
   ls' uidv \<triangleq> ls'';
   uid = to_nat uidv
   \<rbrakk> \<Longrightarrow> S ~~ (i, ANewId uidv, True) \<leadsto>\<^sub>S (S\<lparr>localState := (localState S)(i \<mapsto> ls''), 
                                   generatedIds := (generatedIds S)( uid \<mapsto> i) \<rparr>)"   
| beginAtomic: 
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = BeginAtomic ls';
   currentTransaction S i = None;
   transactionStatus S t = None;
   \<comment> \<open> we assume a nondeterministic state change to C' here \<close>
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
   f ls = DbOperation Op ls';
   currentTransaction S i \<triangleq> t;
   calls S c = None;
   querySpec (prog S) Op (getContext S i)  res;
   visibleCalls S i \<triangleq> vis
   \<rbrakk> \<Longrightarrow>  S ~~ (i, ADbOp c Op res, True) \<leadsto>\<^sub>S (S\<lparr>localState := (localState S)(i \<mapsto> ls' res), 
                calls := (calls S)(c \<mapsto> Call Op res ),
                callOrigin := (callOrigin S)(c \<mapsto> t),
                visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>)"              
| invocation:
  "\<lbrakk>\<comment> \<open> localState C s = None; \<close>
   invocationOp S i = None;
   procedure (prog S) proc = (initState, impl);
   uniqueIds proc \<subseteq> knownIds S';
   state_wellFormed S';
   \<And>tx. transactionStatus S' tx \<noteq> Some Uncommitted;
   invariant_all S';
   invocationOp S' i = None;
   prog S' = prog S;
   S'' = (S'\<lparr>localState := (localState S')(i \<mapsto> initState),
                 currentProc := (currentProc S')(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S')(i \<mapsto> {}),
                 invocationOp := (invocationOp S')(i \<mapsto> proc) \<rparr>);
   valid = invariant_all S''; 
   \<And>tx. transactionOrigin S'' tx \<noteq> Some i
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AInvoc proc, valid) \<leadsto>\<^sub>S S''"        
| return:
  "\<lbrakk>localState S i \<triangleq> ls; 
   currentProc S i \<triangleq> f; 
   f ls = Return res;
   currentTransaction S i = None; 
   S' = (S\<lparr>localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>);
   valid = invariant_all S'                   
   \<rbrakk> \<Longrightarrow>  S ~~ (i, AReturn res, valid) \<leadsto>\<^sub>S S'"


inductive steps_s :: "('proc::valueType, 'ls, 'operation, 'any::valueType) state \<Rightarrow> invocId \<times> (('proc, 'operation, 'any) action \<times> bool) list \<Rightarrow> ('proc, 'ls, 'operation, 'any) state \<Rightarrow> bool" (infixr "~~ _ \<leadsto>\<^sub>S*" 60) where         
  steps_s_refl:
  "S ~~ (s, []) \<leadsto>\<^sub>S* S"
| steps_s_step:
  "\<lbrakk>S ~~ (s, tr) \<leadsto>\<^sub>S* S'; S' ~~ (s,a) \<leadsto>\<^sub>S S''\<rbrakk> \<Longrightarrow> S ~~ (s, tr@[a]) \<leadsto>\<^sub>S* S''"
  

\<comment> \<open>Add some nicer syntax for Latex output:\<close>


syntax (latex output)
  "_step_s" :: "('c, 'd, 'a, 'b) state \<Rightarrow> invocId \<times> ('c, 'a, 'b) action \<times> bool \<Rightarrow> ('c, 'd, 'a, 'b) state \<Rightarrow> bool" 
      ("(_)\<^latex>\<open>\\ensuremath{\\xrightarrow{\<close> (_) \<^latex>\<open>}_{S}}\<close> (_)" [5,5,5]65)
  "_steps_s" :: "('c, 'd, 'a, 'b) state \<Rightarrow> invocId \<times> (('c, 'a, 'b) action \<times> bool) list \<Rightarrow> ('c, 'd, 'a, 'b) state \<Rightarrow> bool" 
      ("(_)\<^latex>\<open>\\ensuremath{\\xrightarrow{\<close> (_) \<^latex>\<open>}_{S}^*}\<close> (_)" [5,5,5]65)
translations
  "_step_s x y z" <= "CONST step_s x y z"
  "_steps_s x y z" <= "CONST steps_s x y z"


definition traceCorrect_s where
"traceCorrect_s trace \<equiv> (\<forall>a. (a, False) \<notin> set trace)"

lemma traceCorrect_s_split: 
  assumes "snd a"
and "traceCorrect_s trace"
shows "traceCorrect_s (a#trace)"
  by (metis assms set_ConsD sndI traceCorrect_s_def)


definition programCorrect_s where
"programCorrect_s program \<equiv> (\<forall>trace s S. 
   (initialState program ~~ (s, trace) \<leadsto>\<^sub>S* S)
    \<longrightarrow> traceCorrect_s trace)"
  
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
  shows "a \<noteq> (ACrash, t)"
  using assms  by (auto simp add: step_s.simps)

lemma steps_s_no_Fail: 
  assumes "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
  shows "(ACrash, t) \<notin> set tr"
  using assms apply (induct rule: step_s_induct)
  using step_s_no_Fail by (auto, blast)

end
