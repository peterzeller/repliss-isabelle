theory approach
imports Main sem1_commutativity
  replissSem_singleSession
begin


(*
TODO:

1. single session semantics

2. show that multi-session trace with fixed session can be reduced to multiple single session traces by chopping

3. other things

*)


declare length_dropWhile_le[simp]  
  
(*
split a trace into maximal chunks of actions in the same session.
Each chunk can be used in single-session semantics.

Remember that a trace is just a (session\<times>action) list
*)
fun split_trace :: "trace \<Rightarrow> (session \<times> (action list)) list" where
  "split_trace [] = []"
| "split_trace ((s,a)#rest) = (
   let same = map snd (takeWhile (\<lambda>x. fst x = s) rest);
       rest' = dropWhile (\<lambda>x. fst x = s) rest
   in (s, a#same) # split_trace rest'
)"


text {* Function describing that a list is a prefix of another list.  *}
definition 
"isPrefix xs ys \<equiv> xs = take (length xs) ys"

lemma isPrefix_append:
"isPrefix xs ys \<Longrightarrow> isPrefix xs (ys@zs)"
using take_all by (fastforce simp add: isPrefix_def)

lemma isPrefix_appendI[simp]:
"isPrefix xs (xs@ys)"
  by (simp add: isPrefix_def)

lemma state_wellFormed_tx_to_visibleCalls:     
assumes "state_wellFormed S"
and "currentTransaction S s \<triangleq> tx"
shows "visibleCalls S s \<noteq> None"

sorry
  
  
find_theorems "initialState" steps  
  
text {*
If we have an execution on a a single session starting with state satisfying the invariant, then we can convert 
this trace to a single-session trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
*}
lemma 
fixes tr :: trace
  and s :: session      
  and S S' :: state
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and singleSession: "\<And>a. a\<in>set tr \<Longrightarrow> fst a = s"
    (* invariant holds on all states in the execution *)
    and inv: "\<And>s' S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant (prog S) (invContext S' s')"
shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (if currentTransaction S' s = None then S2 = S' else \<exists>vis'. vis' \<subseteq> visibleCalls S' s orElse {} \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s \<mapsto> vis') \<rparr> )"
        (* TODO special case for fail, pull (and others?) *)
using steps S_wellformed singleSession inv proof (induct rule: steps.induct)
  case (steps_refl S)
  
    
  
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="S"], intro conjI)
    show "S ~~ (s, []) \<leadsto>\<^sub>S* S"
      by (simp add: steps_s_refl) 
    show "\<forall>a. (a, False) \<notin> set []"
      by simp
    show "if currentTransaction S s = None then S = S else \<exists>vis'\<subseteq>visibleCalls S s orElse {}. S = S\<lparr>visibleCalls := visibleCalls S(s \<mapsto> vis')\<rparr>"
    proof (subst if_splits, safe)
      fix tx
      assume a: "currentTransaction S s \<triangleq> tx"
      hence "visibleCalls S s \<noteq> None"
        using `state_wellFormed S`
        by (simp add: state_wellFormed_tx_to_visibleCalls)
      
      hence "S = S\<lparr>visibleCalls := visibleCalls S(s \<mapsto> visibleCalls S s orElse {})\<rparr>"
      proof auto
        fix vis 
        assume "visibleCalls S s \<triangleq> vis"
        hence "visibleCalls S(s \<mapsto> vis) = visibleCalls S"
          by auto
        thus "S = S\<lparr>visibleCalls := visibleCalls S(s \<mapsto> vis)\<rparr>"
          by auto
      qed
      thus "\<exists>vis'\<subseteq>visibleCalls S s orElse {}. S = S\<lparr>visibleCalls := visibleCalls S(s \<mapsto> vis')\<rparr>"
        by blast
    qed
  qed
next
  case (steps_step S tr S' a S'')
  hence  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; \<And>a. a \<in> set tr \<Longrightarrow> fst a = s; 
               \<And>tr' S' s'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant (prog S) (invContext S' s')\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> (if currentTransaction S' s = None then S2 = S' else \<exists>vis'\<subseteq>visibleCalls S' s orElse {}. S2 = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis')\<rparr>)"
    and  step: "S' ~~ a \<leadsto> S''"
    and  singleSession: "\<And>a'. a' \<in> set (tr @ [a]) \<Longrightarrow> fst a' = s"
    and prefix_invariant: "\<And>tr' S' s'.  \<lbrakk>isPrefix tr' (tr @ [a]); S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant (prog S) (invContext S' s')"
    by auto
 
  have "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> (if currentTransaction S' s = None then S2 = S' else \<exists>vis'\<subseteq>visibleCalls S' s orElse {}. S2 = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis')\<rparr>)"
  proof (rule IH)
    show "\<And>a. a \<in> set tr \<Longrightarrow> fst a = s"
      using singleSession by auto
    show "\<And>tr' S' s'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant (prog S) (invContext S' s')"
      using prefix_invariant isPrefix_append by blast 
    show "state_wellFormed S" using S_wf .
  qed
    
  from this obtain tr' S2
      where ih1: "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
        and ih2: "\<And>a. (a, False) \<notin> set tr'"
        and ih3: "(if currentTransaction S' s = None then S2 = S' else \<exists>vis'\<subseteq>visibleCalls S' s orElse {}. S2 = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis')\<rparr>)"
      by blast
  
  have vis_defined: "visibleCalls S' s \<noteq> None" if "currentTransaction S' s \<noteq> None"
    using S_wf state_wellFormed_combine state_wellFormed_tx_to_visibleCalls steps that by auto    
    
  obtain vis'
     where vis'_sub: "vis'\<subseteq>visibleCalls S' s orElse {}"
       and vis'_else: "currentTransaction S' s \<noteq> None \<Longrightarrow> vis' = the (visibleCalls S' s)"
       and S2_vis': "S2 = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis')\<rparr>"
  proof (atomize_elim, cases "visibleCalls S' s")
    case None
    then show " \<exists>vis'\<subseteq>visibleCalls S' s orElse {}. (currentTransaction S' s \<noteq> None \<longrightarrow> vis' = the (visibleCalls S' s)) \<and> S2 = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis')\<rparr>"
      apply (rule_tac x="{}" in exI, cases "visibleCalls S' s", auto)
      using vis_defined apply auto[1]
      (* TODO *)
      
      
      
      
  next
    case (Some a)
    then show ?thesis sorry
  qed   
      
  show ?case 
  proof (cases "snd a")
    case ALocal
    hence "a = (s, ALocal)"
      by (simp add: prod.expand singleSession) 

    with step
    have step': "S' ~~ (s, ALocal) \<leadsto> S''" by simp
    
    from step_elim_ALocal[OF step']
    obtain ls f ls' 
       where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls')\<rparr>"
         and a2: "localState S' s \<triangleq> ls"
         and a3: "currentProc S' s \<triangleq> f"
         and a4: "f ls = LocalStep ls'"
       by metis
    
    from a2 a3 a4
    have step_s: "S' ~~ (s,(ALocal,True)) \<leadsto>\<^sub>S S'\<lparr>localState := localState S'(s \<mapsto> ls')\<rparr>"
      by (rule step_s.local)
    
    from ih1
    have steps_s: "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''"
    proof (rule steps_s_step)
      from step_s
      show "S' ~~ (s, ALocal, True) \<leadsto>\<^sub>S S''"
        using a1 by blast
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''" using steps_s .
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ALocal, True)])"
        by (simp add: ih2) 
    qed
    
  next
    case (ANewId uid)
    hence [simp]: "a = (s, ANewId uid)"
      by (simp add: prod_eqI steps_step.prems) 
    
    with step
    have step': "S' ~~ (s, ANewId uid) \<leadsto> S''" by simp
    
    from step_elim_ANewId[OF step']
    obtain ls f ls' 
       where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls' uid), generatedIds := insert uid (generatedIds S')\<rparr>"
         and a2: "localState S' s \<triangleq> ls"
         and a3: "currentProc S' s \<triangleq> f"
         and a4: "f ls = NewId ls'"
         and a5: "uid \<notin> generatedIds S'"
       by metis  
    
    
    from a2 a3 a4 a5
    have step_s: "S' ~~ (s,(ANewId uid,True)) \<leadsto>\<^sub>S S'\<lparr>localState := localState S'(s \<mapsto> ls' uid), generatedIds := generatedIds S' \<union> {uid}\<rparr>"
      by (rule step_s.newId)
    
    from ih1
    have steps_s: "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''"
    proof (rule steps_s_step)
      from step_s
      show "S' ~~ (s, ANewId uid, True) \<leadsto>\<^sub>S S''"
        by (simp add: a1) 
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''" using steps_s .
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ANewId uid, True)])"
        by (simp add: ih2) 
    qed  
       
  next
    case (ABeginAtomic txId)
    hence [simp]: "a = (s, ABeginAtomic txId)"
      by (simp add: prod_eqI steps_step.prems) 
    
    with step
    have step': "S' ~~ (s, ABeginAtomic txId) \<leadsto> S''" by simp
    
    from step_elim_ABeginAtomic[OF step']
    obtain ls f ls' 
      where a1: "S'' = S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited)\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = BeginAtomic ls'"
        and a5: "currentTransaction S' s = None"
        and a6: "transactionStatus S' txId = None"
      by metis
    
    have "invariant (prog S) (invContext S' s')" for s'
    proof (rule prefix_invariant)
      show "S ~~ tr \<leadsto>* S'" using steps .
      show "isPrefix tr (tr @ [a])" by simp
    qed
    
    hence inv': "invariant (prog S') (invContext S' s')" for s'
      using step_prog_invariant steps by auto
      
      
    from a2 a3 a4 a5 a6 inv'
    have step_s: "S' ~~ (s,(ABeginAtomic txId,True)) \<leadsto>\<^sub>S S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited)\<rparr>"
    by (rule step_s.beginAtomic)  
      
    then show ?thesis
      by (metis ih1 ih2 a1 insert_iff list.simps(15) prod.inject rotate1.simps(2) set_rotate1 steps_s_step) 
  next
    case AEndAtomic
    hence [simp]: "a = (s, AEndAtomic)"
      by (simp add: prod.expand steps_step.prems(1)) 

    with step
    have step': "S' ~~ (s, AEndAtomic) \<leadsto> S''" by simp
    
    from step_elim_AEndAtomic[OF step']  
    obtain ls f ls' t 
      where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls'), 
              currentTransaction := (currentTransaction S')(s := None), 
              transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = EndAtomic ls'"
        and a5: "currentTransaction S' s \<triangleq> t"
      by metis  
      
    (*from a2 a3 a4 a5 *)
    from a2 a3 a4 a5 a1
    have step_s: "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
    proof (rule step_s.endAtomic)  
      show "True = invariant (prog S') (invContext S' s)"
        using step_prog_invariant steps steps_step.prems(2) by force
    qed  
      
    then show ?thesis
      by (smt UnE ih1 ih2 empty_set list.set(2) prod.inject set_append singletonD steps_s.intros(2)) 
  next
    case (ADbOp cId operation args res)
    hence [simp]: "a = (s, ADbOp cId operation args res)"
      by (simp add: prod.expand steps_step.prems(1)) 

    with step
    have step': "S' ~~ (s, ADbOp cId operation args res) \<leadsto> S''" by simp
    
    from step_elim_ADbOp[OF step']  
    obtain ls f ls' t vis 
      where a1: "S'' = S'\<lparr>localState := localState S'(s \<mapsto> ls' res), 
                        calls := calls S'(cId \<mapsto> Call operation args res), 
                        callOrigin := callOrigin S'(cId \<mapsto> t), 
                        visibleCalls := visibleCalls S'(s \<mapsto> insert cId vis),
                        happensBefore := happensBefore S' \<union> vis \<times> {cId}\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = DbOperation operation args ls'"
        and a5: "currentTransaction S' s \<triangleq> t"
        and a6: "calls S' cId = None"
        and a7: "querySpec (prog S') operation args (getContextH (calls S') (happensBefore S') (Some vis)) res"
        and a8: "visibleCalls S' s \<triangleq> vis"
      by metis  
      
    from a2 a3 a4 a5 a6 
    have step_s: "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S'\<lparr>localState := localState S'(s \<mapsto> ls' res), 
                        calls := calls S'(cId \<mapsto> Call operation args res), 
                        callOrigin := callOrigin S'(cId \<mapsto> t), 
                        visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> {cId}),
                        happensBefore := happensBefore S' \<union> vis \<times> {cId}\<rparr>"
    proof (rule step_s.dbop)  
      show "querySpec (prog S') operation args (getContext S' s) res"
        using a7 by (simp add: a8) 
      show "visibleCalls S' s \<triangleq> vis" using a8 .
    qed  
    hence "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S''"
      by (simp add: a1)
    then show ?thesis
      by (smt UnE ih1 ih2 empty_set list.simps(15) prod.inject set_append singletonD step' step.dbop stepDeterministic step_s.dbop steps_s_step) 
  next
    case (APull x6)
    then show ?thesis sorry
  next
    case (AInvoc x71 x72)
    then show ?thesis sorry
  next
    case (AReturn x8)
    then show ?thesis sorry
  next
    case AFail
    then show ?thesis sorry
  next
    case (AInvcheck x10)
    then show ?thesis sorry
  qed
    
    
  
  qed
qed




text {*
When a program is correct in the single session semantics, 
it is also correct when executed in the concurrent interleaving semantics.
*}
theorem
assumes works_in_single_session: "programCorrect_s program"
shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving)
  text {* Assume we have a trace and a final state S *}
  fix trace S
  text {* Such that executing the trace finishes in state S. *}
  assume steps: "initialState program ~~ trace \<leadsto>* S"
  
  text {* We can assume transactions are packed. *}
  assume packed: "transactionsArePacked trace"
  
  text {* We show that the trace must be correct (proof by contradiction). *}
  show "traceCorrect program trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect program trace"
    
    text {* If the trace is incorrect, there must be a failing invariant check in the trace: *}
    from this obtain s where "(s, AInvcheck False) \<in> set trace"
       using steps by (auto simp add: traceCorrect_def)
    
       
   (* TODO now we need to split up the transactions one by one *)    
    
    
  
  


qed



end