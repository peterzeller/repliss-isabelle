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

  
lemma state_wellFormed_ls_visibleCalls:     
assumes "state_wellFormed S"
shows "localState S s = None \<longleftrightarrow> visibleCalls S s = None"
using assms apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
done  

lemma state_wellFormed_ls_to_visibleCalls:     
assumes "state_wellFormed S"
and "currentTransaction S s \<triangleq> tx"
shows "localState S s \<noteq> None"
using assms apply (induct rule: wellFormed_induct)
apply (simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
done  

lemma state_wellFormed_tx_to_visibleCalls:     
assumes "state_wellFormed S"
and "currentTransaction S s \<triangleq> tx"
shows "visibleCalls S s \<noteq> None"
  using assms state_wellFormed_ls_to_visibleCalls state_wellFormed_ls_visibleCalls by auto

 

    
text {* Coupling invariant: S is state from distributed execution and S is state from single-session execution.  *}
definition state_coupling where
"state_coupling S S' s \<equiv> 
          (if currentTransaction S s = None 
           then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S s orElse {} \<and> S' = S\<lparr>visibleCalls := (visibleCalls S)(s := vis') \<rparr> 
           else S' = S)"
  
lemma state_coupling_same_inv:
assumes "state_coupling S S' s"
shows "invariant_all S' \<longleftrightarrow> invariant_all S"
proof -
  have [simp]: "prog S' = prog S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "callOrigin S' = callOrigin S" using assms by (auto simp add: state_coupling_def split: if_splits)  
  moreover have [simp]: "transactionStatus S' = transactionStatus S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "happensBefore S' = happensBefore S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "calls S' = calls S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "knownIds S' = knownIds S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationOp S' = invocationOp S" using assms by (auto simp add: state_coupling_def split: if_splits)
  moreover have [simp]: "invocationRes S' = invocationRes S" using assms by (auto simp add: state_coupling_def split: if_splits)
  
  ultimately 
  show "invariant_all S' \<longleftrightarrow> invariant_all S"
    by  (auto simp add: invariant_all_def consistentSnapshot_def)
qed    

           
text {*
If we have an execution on a a single session starting with state satisfying the invariant, then we can convert 
this trace to a single-session trace leading to an equivalent state.
Moreover the new trace contains an invariant violation, if the original trace contained one.
*}
lemma convert_to_single_session_trace:
fixes tr :: trace
  and s :: session      
  and S S' :: state
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and singleSession: "\<And>a. a\<in>set tr \<Longrightarrow> fst a = s"
    and noFails: "(s, AFail) \<notin> set tr"
    (* invariant holds on all states in the execution *)
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 s)"
        (* TODO special case for fail, pull (and others?) *)
using steps S_wellformed singleSession inv noFails proof (induct rule: steps.induct)
  case (steps_refl S)
  
    
  
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="S"], intro conjI)
    show "S ~~ (s, []) \<leadsto>\<^sub>S* S"
      by (simp add: steps_s_refl) 
    show "\<forall>a. (a, False) \<notin> set []"
      by simp
    show "state_coupling S S s"
    unfolding state_coupling_def 
    proof (subst if_splits, safe)
      fix tx
      assume a: "currentTransaction S s = None"
      show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S s orElse {} \<and> S = S\<lparr>visibleCalls := (visibleCalls S)(s := vis')\<rparr>"
        by (rule exI[where x="visibleCalls S s"], auto)
    qed
  qed
next
  case (steps_step S tr S' a S'')
  hence  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; \<And>a. a \<in> set tr \<Longrightarrow> fst a = s; 
               \<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
                   \<and> (\<forall>a. (a, False) \<notin> set tr') 
                   \<and> (state_coupling S' S2 s)"
    and  step: "S' ~~ a \<leadsto> S''"
    and  singleSession: "\<And>a'. a' \<in> set (tr @ [a]) \<Longrightarrow> fst a' = s"
    and prefix_invariant: "\<And>tr' S'.  \<lbrakk>isPrefix tr' (tr @ [a]); S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
    and noFails: "(s, AFail) \<notin> set (tr @ [a])"
    by auto

  
  have steps': "S ~~ tr @ [a] \<leadsto>* S''"
    using steps step steps.steps_step by blast 
    
  from prefix_invariant steps
  have inv': "invariant_all S'"
    using isPrefix_appendI by blast
    
    
  from prefix_invariant steps'
  have inv'': "invariant_all S''"
    by (metis append.right_neutral isPrefix_appendI)
    
    
  have "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
         \<and> (\<forall>a. (a, False) \<notin> set tr') 
         \<and> (state_coupling S' S2 s)"
  proof (rule IH)
    show "\<And>a. a \<in> set tr \<Longrightarrow> fst a = s"
      using singleSession by auto
    show "\<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using prefix_invariant isPrefix_append by blast 
    show "state_wellFormed S" using S_wf .
  qed
    
  from this obtain tr' S2
      where ih1: "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
        and ih2: "\<And>a. (a, False) \<notin> set tr'"
        and ih3: "state_coupling S' S2 s"
      by blast
  
  have ih3_noTx: "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>" if "currentTransaction S' s = None"
    using ih3 that by (auto simp add: state_coupling_def)
  have ih3_tx: "S2 = S'" if "currentTransaction S' s \<triangleq> tx" for tx
    using ih3 that by (auto simp add: state_coupling_def)
  
  have S2_calls: "calls S2 = calls S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_happensBefore: "happensBefore S2 = happensBefore S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_prog: "prog S2 = prog S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_localState: "localState S2 = localState S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_currentProc: "currentProc S2 = currentProc S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_currentTransaction: "currentTransaction S2 = currentTransaction S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_transactionStatus: "transactionStatus S2 = transactionStatus S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_callOrigin: "callOrigin S2 = callOrigin S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_generatedIds: "generatedIds S2 = generatedIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_knownIds: "knownIds S2 = knownIds S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_invocationOp: "invocationOp S2 = invocationOp S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
  have S2_invocationRes: "invocationRes S2 = invocationRes S'" using ih3 by (auto simp add: state_coupling_def split: if_splits)
 
  note S2_simps = 
      S2_calls S2_happensBefore S2_prog S2_localState S2_currentProc S2_currentTransaction
      S2_transactionStatus S2_callOrigin S2_generatedIds S2_knownIds S2_invocationOp S2_invocationRes
  
  have vis_defined: "visibleCalls S' s \<noteq> None" if "currentTransaction S' s \<noteq> None"
    using S_wf state_wellFormed_combine state_wellFormed_tx_to_visibleCalls steps that by auto    
    
  obtain vis'
     where vis'_sub: "vis' orElse {} \<subseteq>visibleCalls S' s orElse {}"
       and vis'_else: "currentTransaction S' s \<noteq> None \<Longrightarrow> vis' = visibleCalls S' s"
       and S2_vis': "S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
  proof (atomize_elim, cases "currentTransaction S' s")
    case None
    hence currentTxNone: "currentTransaction S' s = None" .
    
    from ih3_noTx[OF currentTxNone] obtain vis''  
      where vis''1: "vis'' orElse {} \<subseteq> visibleCalls S' s orElse {}" 
        and vis''2: "S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis'')\<rparr>"
      by metis
    
    show " \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> (currentTransaction S' s \<noteq> None \<longrightarrow> vis' = visibleCalls S' s) \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
      by (rule_tac x="vis''" in exI, auto simp add: currentTxNone vis''1 vis''2) 
      
  next
    case (Some tx)
    hence currentTxSome: "currentTransaction S' s \<triangleq> tx" .
    
    from ih3_tx[OF currentTxSome] have sameStates: "S2 = S'" .
    
    
    show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S' s orElse {} \<and> (currentTransaction S' s \<noteq> None \<longrightarrow> vis' = visibleCalls S' s) \<and> S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := vis')\<rparr>"
    by (rule exI[where x="visibleCalls S' s"], auto simp add: sameStates)
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
    
    have a2': "localState S2 s \<triangleq> ls" 
      using a2 ih3 by (auto simp add: state_coupling_def split: if_splits)
    have a3': "currentProc S2 s \<triangleq> f" 
      using a3 ih3 by (auto simp add: state_coupling_def split: if_splits)
    from a2' a3' a4
    have step_s: "S2 ~~ (s,(ALocal,True)) \<leadsto>\<^sub>S S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr>"
      by (rule step_s.local)
      
    have S''_S2: "S'' = S2\<lparr>localState := localState S2(s \<mapsto> ls'), visibleCalls := visibleCalls S''\<rparr>"  
      by (auto simp add: state_ext S2_vis' a1)
   
    hence S''_S2_a: "S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr> = S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"  
      by (auto simp add: state_ext)
    
    from ih1
    have steps_s: "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
    proof (rule steps_s_step)
      from step_s
      show "S2 ~~ (s, ALocal, True) \<leadsto>\<^sub>S S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
        using a1 S''_S2_a by auto
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>" using steps_s .
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ALocal, True)])"
        by (simp add: ih2) 
      show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s"
      (*show "if currentTransaction S'' s = None 
            then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>
            else S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"*)
      unfolding state_coupling_def
      proof auto
        assume no_tx_S': "currentTransaction S'' s = None"
        hence no_tx_S': "currentTransaction S' s = None"
          using a1 by auto
        from ih3_noTx[OF no_tx_S']  
        show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>"
          using a1 by auto
      next
        fix tx
        assume tx: "currentTransaction S'' s \<triangleq> tx"
        hence tx': "currentTransaction S' s \<triangleq> tx" using a1 by auto
        from ih3_tx[OF tx']
        show "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"
          using a1 by auto
      qed
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
    
    have a2':  "localState S2 s \<triangleq> ls" using a2 by (simp add: S2_localState) 
    have a3':  "currentProc S2 s \<triangleq> f" using a3 by (simp add: S2_currentProc)
    have a5':  "uid \<notin> generatedIds S2" using a5 by (simp add: S2_generatedIds)
    
    from a2' a3' a4 a5'
    have step_s: "S2 ~~ (s,(ANewId uid,True)) \<leadsto>\<^sub>S S2\<lparr>localState := localState S2(s \<mapsto> ls' uid), generatedIds := generatedIds S2 \<union> {uid}\<rparr>"
      by (rule step_s.newId)
    
    have S''_S2: "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S2\<lparr>localState := localState S2(s \<mapsto> ls' uid), generatedIds := generatedIds S2 \<union> {uid}\<rparr>" 
      by (auto simp add: a1 S2_simps)
      
      
    from ih1
    have steps_s: "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
    proof (rule steps_s_step)
      from step_s
      show "S2 ~~ (s, ANewId uid, True) \<leadsto>\<^sub>S S''\<lparr>visibleCalls := visibleCalls S2\<rparr>"
        using S''_S2 by auto
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''\<lparr>visibleCalls := visibleCalls S2\<rparr>" using steps_s .
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ANewId uid, True)])"
        by (simp add: ih2) 
      show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s"
      unfolding state_coupling_def
        proof auto
        assume no_tx_S': "currentTransaction S'' s = None"
        hence no_tx_S': "currentTransaction S' s = None"
          using a1 by auto
        from ih3_noTx[OF no_tx_S']  
        show "\<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S'' s orElse {} \<and> S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''\<lparr>visibleCalls := (visibleCalls S'')(s := vis')\<rparr>"
          using a1 by auto
      next
        fix tx
        assume tx: "currentTransaction S'' s \<triangleq> tx"
        hence tx': "currentTransaction S' s \<triangleq> tx" using a1 by auto
        from ih3_tx[OF tx']
        show "S''\<lparr>visibleCalls := visibleCalls S2\<rparr> = S''"
          using a1 by auto
      qed
        
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
    
    have a2': "localState S2 s \<triangleq> ls" using a2 S2_simps by auto
    have a3': "currentProc S2 s \<triangleq> f" using a3 S2_simps by auto 
    have a5': "currentTransaction S2 s = None" using a5 S2_simps by auto
    have a6': "transactionStatus S2 txId = None" using a6 S2_simps by auto
      
    have inv': "invariant_all S'" 
    proof (rule prefix_invariant)
      show "S ~~ tr \<leadsto>* S'" using steps .
      show "isPrefix tr (tr @ [a])" by simp
    qed
    
    
      
      
    from a2' a3' a4 a5' a6' 
    have step_s: "S2 ~~ (s,(ABeginAtomic txId,True)) \<leadsto>\<^sub>S S'\<lparr>
                localState := localState S2(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S2(s \<mapsto> txId), 
                transactionStatus := transactionStatus S2(txId \<mapsto> Uncommited)\<rparr>"
    proof (rule step_s.beginAtomic)  
      show "prog S' = prog S2"
        by (simp add: S2_prog)
      show "invariant_all S'" using inv' .
    qed
    
    moreover have "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
      using ih1 by auto
      
    
    moreover have "S'' = S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited)\<rparr>"
          by (auto simp add: a1)
    
    ultimately have steps_S''_s: "S ~~ (s, tr'@[(ABeginAtomic txId,True)]) \<leadsto>\<^sub>S* S''"
      using S2_currentTransaction S2_localState S2_transactionStatus steps_s_step by auto      
      
          
    show ?thesis
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ABeginAtomic txId,True)]) \<leadsto>\<^sub>S* S''"
        using steps_S''_s .
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic txId, True)])"
        by (simp add: ih2)     
      show "state_coupling S'' S'' s"  
      unfolding state_coupling_def
        by (simp add: a1)
    qed    
    
  next
    case AEndAtomic
    hence [simp]: "a = (s, AEndAtomic)"
      by (simp add: local.steps_step(5) prod_eqI)

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
      
    have "S2 = S'"
      using a5 ih3_tx by blast
      
    have "invariant_all S'"
      using step_prog_invariant steps
      by (metis (no_types, lifting) isPrefix_appendI steps_step.prems(3)) 
      
      
    (*from a2 a3 a4 a5 *)
    from a2 a3 a4 a5 a1
    have step_s: "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
    proof (rule step_s.endAtomic)  
      from `invariant_all S'`
      show "True = invariant_all S''"
        by (simp add: inv'')
    qed  
    
    with `S2 = S'`
    have "S' ~~ (s,(AEndAtomic,True)) \<leadsto>\<^sub>S S''"
      by simp
    
    hence steps_S''_s: "S ~~ (s, tr'@[(AEndAtomic,True)]) \<leadsto>\<^sub>S* S''"
      using \<open>S2 = S'\<close> ih1 steps_s_step by blast  
      
      
    show ?thesis
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(AEndAtomic,True)]) \<leadsto>\<^sub>S* S''" using steps_S''_s.
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(AEndAtomic, True)])"
        by (simp add: ih2)
      show "state_coupling S'' S'' s"
      unfolding state_coupling_def
        by (auto simp add: a1)
    qed
  next
    case (ADbOp cId operation args res)
    hence [simp]: "a = (s, ADbOp cId operation args res)"
      by (simp add: prod.expand steps_step.prems(2)) 

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
     
    have "S2 = S'"
      using ih3 by (auto simp add: a5 ih3 state_coupling_def)
      
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
    hence step_s': "S' ~~ (s,(ADbOp cId operation args res,True)) \<leadsto>\<^sub>S S''"
      by (simp add: a1)
      
      
    show ?thesis
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ADbOp cId operation args res,True)]) \<leadsto>\<^sub>S* S''" 
        using step_s' `S2 = S'` ih1 steps_s_step by blast 
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ADbOp cId operation args res, True)])"
        by (simp add: ih2)
      show "state_coupling S'' S'' s"
      unfolding state_coupling_def
        by (auto simp add: a1 a5 state_ext)
    qed    
  next    
    case (APull pulledTxns)
    hence "a = (s, APull pulledTxns)"
      by (simp add: prod.expand steps_step.prems(2))
    
    with step
    have step': "S' ~~ (s, APull pulledTxns) \<leadsto> S''" by simp  
    
    from step_elim_APull[OF step']  
    obtain ls vis 
      where a1: "S'' = S'\<lparr>visibleCalls := visibleCalls S'(s \<mapsto> vis \<union> callsInTransaction S' pulledTxns \<down> happensBefore S')\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentTransaction S' s = None"
        and a4: "visibleCalls S' s \<triangleq> vis"
        and a5: "pulledTxns \<subseteq> commitedTransactions S'"
      by metis
      
      
    show ?thesis
    proof (intro exI conjI)
      text {* we don't execute the pull here but wait until beginAtomic to execute it *}
      show "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
        by (simp add: ih1) 
      show "\<forall>a. (a, False) \<notin> set tr'"
        by (simp add: ih2)
      show " state_coupling S'' S2 s"
      unfolding state_coupling_def
      proof (auto simp add: a3 a1, rule exI[where x="visibleCalls S2 s"], intro conjI)
        show "S2 = S'\<lparr>visibleCalls := (visibleCalls S')(s := visibleCalls S2 s)\<rparr>"
          by (auto simp add: state_ext S2_simps S2_vis')
        show "visibleCalls S2 s orElse {} \<subseteq> vis \<union> callsInTransaction S' pulledTxns \<down> happensBefore S'"
        proof
          fix x
          assume a: "x \<in> visibleCalls S2 s orElse {}"
          hence "x \<in> vis"
            using S2_vis' a4 vis'_sub by auto 
          thus "x \<in> vis \<union> callsInTransaction S' pulledTxns \<down> happensBefore S'"
            by simp
        qed
      qed
    qed
  next
    case (AInvoc procName args)
    hence "a = (s, AInvoc procName args)"
      by (simp add: prod_eqI steps_step.prems(2))
    
    with step
    have step': "S' ~~ (s, AInvoc procName args) \<leadsto> S''" by simp  
    
    from step_elim_AInvoc[OF step'] 
    obtain initialState impl
      where a1: "S'' = S'\<lparr>
                   localState := localState S'(s \<mapsto> initialState), 
                   currentProc := currentProc S'(s \<mapsto> impl), 
                   visibleCalls := visibleCalls S'(s \<mapsto> {}), 
                   invocationOp := invocationOp S'(s \<mapsto> (procName, args))\<rparr>"
        and a2: "localState S' s = None"
        and a3: "procedure (prog S') procName args \<triangleq> (initialState, impl)"
        and a4: "uniqueIdsInList args \<subseteq> knownIds S'"
        and a5: "invocationOp S' s = None"
      by metis
    
    have inv_S': "invariant_all S'"
      using step_prog_invariant steps steps_step.prems(3) by force  
    
    have vis_None: "visibleCalls S' s = None"
      using  S_wf a2 state_wellFormed_combine steps state_wellFormed_ls_visibleCalls by blast 
    
    have "visibleCalls S2 s = None \<or> visibleCalls S2 s \<triangleq> {}"
      using S2_vis' option.sel vis'_sub vis_None by fastforce
      
      
      
    hence invContextSame: "invContext S2 s =  invContext S' s"
      by (auto simp add: S2_simps vis_None invContextH_def)
      
      
    have step_s': "S2 ~~ (s, (AInvoc procName args, True)) \<leadsto>\<^sub>S S'' "
    proof (rule step_s.invocation)
      show "localState S2 s = None"
        by (simp add: S2_localState a2) 
      show "procedure (prog S2) procName args \<triangleq> (initialState, impl)"
        by (simp add: S2_prog a3)
      show "uniqueIdsInList args \<subseteq> knownIds S2"
        by (simp add: S2_knownIds a4)
      show "invocationOp S2 s = None"
        by (simp add: S2_invocationOp a5)
      show "S'' = S2\<lparr>localState := localState S2(s \<mapsto> initialState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"
        by (auto simp add: state_ext S2_simps a1 S2_vis')
      show "True = invariant_all S''"
        by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps.steps_step)
    qed
    
    
    
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(AInvoc procName args, True)]) \<leadsto>\<^sub>S* S''"
        using step_s'
        using ih1 steps_s_step by auto 
      show " \<forall>a. (a, False) \<notin> set (tr' @ [(AInvoc procName args, True)])"
        by (simp add: ih2)
      show "state_coupling S'' S'' s "
      unfolding state_coupling_def  
        apply (auto simp add: a1 state_ext)
        by force
    qed    
  next
    case (AReturn res)
    hence "a = (s, AReturn res)"
      by (simp add: prod_eqI steps_step.prems(2))
    
    with step
    have step': "S' ~~ (s, AReturn res) \<leadsto> S''" by simp  
    
    from step_elim_AReturn[OF step']  
    obtain ls f
      where a1: "S'' = S'\<lparr>
                  localState := (localState S')(s := None), 
                  currentProc := (currentProc S')(s := None), 
                  visibleCalls := (visibleCalls S')(s := None), 
                  invocationRes := invocationRes S'(s \<mapsto> res),
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = Return res"
        and a5: "currentTransaction S' s = None"
      by metis
    
    have inv_S': "invariant_all S'"
      using isPrefix_appendI step_prog_invariant steps steps_step.prems(3) by fastforce  
      
    have inv_S'': "invariant_all S''"
      by (metis append.right_neutral isPrefix_appendI local.step prefix_invariant steps steps_appendBack)
    
      
    have step_s': "S2 ~~ (s, (AReturn res, True)) \<leadsto>\<^sub>S S'' "
    proof (rule step_s.return)
      show "localState S2 s \<triangleq> ls"
        by (simp add: S2_localState a2)
      show "currentProc S2 s \<triangleq> f"
        by (simp add: S2_currentProc a3)
      show "f ls = Return res"
        by (simp add: a4)  
      show "currentTransaction S2 s = None"
        by (simp add: S2_currentTransaction a5)
      show "True = invariant_all S''" using inv_S''
        by simp
      show "S'' = S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S2(s \<mapsto> res), knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"  
        by (auto simp add: a1 state_ext S2_simps S2_vis')
    qed    
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(AReturn res, True)]) \<leadsto>\<^sub>S* S''"    
        using step_s' ih1 steps_s_step by blast 
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(AReturn res, True)])"
        using ih2 by auto
      show "state_coupling S'' S'' s "
      unfolding state_coupling_def  
        by auto
    qed    
  next
    case AFail
    hence "a = (s, AFail)"
      by (simp add: prod_eqI steps_step.prems(2))
    with noFails have "False"
      by simp
    thus ?thesis ..
  next
    case (AInvcheck i)
    hence "a = (s, AInvcheck i)"
      by (simp add: prod_eqI steps_step.prems(2))
   
    with step
    have step': "S' ~~ (s, AInvcheck i) \<leadsto> S''" by simp  
    
    from step_elim_AInvcheck[OF step']
    obtain vis
      where a1: "S'' = S'" 
        and a2: "currentTransaction S' s = None"
        and a3: "visibleCalls S' s \<triangleq> vis"
        and a4: "i = invariant (prog S') (invContextH (callOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S') (invocationRes S') (Some vis) )"
      by metis
      
    text {* We already assumed it holds for all possible set of visible calls *}
    
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
        by (simp add: ih1)
      show "\<forall>a. (a, False) \<notin> set tr'"
        by (simp add: ih2)
      show "state_coupling S'' S2 s "
        using ih3 by (auto simp add: state_coupling_def a1)
    qed
  qed
qed


lemma convert_to_single_session_trace_invFail_step:
fixes tr :: trace
  and s :: session      
  and S S' :: state
assumes step: "S ~~ (s,a) \<leadsto> S'"
    and S_wellformed: "state_wellFormed S"
    and noFails: "a \<noteq> AFail"
    (* invariant holds in the initial state *)
    and inv: "invariant_all S"
    (* invariant no longer holds *)
    and not_inv: "\<not>invariant_all S'"
    and coupling: "state_coupling S S2 s"
    (* we assume that we are not in a transaction (inside a transaction it is not necessary for invariants to hold)*)
    and not_in_transaction: "currentTransaction S s = None "
shows "\<exists>tr' S2'. (S2 ~~ (s, tr') \<leadsto>\<^sub>S* S2') 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
using step proof (cases rule: step.cases)
  case (local ls f ls')
  text {* a local step does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using local by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using local by (auto simp add: consistentSnapshot_def)
  qed
  
  with inv and not_inv
  have False by simp
    
  thus ?thesis ..
next
  case (newId ls f ls' uid)
  text {* generating a new id does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using newId by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using newId by (auto simp add: consistentSnapshot_def)
  qed
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (beginAtomic ls f ls' t)
  text {* starting a transaction does not change the invariant *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using beginAtomic by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using beginAtomic by (auto simp add: consistentSnapshot_def)
  qed
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (endAtomic ls f ls' t)
  text {* Ending a transaction includes an invariant-check in the single-session semantics, so we get a failing trace. *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Commited)\<rparr>"
  
  have "S2 ~~ (s,(AEndAtomic, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls" 
     and "currentProc S2 s \<triangleq> f"  
     and "f ls = EndAtomic ls'"
     and "currentTransaction S2 s \<triangleq> t"
      using coupling local.endAtomic state_coupling_def by force+
    show "S2' 
        = S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Commited)\<rparr>"
     using S2'_def by simp
     
    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add: invariant_all_def state_coupling_def local.endAtomic(6) split: if_splits)
      fix vis
      assume a0: "S2 = S"
         and a1: "consistentSnapshot S' vis"
         and a2: "\<not> invariant (prog S') (invContextVis S' vis)"
      
      show "\<exists>vis. consistentSnapshot S2' vis \<and> \<not> invariant (prog S2') (invContextVis S2' vis)"
      proof (rule exI[where x=vis], intro conjI)
        from a1
        show "consistentSnapshot S2' vis"
          by (auto simp add: consistentSnapshot_def S2'_def `S2 = S`  local.endAtomic(2))
          
        from a2
        show "\<not> invariant (prog S2') (invContextVis S2' vis)"  
          by (auto simp add: S2'_def `S2 = S`  local.endAtomic(2))
      qed    
    qed
  qed  
  
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (dbop ls f Op args ls' t c res vis)
  text {* assumption: we are not inside a transaction *}
  
  with not_in_transaction
  have False
    by simp
  
  thus ?thesis ..
next
  case (pull ls vis newTxns newCalls)
  text {* pulling in new transactions only  *}
  
  have "invariant_all S' = invariant_all S"
  proof (rule show_invariant_all_changes)
    show "invContextVis S' vis = invContextVis S vis" for vis
      using pull by (auto simp add: invContextH_def)
    show "prog S' = prog S"
      using local.step prog_inv by auto
    show "consistentSnapshot S' = consistentSnapshot S"
      using pull by (auto simp add: consistentSnapshot_def)
  qed  
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (invocation procName args initialState impl)
  
  
  
  then show ?thesis sorry
next
  case (return ls f res)
  then show ?thesis sorry
next
  case (fail ls)
  then show ?thesis
    using noFails by blast 
next
  case (invCheck vis res)
  then show ?thesis
    using inv not_inv by blast 
qed

lemma convert_to_single_session_trace_invFail:
fixes tr :: trace
  and s :: session      
  and S S' :: state
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and singleSession: "\<And>a. a\<in>set tr \<Longrightarrow> fst a = s"
    and noFails: "(s, AFail) \<notin> set tr"
    (* invariant holds in the initial state *)
    and inv: "invariant (prog S) (invContext S s)"
    (* invariant no longer holds *)
    and not_inv: "invariant (prog S') (invContext S' s)"
shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
sorry (* TODO *)
           
lemma GreatestI2:
assumes example: "Q k"
   and impl: "\<And>i. Q i \<Longrightarrow> P i"
   and bound: "\<And>i. Q i \<Longrightarrow> i < bound"
shows "P (GREATEST x::nat. Q x)"
proof -
  
  have "Q (GREATEST x::nat. Q x)"
  using example proof (rule GreatestI)
    show "\<forall>y. Q y \<longrightarrow> y < bound" using bound by simp
  qed
  thus "P (GREATEST x::nat. Q x)"
    using impl by blast
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
  
  text {* We may also assume that there are no failures *}
  assume noFail: "\<And>s. (s, AFail) \<notin> set trace"
  
  text {* We show that the trace must be correct (proof by contradiction). *}
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"
    
    text {* If the trace is incorrect, there must be a failing invariant check in the trace: *}
    from this obtain s where "(s, AInvcheck False) \<in> set trace"
       using steps by (auto simp add: traceCorrect_def)
    
     
    from this
    obtain invFailPos where invFailPos_def: "trace ! invFailPos = (s, AInvcheck False)" and invFailPos_inrange: "invFailPos < length trace"
      by (meson in_set_conv_nth)
    
    text {*
      Consider two cases: Either there is a beginAtomic before the failing invariant check
      or there is none, in which case we consider the invocation before
    *}
    {
      text "Case 1: There is a transaction before invFailPos"
      assume beginAtomic_before: "\<exists>startPos txId. startPos < invFailPos \<and>  trace ! startPos = (s, ABeginAtomic txId)"
      obtain startPos txId
        where startPos_before: "startPos < invFailPos"
          and startPos_beginAtomic: "trace ! startPos = (s, ABeginAtomic txId)"
          and startPos_greatest: "\<And>startPos' txId'. \<lbrakk>startPos' < invFailPos; trace ! startPos' = (s, ABeginAtomic txId')\<rbrakk> \<Longrightarrow> startPos' \<le> startPos"
      proof (atomize_elim, auto, rule exI, intro conjI)
        
        obtain startPos txId
          where startPos_before: "startPos < invFailPos"
            and startPos_beginAtomic: "trace ! startPos = (s, ABeginAtomic txId)"
          using beginAtomic_before by blast
      
        show "(GREATEST i. \<exists>tx. i < invFailPos \<and> trace ! i = (s, ABeginAtomic tx)) < invFailPos"
          using Greatest_smaller beginAtomic_before by presburger
        show "\<exists>txId. trace ! (GREATEST i. \<exists>tx. i < invFailPos \<and> trace ! i = (s, ABeginAtomic tx)) = (s, ABeginAtomic txId)"
        proof (rule GreatestI2)
          show "\<exists>tx. startPos < invFailPos \<and> trace ! startPos = (s, ABeginAtomic tx)"
            using startPos_before startPos_beginAtomic by blast
          show "\<And>i. \<exists>tx. i < invFailPos \<and> trace ! i = (s, ABeginAtomic tx) \<Longrightarrow> \<exists>txId. trace ! i = (s, ABeginAtomic txId)"
            by blast  
          show "\<And>i. \<exists>tx. i < invFailPos \<and> trace ! i = (s, ABeginAtomic tx) \<Longrightarrow> i < invFailPos"
            by simp
        qed    
        show "\<forall>startPos'<invFailPos. (\<exists>txId'. trace ! startPos' = (s, ABeginAtomic txId')) \<longrightarrow> startPos' \<le> (GREATEST i. \<exists>tx. i < invFailPos \<and> trace ! i = (s, ABeginAtomic tx))"
          by (metis (mono_tags, lifting) Greatest_le)
          
      qed  
      
      define trace_until_begin where "trace_until_begin \<equiv> take startPos trace"
      
      text {* Let S_at_begin be the state at the betinAtomic  *}
      obtain S_at_begin
        where steps_until_begin: "initialState program ~~ trace_until_begin \<leadsto>* S_at_begin"
        using steps
        by (metis append_take_drop_id steps_append trace_until_begin_def) 
        
      define trace_begin_to_invcheck where "trace_begin_to_invcheck \<equiv> drop startPos (take invFailPos trace)"
      
      define trace_rest where "trace_rest \<equiv> drop (Suc invFailPos) trace"
      
      have trace_split: "trace = trace_until_begin @ trace_begin_to_invcheck @ [(s, AInvcheck False)] @ trace_rest"
      proof (rule nth_equalityI)
        have [simp]: "invFailPos < length trace" using invFailPos_inrange .
        hence [simp]: "startPos < length trace"
          using dual_order.strict_trans startPos_before by blast
          
          
      
        show "length trace = length (trace_until_begin @ trace_begin_to_invcheck @ [(s, AInvcheck False)] @ trace_rest)"
          apply (auto simp add: trace_until_begin_def trace_begin_to_invcheck_def trace_rest_def)
          using invFailPos_inrange startPos_before by linarith
        
        show "\<forall>i<length trace. trace ! i = (trace_until_begin @ trace_begin_to_invcheck @ [(s, AInvcheck False)] @ trace_rest) ! i"
          apply (auto simp add: nth_append trace_until_begin_def trace_begin_to_invcheck_def trace_rest_def)
          apply (metis (no_types, lifting) \<open>startPos < length trace\<close> add_diff_inverse_nat invFailPos_inrange leD le_add_diff_inverse2 le_less_linear length_take less_diff_conv less_imp_le_nat min_def nth_drop nth_take)
          by (metis Cons_nth_drop_Suc \<open>startPos < length trace\<close> add.commute invFailPos_def invFailPos_inrange le_add_diff_inverse2 le_less_linear less_diff_conv less_imp_le_nat min_absorb2 nth_drop startPos_before)
      qed    
      
      
      obtain S_at_invcheck
        where steps_begin_to_invcheck: "S_at_begin ~~ trace_begin_to_invcheck \<leadsto>* S_at_invcheck"
        using steps steps_until_begin trace_begin_to_invcheck_def trace_until_begin_def
          apply auto
          by (metis (mono_tags, hide_lams) append_take_drop_id drop_take steps_append steps_append2)
       
      have steps_to_invcheck: "initialState program ~~ trace_until_begin @ trace_begin_to_invcheck \<leadsto>* S_at_invcheck"  
        using steps steps_append2 steps_begin_to_invcheck steps_until_begin by blast 
        
      text {* the invariant fails at S_at_invcheck: *}  
      obtain S_at_invcheck'
        where "S_at_invcheck ~~ (s, AInvcheck False) \<leadsto> S_at_invcheck'"
        using steps trace_split apply auto
        using steps_append2 steps_appendFront steps_begin_to_invcheck steps_until_begin by auto
          
      hence S_at_invcheck_invFail: "\<not>invariant (prog S_at_invcheck) (invContext S_at_invcheck s) "
        and S_at_invcheck'_eq: "S_at_invcheck = S_at_invcheck'"
        and S_at_invcheck_vis: "\<exists>vis. visibleCalls S_at_invcheck s \<triangleq> vis"
        and S_at_invcheck_notx: "currentTransaction S_at_invcheck s = None"
        by (auto simp add: step_simps)
      
      from steps_to_invcheck
      have prog_at_invcheck: "prog S_at_invcheck = program"
        using step_prog_invariant by (auto simp add: initialState_def)
        
      with S_at_invcheck_invFail  
      have "\<not> invariant program (invContext S_at_invcheck s)" by simp
        
      text {*
       Now consider two cases:
        Either the invariant holds in state S_at_begin or it does not.
      *}
      {
        text {* First consider the case where the invariant holds: *}
        assume "invariant program (invContext S_at_begin s)"
        
        text {*
        Then we can execute the single session program starting from this state ...
        *}
        obtain tr' S2 
          where "S_at_begin ~~ (s, tr') \<leadsto>\<^sub>S* S2"
            and "\<forall>a. (a, False) \<notin> set tr'"
            and "if currentTransaction S_at_invcheck s = None then 
                   \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S_at_invcheck s orElse {} 
                        \<and> S2 = S_at_invcheck\<lparr>visibleCalls := (visibleCalls S_at_invcheck)(s := vis')\<rparr> 
                 else 
                   S2 = S_at_invcheck"
        proof (atomize_elim, rule convert_to_single_session_trace[OF steps_begin_to_invcheck])
          show "state_wellFormed S_at_begin"
            using state_wellFormed_combine state_wellFormed_init steps_until_begin by blast
          show "\<And>a. a \<in> set trace_begin_to_invcheck \<Longrightarrow> fst a = s"
            sorry (* TODO this only holds until endAtomic (we have packed transactions )*)
          show "(s, AFail) \<notin> set trace_begin_to_invcheck"
            by (metis UnCI append_take_drop_id noFail set_append trace_begin_to_invcheck_def)
            
        
        find_theorems steps_s
        
        
        (*
        | invCheck:
  "\<lbrakk>currentTransaction C s = None;
   visibleCalls C s \<triangleq> vis;
   invariant (prog C) (invContext C s) = res
   \<rbrakk> \<Longrightarrow>  C ~~ (s, AInvcheck res) \<leadsto> C"   
   *)
        
      
      
      }
      
      
      have False sorry
    }
    proof       
      
    from this obtain startPos
      where "startPos < invFailPos"
        and "(\<exists>txId. trace ! startPos = (s, ABeginAtomic txId)) \<or> ()"
       
   (* TODO now we need to split up the transactions one by one *)    
    
    
  
  

  (* Goal: show that there is a failing trace in the single-session semantics (contradiction to works_in_single_session) *)
qed



end