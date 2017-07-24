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
definition state_coupling :: "state \<Rightarrow> state \<Rightarrow> session \<Rightarrow> bool \<Rightarrow> bool" where
"state_coupling S S' s sameSession \<equiv> 
   if sameSession then
      (* did a step in the same session *)
      if currentTransaction S s = None 
      then \<exists>vis'. vis' orElse {} \<subseteq> visibleCalls S s orElse {} \<and> S' = S\<lparr>visibleCalls := (visibleCalls S)(s := vis') \<rparr> 
      else S' = S
   else 
      (* did step in a different session *)
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
      (* local state on s unchanged *)
      \<and> localState S s = localState S' s
      \<and> currentProc S s = currentProc S' s
      \<and> currentTransaction S s = currentTransaction S' s
      \<and> prog S = prog S'
      "
  
(*

record operationContext = 
  calls :: "callId \<rightharpoonup> call"
  happensBefore :: "callId rel"

record distributed_state = operationContext +
  prog :: prog
  callOrigin :: "callId \<rightharpoonup> txid"
  generatedIds :: "uniqueId set"
  knownIds :: "uniqueId set"
  invocationOp :: "session \<rightharpoonup> (procedureName \<times> any list)"
  invocationRes :: "session \<rightharpoonup> any"
  transactionStatus :: "txid \<rightharpoonup> transactionStatus"

record state = distributed_state + 
  localState :: "session \<rightharpoonup> localState"
  currentProc :: "session \<rightharpoonup> procedureImpl"
  visibleCalls :: "session \<rightharpoonup> callId set"
  currentTransaction :: "session \<rightharpoonup> txid"
*)
      
      
lemma state_coupling_same_inv:
assumes "state_coupling S S' s True"
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
    and packed: "packed_trace tr"
    and noFails: "(s, AFail) \<notin> set tr"
    (* invariant holds on all states in the execution *)
    and inv: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
shows "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<forall>a. (a, False)\<notin>set tr')
        \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
        (* TODO special case for fail, pull (and others?) *)
using steps S_wellformed packed inv noFails proof (induct rule: steps.induct)
  case (steps_refl S)
  
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="S"], intro conjI; simp?)
    show "S ~~ (s, []) \<leadsto>\<^sub>S* S"
      by (simp add: steps_s_refl) 
    show "state_coupling S S s True"
    unfolding state_coupling_def 
    by auto
  qed
next
  case (steps_step S tr S' a S'')
  hence  steps: "S ~~ tr \<leadsto>* S'"
    and S_wf: "state_wellFormed S"
    and  IH: "\<lbrakk>state_wellFormed S; packed_trace tr; 
               \<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'\<rbrakk> 
               \<Longrightarrow> \<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
                   \<and> (\<forall>a. (a, False) \<notin> set tr') 
                   \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
    and  step: "S' ~~ a \<leadsto> S''"
    and  packed: "packed_trace (tr @ [a])"
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
         \<and> (state_coupling S' S2 s (tr = [] \<or> fst (last tr) = s))"
  proof (rule IH)
    have "isPrefix tr (tr@[a])"
      by simp
    thus "packed_trace tr"
      using packed prefixes_are_packed by blast 
    show "\<And>tr' S'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using prefix_invariant isPrefix_append by blast 
    show "state_wellFormed S" using S_wf .
  qed
    
  from this obtain tr' S2
      where ih1: "S ~~ (s, tr') \<leadsto>\<^sub>S* S2"
        and ih2: "\<And>a. (a, False) \<notin> set tr'"
        and ih3': "state_coupling S' S2 s  (tr = [] \<or> fst (last tr) = s)"
      by blast
  
  show  "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s (tr @ [a] = [] \<or> fst (last (tr @ [a])) = s)"  
  proof (cases "fst a = s"; simp)
    case True (* the new action is on session s *)
    hence [simp]: "fst a = s" .
  
  show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s True"  (is ?goal) 
  proof (cases "tr = [] \<or> fst (last tr) = s")
    case True (* the previous action was on the same trace (if there was a previous action) *)
    hence [simp]: "tr = [] \<or> fst (last tr) = s" by simp
    hence ih3: "state_coupling S' S2 s True"
      using ih3' by simp
    
    
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
      
  show ?goal
  proof (cases "snd a")
    case ALocal
    hence "a = (s, ALocal)"
      by (simp add: prod.expand) 

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
      show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s True"
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
      show "state_coupling S'' (S''\<lparr>visibleCalls := visibleCalls S2\<rparr>) s True"
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
    case (ABeginAtomic txId txns)
    hence [simp]: "a = (s, ABeginAtomic txId txns)"
      by (simp add: prod_eqI steps_step.prems) 
    
    with step
    have step': "S' ~~ (s, ABeginAtomic txId txns) \<leadsto> S''" by simp
    
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
    proof (rule step_s.beginAtomic; auto?)  
      show "prog S' = prog S2"
        by (simp add: S2_prog)
      
      define newS where "newS =  (S'\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := currentTransaction S2(s \<mapsto> txId), transactionStatus := transactionStatus S2(txId \<mapsto> Uncommited)\<rparr>)"
      
      have [simp]: "consistentSnapshot newS vis \<Longrightarrow> consistentSnapshot S' vis" for vis
        apply (auto simp add: consistentSnapshot_def newS_def a6' transactionConsistent_def)
        by (metis S2_transactionStatus option.inject transactionStatus.distinct(1))
        
      show "invariant_all newS" 
        using inv' apply (auto simp add: invariant_all_def)
        using S2_currentTransaction S2_localState S2_transactionStatus newS_def a1 inv'' invariant_all_def by auto
        
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
      show "state_coupling S'' S'' s True"  
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
      show "state_coupling S'' S'' s True"
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
      show "state_coupling S'' S'' s True"
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
      show " state_coupling S'' S2 s True"
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
      show "invariant_all S2"
        using ih3' inv_S' state_coupling_same_inv by auto
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
      show "state_coupling S'' S'' s True"
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
      show "state_coupling S'' S'' s True"
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
      show "state_coupling S'' S2 s True"
        using ih3 by (auto simp add: state_coupling_def a1)
    qed
  qed
next
  case False (* we are coming from a different case and executing an action on s now  *)
  hence [simp]: "tr \<noteq> []" and [simp]: "fst (last tr) \<noteq> s" by auto
  
  hence ih3: "state_coupling S' S2 s  False" using ih3' by simp
  
  text {* Because the trace is packed, there can only be two cases where we can go from another session to s: *}
  have "(\<exists>tx. (snd a) = ABeginAtomic tx) \<or> (\<exists>p ar. (snd a) = AInvoc p ar)"
  proof (rule context_switches_in_packed[OF packed])
    show "tr @ [a] = butlast tr @ [(fst (last tr), snd (last tr)), (s, snd a)] @ []"
      apply auto
      by (metis True prod.collapse)
    show "fst (last tr) \<noteq> s"
      by simp
  qed
  thus ?thesis
  proof (rule disjE; clarsimp)
    fix tx
    assume "snd a = ABeginAtomic tx"
    
    with step
    have step': "S' ~~ (s, ABeginAtomic tx) \<leadsto> S''"
      by (metis True surjective_pairing) 
      
    from step_elim_ABeginAtomic[OF step']  
    obtain ls f ls'
      where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> ls'), 
                    currentTransaction := currentTransaction S'(s \<mapsto> tx), 
                    transactionStatus := transactionStatus S'(tx \<mapsto> Uncommited)\<rparr>"
        and a2: "localState S' s \<triangleq> ls"
        and a3: "currentProc S' s \<triangleq> f"
        and a4: "f ls = BeginAtomic ls'"
        and a5: "currentTransaction S' s = None"
        and a6: "transactionStatus S' tx = None"
        by metis
    
    find_theorems "S'" S2    
        
    show ?thesis
    proof (intro exI conjI)
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(ABeginAtomic tx, True)])"
        using ih2 by auto
        
      show "state_coupling S'' S'' s True"
        by (auto simp add: state_coupling_def)
      
      have "S2 ~~ (s, ABeginAtomic tx, True) \<leadsto>\<^sub>S S''"
      proof (rule step_s.beginAtomic)
        show "localState S2 s \<triangleq> ls"
          using a2 ih3 by (simp add: state_coupling_def) 
        show "currentProc S2 s \<triangleq> f"  
          using a3 ih3  by (simp add: state_coupling_def)
        show "f ls = BeginAtomic ls'" using a4 .
        show "currentTransaction S2 s = None"
          using a5 ih3  by (auto simp add: state_coupling_def)
        show "transactionStatus S2 tx = None"
          sorry (* this is derivable from the trace *)
        show "prog S'' = prog S2"
          using ih3 local.step prog_inv  by (auto simp add: state_coupling_def)
        show "invariant_all S''"
          using inv'' by blast
        show "localState S'' s \<triangleq> ls'"
          using a2 a1 by auto
        show "currentTransaction S'' s \<triangleq> tx"
          using a1 by auto
        show "transactionStatus S'' tx \<triangleq> Uncommited"
          using a1 by auto
      qed
        
      thus "S ~~ (s, tr'@[(ABeginAtomic tx, True)]) \<leadsto>\<^sub>S*  S''"
        using ih1 steps_s_step by blast
    qed
  next
    fix p ar
    assume a0: "snd a = AInvoc p ar"
    
    with step
    have step': "S' ~~ (s, AInvoc p ar) \<leadsto> S''"
      by (metis True surjective_pairing) 
      
    from step_elim_AInvoc[OF step']  
    obtain initial impl 
      where a1: "S'' = S'\<lparr>
                    localState := localState S'(s \<mapsto> initial), 
                    currentProc := currentProc S'(s \<mapsto> impl), 
                    visibleCalls := visibleCalls S'(s \<mapsto> {}), 
                    invocationOp := invocationOp S'(s \<mapsto> (p, ar))\<rparr>"
        and a2: "localState S' s = None"
        and a3: "procedure (prog S') p ar \<triangleq> (initial, impl)"
        and a4: "uniqueIdsInList ar \<subseteq> knownIds S'"
        and a5: "invocationOp S' s = None"
      by metis
      
    show "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s True"
    proof (intro exI conjI)
      have "S2 ~~ (s, AInvoc p ar, True) \<leadsto>\<^sub>S S''"
      proof (rule step_s.intros)
        show "localState S2 s = None"
          using a2 ih3 by (simp add: state_coupling_def)
        have [simp]: "prog S2 = prog S'"
          using ih3 state_coupling_def by auto
        show "procedure (prog S2) p ar \<triangleq> (initial, impl)"
          using a3 state_coupling_def by auto
        show "uniqueIdsInList ar \<subseteq> knownIds S'"
          using a4 ih3 state_coupling_def by auto
        show "invariant_all S'"
          by (simp add: inv')
        show "invocationOp S' s = None" using a5  .
        show "S'' = S'\<lparr>localState := localState S'(s \<mapsto> initial), currentProc := currentProc S'(s \<mapsto> impl), visibleCalls := visibleCalls S'(s \<mapsto> {}), invocationOp := invocationOp S'(s \<mapsto> (p, ar))\<rparr>"
          using a1 by auto
        show "True = invariant_all S''"
          by (simp add: inv'')
      qed
      thus "S ~~ (s, tr'@[(AInvoc p ar, True)]) \<leadsto>\<^sub>S* S''"
        using ih1 steps_s_step by blast
      show "\<forall>a. (a, False) \<notin> set (tr' @ [(AInvoc p ar, True)])"
        using ih2 by auto
      show "state_coupling S'' S'' s True"
        by (auto simp add: state_coupling_def)
    qed
  qed
qed
next
  case False
  hence different_session[simp]:  "fst a \<noteq> s" by simp
  
  text {* we are now in the case of doing steps in a different session.
   We show that all of these preserve the coupling. 
   *}
   
  text {* no matter what he had before, the coupling with "False" will hold: *}
  from ih3'
  have old_coupling: "state_coupling S' S2 s False"
    by (auto simp add: state_coupling_def split: if_splits)
  
  from step
  have new_coupling: "state_coupling S'' S2 s False"
  proof (induct rule: step.cases) (* prove this with a case distinction on the action *)
    case (local C s ls f ls')
    then show ?case 
      using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (newId C s ls f ls' uid)
    thus ?case 
      using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (beginAtomic C s ls f ls' t)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (endAtomic C s ls f ls' t)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (dbop C s ls f Op args ls' t c res vis)
    
    have "callOrigin C c = None"
      using `calls C c = None`
      using S_wf dbop.hyps(1) state_wellFormed_combine steps wellFormed_callOrigin_dom2 by blast
      
    hence "callOrigin S2 c = None"
      using dbop.hyps(1) old_coupling state_coupling_def by fastforce  
      
    with dbop
    show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (pull C s ls vis newTxns newCalls)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (invocation C s procName args initialState impl)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (return C s ls f res)
    
    have "invocationRes C s = None"
      sorry (* TODO prove that each procedure can only return once, so there cannot be a return value here *)
    
    with return
    show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (fail C s ls)
    
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  next
    case (invCheck C s vis res)
    then show ?case using old_coupling different_session by (auto simp add: state_coupling_def)
  qed
  
    
  thus "\<exists>tr' S2. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) \<and> (\<forall>a. (a, False) \<notin> set tr') \<and> state_coupling S'' S2 s False"
    using ih1 ih2 by blast
    
    
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
    and coupling: "state_coupling S S2 s sameSession"
    and ctxtSwitchCases: "\<not>sameSession \<Longrightarrow> (\<exists>tx. a = ABeginAtomic tx) \<or> (\<exists>p ar. a = AInvoc p ar)"
    (* we assume that we are not in a transaction (inside a transaction it is not necessary for invariants to hold)*)
    (* and not_in_transaction: "currentTransaction S s = None " *)
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
    have "consistentSnapshot S' vis = consistentSnapshot S vis" for vis
      using beginAtomic by (auto simp add: consistentSnapshot_def transactionConsistent_def)
    thus "consistentSnapshot S' = consistentSnapshot S" ..
  qed
  
  with inv and not_inv
  have False by simp
  
  thus ?thesis ..
next
  case (endAtomic ls f ls' t)
  text {* Ending a transaction includes an invariant-check in the single-session semantics, so we get a failing trace. *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S2(t \<mapsto> Commited)\<rparr>"
  
  have [simp]: "sameSession"
    using ctxtSwitchCases local.endAtomic(1) by auto 
  
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
  text {* uncommitted operations do not affect the invariant *}
  
  have hb': "happensBefore S' = happensBefore S \<union> vis \<times> {c}"
    using dbop by auto
    
    
  
  have "invariant_all S'" if "invariant_all S"
  using that proof (auto simp add: invariant_all_def)
    fix vis'
    assume a0: "\<forall>vis. consistentSnapshot S vis \<longrightarrow> invariant (prog S) (invContextVis S vis)"
       and a1: "consistentSnapshot S' vis'"
    
    from a1
    have "vis' \<subseteq> insert c (dom (calls S))" 
      by (auto simp add: consistentSnapshot_def dbop)
    
    
      
    from a1  
    have "causallyConsistent (happensBefore S \<union> vis \<times> {c}) vis'" 
      using hb' by (auto simp add: consistentSnapshot_def causallyConsistent_def)
    
    hence "causallyConsistent (happensBefore S) vis'"
      by (auto simp add: causallyConsistent_def)
         
    
    from a1
    have "transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis'"
      by (auto simp add: consistentSnapshot_def dbop)
    
    hence "c \<notin> vis'"
      by (metis (full_types) S_wellformed fun_upd_same local.dbop(6) map_upd_eqD1 transactionConsistent_def transactionStatus.distinct(1) wellFormed_currentTransaction_unique_h(2))  
      
    with `vis' \<subseteq> insert c (dom (calls S)) `
    have "vis' \<subseteq> dom (calls S)"
      by blast 
      
    from `transactionConsistent (callOrigin S(c \<mapsto> t)) (transactionStatus S) vis'`  
    have "transactionConsistent (callOrigin S) (transactionStatus S) vis'"
      by (metis (full_types) S_wellformed fun_upd_same local.dbop(6) map_upd_eqD1 transactionConsistent_def transactionStatus.distinct(1) wellFormed_currentTransaction_unique_h(2))
      
    from `transactionConsistent (callOrigin S) (transactionStatus S) vis'`
     and `vis' \<subseteq> dom (calls S)`
     and `causallyConsistent (happensBefore S) vis'`
    have "consistentSnapshot S vis'"
      by (simp add: consistentSnapshot_def)
      
    with a0  
    have "invariant (prog S) (invContextVis S vis')"
      by blast  
    
    have [simp]: "prog S' = prog S"
      using local.step prog_inv by auto
    
    have commitedCalls_simp: 
         "commitedCallsH (callOrigin S(c \<mapsto> t)) (transactionStatus S) 
        = commitedCallsH (callOrigin S) (transactionStatus S)"
      using S_wellformed local.dbop(6) local.dbop(7) by auto
        
    have "c \<notin> commitedCalls S"
      by (simp add: S_wellformed local.dbop(7))
      
      
    have "invContextVis S' vis' = invContextVis S vis'"
      by (auto simp add: invContextH_def dbop commitedCalls_simp S_wellformed restrict_relation_def `c \<notin> commitedCalls S`)
      
    with `invariant (prog S) (invContextVis S vis')`   
    show "invariant (prog S') (invContextVis S' vis')"
      by simp
  qed    

  hence False
    by (simp add: inv not_inv)
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
  text {* invocations include an invariant-check *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := localState S2(s \<mapsto> initialState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"
  
  have "S2 ~~ (s,(AInvoc procName args, False)) \<leadsto>\<^sub>S S'"
  proof (rule step_s.intros)
    show "localState S2 s = None"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "procedure (prog S2) procName args \<triangleq> (initialState, impl)"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "uniqueIdsInList args \<subseteq> knownIds S"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invocationOp S s = None"
      using invocation coupling by (auto simp add: state_coupling_def split: if_splits)
    show "invariant_all S"
      by (simp add: inv)
    show "S' = S\<lparr>localState := localState S(s \<mapsto> initialState), currentProc := currentProc S(s \<mapsto> impl), visibleCalls := visibleCalls S(s \<mapsto> {}), invocationOp := invocationOp S(s \<mapsto> (procName, args))\<rparr>"
      using local.invocation(2) by blast  
    show "False = invariant_all S'"
      by (simp add: not_inv)
  qed    
    
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (return ls f res)
  text {* return contains an invariant check *}
  
  define S2' where "S2' \<equiv> S2\<lparr>localState := (localState S2)(s := None), 
                              currentProc := (currentProc S2)(s := None), 
                              visibleCalls := (visibleCalls S2)(s := None), 
                              invocationRes := invocationRes S2(s \<mapsto> res), 
                              knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"
  
  have [simp]: sameSession
    using ctxtSwitchCases local.return(1) by auto                             
                              
  have "S2 ~~ (s,(AReturn res, False)) \<leadsto>\<^sub>S S2'"
  proof (rule step_s.intros)
    show "localState S2 s \<triangleq> ls"
     and "currentProc S2 s \<triangleq> f"
     and "f ls = Return res"
     and "currentTransaction S2 s = None"
      using return coupling by (auto simp add: state_coupling_def)
  
    show "S2' = S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S2(s \<mapsto> res), knownIds := knownIds S2 \<union> uniqueIds res\<rparr>"
      using S2'_def by simp
  
    have not_in_transaction: "currentTransaction S s = None"
      using S_wellformed return wellFormed_invoc_notStarted(1) by auto  
      
    from not_inv coupling
    show "False = invariant_all S2'"
    proof (auto simp add: invariant_all_def state_coupling_def not_in_transaction)
      fix vis vis'
      assume a0: "consistentSnapshot S' vis"
         and a1: "\<not> invariant (prog S') (invContextVis S' vis)"
         and a2: "vis' orElse {} \<subseteq> visibleCalls S s orElse {}"
         and a3: "S2 = S\<lparr>visibleCalls := (visibleCalls S)(s := vis')\<rparr>"
      
      show "\<exists>vis. consistentSnapshot S2' vis \<and> \<not> invariant (prog S2') (invContextVis S2' vis)"
      proof (rule exI[where x="vis"], intro conjI)
        show "consistentSnapshot S2' vis"
          using a0 by (auto simp add: consistentSnapshot_def S2'_def a3  return(2))
          
        from a1
        show "\<not> invariant (prog S2') (invContextVis S2' vis)"  
          using a0 by (auto simp add: consistentSnapshot_def S2'_def a3  return(2))
      qed 
    qed
  qed
      
  then show ?thesis
    using steps_s_refl steps_s_step by fastforce 
next
  case (fail ls)
  text {* we assumed that there are no fails *}
  then show ?thesis
    using noFails by blast
next
  case (invCheck vis res)
  then show ?thesis
    using inv not_inv by blast (* same state *)
qed

lemma convert_to_single_session_trace_invFail:
fixes tr :: trace
  and S S' :: state
assumes steps: "S ~~ tr \<leadsto>* S'"
    and S_wellformed: "state_wellFormed S"
    and packed: "packed_trace tr"
    and noFails: "\<And>s. (s, AFail) \<notin> set tr"
    (* invariant holds in the initial state *)
    and inv: "invariant_all S"
    (* invariant no longer holds *)
    and not_inv: "\<not> invariant_all S'"
shows "\<exists>tr' S2 s. (S ~~ (s, tr') \<leadsto>\<^sub>S* S2) 
        \<and> (\<exists>a. (a, False)\<in>set tr')"
proof -
  
  have not_inv_ex: "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail"
    by (rule exI[where x="tr"], rule exI[where x="S'"], auto  simp add: not_inv steps)
    

  text {* There must be a place where the invariant fails for the first time: *}
  obtain tr1 a tr2 S1 S_fail
    where tr_split: "tr = tr1@a#tr2"
      and steps1: "S ~~ tr1 \<leadsto>* S1"
      and stepA: "S1 ~~ a \<leadsto> S_fail"
      and first_not_inv: "\<not>invariant_all S_fail"
      and inv_before: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr1; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S' "
  proof (atomize_elim)  
    show "\<exists>tr1 a tr2 S1 S_fail. tr = tr1 @ a # tr2 \<and> (S ~~ tr1 \<leadsto>* S1) \<and> (S1 ~~ a \<leadsto> S_fail) \<and> \<not> invariant_all S_fail \<and> (\<forall>S' tr'. isPrefix tr' tr1 \<longrightarrow> (S ~~ tr' \<leadsto>* S') \<longrightarrow> invariant_all S')"
    using steps inv not_inv_ex proof (induct rule: steps_induct)
      case initial
      then show ?case
        by simp 
    next
      case (step S' tr a S'')
      then show ?case 
      proof (cases "\<exists>tr_pre S_fail. isPrefix tr_pre tr \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail")
        case True
        then show ?thesis
          using inv step.IH by force 
      next
        case False
        
        hence invariant_in_tr: "\<And>S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
          by blast
        
        from `\<exists>tr_pre S_fail. isPrefix tr_pre (tr @ [a]) \<and> (S ~~ tr_pre \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail`
        obtain tr_pre S_fail 
          where "isPrefix tr_pre (tr @ [a])" 
          and "S ~~ tr_pre \<leadsto>* S_fail" 
          and "\<not> invariant_all S_fail"
          by blast
        
        have "tr_pre = tr @ [a]"
        proof (rule ccontr)
          assume "tr_pre \<noteq> tr @ [a]"
          with `isPrefix tr_pre (tr @ [a])`
          have "isPrefix tr_pre tr"
            by (metis (no_types, lifting) append_eq_append_conv_if append_take_drop_id isPrefix_def length_append_singleton not_less_eq_eq take_all)
          
          with invariant_in_tr
          have "invariant_all S_fail"
            using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> by blast
          with `\<not> invariant_all S_fail`
          show False ..
        qed
        
        hence "S_fail = S''"
          using \<open>S ~~ tr_pre \<leadsto>* S_fail\<close> step.step step.steps steps_step traceDeterministic by blast
          
        with `\<not> invariant_all S_fail`
        have "\<not>invariant_all S''"
          by auto
          
        
        show ?thesis 
         using step invariant_in_tr `\<not>invariant_all S''` by blast 
      qed
    qed  
  qed
  
  obtain as aa where a_def: "a = (as,aa)"
    by force
  
  thm convert_to_single_session_trace
  obtain tr1' S1' 
    where tr1'_steps: "S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'"
      and tr1'_ok: "\<forall>a. (a, False)\<notin>set tr1'"
      and tr1'_coupling: "state_coupling S1 S1' as (tr1 = [] \<or> fst (last tr1) = as)"
  proof (atomize_elim, rule convert_to_single_session_trace)
    show "S ~~ tr1 \<leadsto>* S1" using steps1 .
    show "state_wellFormed S" using S_wellformed .
    show "packed_trace tr1"
      using isPrefix_appendI packed prefixes_are_packed tr_split by blast 
    show "(as, AFail) \<notin> set tr1" using tr_split noFails by auto
    show "\<And>S' tr1'. \<lbrakk>isPrefix tr1' tr1; S ~~ tr1' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant_all S'"
      using inv_before by auto
  qed
  
  have tr1_packed: "packed_trace (tr1@[a])"     
  using packed proof (rule prefixes_are_packed)
    have "isPrefix (tr1 @ [a]) ((tr1 @ [a]) @ tr2)" by (rule isPrefix_appendI)
    thus "isPrefix (tr1 @ [a]) tr" using tr_split by auto
  qed  
    
  
  obtain tr_a S_fail'
    where steps_tr_a: "S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'"
      and tr_a_fails: "\<exists>a. (a, False)\<in>set tr_a"
  proof (atomize_elim, rule convert_to_single_session_trace_invFail_step)
    show "S1 ~~ (as,aa) \<leadsto> S_fail"
      using a_def stepA by blast
    show "state_wellFormed S1"
      using S_wellformed state_wellFormed_combine steps1 by blast
    show "aa \<noteq> AFail"
      using a_def noFails tr_split by auto
    show "invariant_all S1"
      using inv_before isPrefix_refl steps1 by blast
    show "\<not> invariant_all S_fail"
      by (simp add: first_not_inv)
    show "state_coupling S1 S1' as (tr1 = [] \<or> fst (last tr1) = as)"  
      using tr1'_coupling .
      
       
    assume "\<not> (tr1 = [] \<or> fst (last tr1) = as)"
    hence "tr1 \<noteq> []" and "fst (last tr1) \<noteq> as"
      by auto
    show "(\<exists>tx. aa = ABeginAtomic tx) \<or> (\<exists>p ar. aa = AInvoc p ar)"  
    using tr1_packed proof (rule context_switches_in_packed)
      show "tr1 @ [a] = butlast tr1 @ [(fst (last tr1), snd (last tr1)), (as, aa)] @ []"
        by (simp add: \<open>tr1 \<noteq> []\<close> a_def)
      show "fst (last tr1) \<noteq> as"
        by (simp add: \<open>fst (last tr1) \<noteq> as\<close>)
    qed    
  qed    
    
  show ?thesis
  proof (rule exI[where x="tr1'@tr_a"], rule exI[where x="S_fail'"], rule exI[where x="as"], intro conjI)
    from `S ~~ (as, tr1') \<leadsto>\<^sub>S* S1'` 
     and `S1' ~~ (as, tr_a) \<leadsto>\<^sub>S* S_fail'`
    show " S ~~ (as, tr1' @ tr_a) \<leadsto>\<^sub>S* S_fail'"
      by (rule steps_s_append)  
    show "\<exists>a. (a, False) \<in> set (tr1' @ tr_a)"
      using tr_a_fails by auto
  qed
qed

lemma wellFormed_state_consistent_snapshot:
assumes wf: "state_wellFormed S"
assumes vis: "visibleCalls S s \<triangleq> vis"
assumes noTx: "currentTransaction S' s = None" 
shows "consistentSnapshot S vis"
unfolding consistentSnapshot_def proof (intro conjI)
  show "vis \<subseteq> dom (calls S)"
    using wf vis
    using wellFormed_visibleCallsSubsetCalls_h(2) by auto 
    
  show "causallyConsistent (happensBefore S) vis"
    using wf vis apply (auto simp add: causallyConsistent_def)
    sorry (* TODO *)
  
  show "transactionConsistent (callOrigin S) (transactionStatus S) vis"
    using wf vis noTx apply (auto simp add: transactionConsistent_def)
    sorry (* TODO *)
qed
    

text {* if there is an failing invariant check in the trace, then there is a prefix of the trace leading to a
  state that does not satisfy the invariant *}
lemma invCheck_to_failing_state:
assumes steps: "S ~~ trace \<leadsto>* S'"
    and inv_fail: "(s, AInvcheck False) \<in> set trace"
    and state_wf: "state_wellFormed S"
shows "\<exists>tr' S_fail. isPrefix tr' trace \<and> (S ~~ tr' \<leadsto>* S_fail) \<and> \<not> invariant_all S_fail" 
using steps inv_fail proof (induct rule: steps_induct)
  case initial
  then show ?case
    by auto 
next
  case (step S' tr a S'')
  show ?case 
  proof (cases "(s, AInvcheck False) \<in> set tr")
    case True
    with step.IH
    obtain tr' S_fail 
      where "isPrefix tr' tr" 
        and"S ~~ tr' \<leadsto>* S_fail" 
        and "\<not> invariant_all S_fail"
      by blast
      
    then show ?thesis
      using isPrefix_append by blast 
      
  next
    case False
    with `(s, AInvcheck False) \<in> set (tr @ [a])`
    have "a = (s, AInvcheck False)" by auto
    
    show ?thesis
    proof (intro exI conjI)
      show "isPrefix (tr @ [a]) (tr @ [a])"
        by simp
      show "S ~~ tr @ [a] \<leadsto>* S''"
        using step.step step.steps steps_step by auto   
      
      from `S' ~~ a \<leadsto> S''`
      have "S' ~~ (s, AInvcheck False) \<leadsto> S''" using `a = (s, AInvcheck False)` by simp
      from this
      obtain vis 
        where "\<not> invariant (prog S') (invContextVis S' vis)" 
          and [simp]: "S'' = S'" 
          and "currentTransaction S' s = None" 
          and "visibleCalls S' s \<triangleq> vis"
        by (auto simp add: step_simps)
        
      show "\<not> invariant_all S''"  
      proof (auto simp add: invariant_all_def, rule exI[where x=vis], intro conjI)
        from `\<not> invariant (prog S') (invContextVis S' vis)`
        show "\<not> invariant (prog S') (invContextVis S' vis)" .
        
        have "state_wellFormed S'"
          using state_wellFormed_combine state_wf step.steps by blast
          
        with `visibleCalls S' s \<triangleq> vis`
        show "consistentSnapshot S' vis"
          using \<open>currentTransaction S' s = None\<close> wellFormed_state_consistent_snapshot by blast
      qed    
    qed
  qed
qed

           
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

lemma prefix_induct[case_names Nil snoc[IH]]:
assumes empty: "P []"
    and step: "\<And>ys a. \<lbrakk>\<And>xs. isPrefix xs ys \<Longrightarrow> P xs\<rbrakk> \<Longrightarrow> P (ys@[a])"
shows "P xs"
proof -
  have "\<forall>xs'. isPrefix xs' xs \<longrightarrow> P xs'"
  using assms proof (induct rule: rev_induct)
    case Nil
    then show ?case
      by simp 
  next
    case (snoc x ys)
    find_theorems name: local.snoc
    show ?case
    proof auto
      fix xs' 
      assume a1: "isPrefix xs' (ys @ [x])"
      show "P xs'"
      proof (cases "isPrefix xs' ys")
        case True
        then show ?thesis
          using local.empty local.step snoc.hyps by blast 
      next
        case False
        with a1
        have "xs' = ys@[x]"
          apply (auto simp add: isPrefix_def)
          by (metis append_self_conv butlast.simps(2) diff_is_0_eq nat_le_linear not_le take_all take_butlast take_eq_Nil)
        
        have " P (ys@[x])"
        proof (rule local.snoc(3))
          show "\<And>xs. isPrefix xs ys \<Longrightarrow> P xs"
            using local.empty local.step snoc.hyps by blast
        qed    
        thus "P xs'" using `xs' = ys@[x]` by simp
      qed
    qed
  qed
  thus "P xs"
    by simp
qed  

lemma smallestPrefix_exists:
fixes tr :: "'a list"
  and  x :: 'b
assumes example: "P tr x"
shows "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not>isPrefix tr' tr)"
using example proof (induct tr arbitrary: x rule: prefix_induct)
  case Nil
  show ?case
  proof (rule exI[where x="[]"], rule exI[where x="x"], auto)
    show "P [] x" using Nil .
  qed
next
  case (snoc xs a)
  show ?case 
  proof (cases "\<exists>tr' x'. P tr' x' \<and> isPrefix tr' xs")
  case True
    from this obtain tr' x'
      where "isPrefix tr' xs" and "P tr' x'"
      by blast
    thus "\<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
      by (rule snoc.IH)
  next 
    case False
    hence noPrefix: "\<not>isPrefix tr' xs" if "P tr' x'" for tr' x'
      using that by blast
      
    show " \<exists>tr x. P tr x \<and> (\<forall>tr' x'. P tr' x' \<and> tr' \<noteq> tr \<longrightarrow> \<not> isPrefix tr' tr)"
    proof (rule exI[where x="xs@[a]"], rule exI[where x=x], intro conjI allI impI; (elim conjE)?)
      show "P (xs @ [a]) x"
        using snoc.prems .
      fix tr' x'
      assume "P tr' x'"
      hence "\<not>isPrefix tr' xs"
        using False by blast
      fix tr' x'
      assume a0: "P tr' x'"
         and a1: "tr' \<noteq> xs @ [a]"
      
      show "\<not> isPrefix tr' (xs @ [a])"
        by (metis False a0 a1 butlast_snoc isPrefix_def not_le take_all take_butlast)
    qed    
  qed 
qed
    
lemma programCorrect_s_inv_initial:
assumes "programCorrect_s program"
shows "invariant_all (initialState program)"
proof (rule ccontr)
  assume "\<not> invariant_all (initialState program)"
  
  text {* from invariant failure, start some procedure, directly get false in there ??? *}
  
  show False
    sorry
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
  
  text {* We can assume the trace is packed. *}
  assume packed: "packed_trace trace"
  
  text {* We may also assume that there are no failures *}
  assume noFail: "\<And>s. (s, AFail) \<notin> set trace"
  
  text {* We show that the trace must be correct (proof by contradiction). *}
  show "traceCorrect trace"
  proof (rule ccontr)
    assume incorrect_trace: "\<not> traceCorrect trace"
    
    text {* If the trace is incorrect, there must be a failing invariant check in the trace: *}
    from this obtain s where "(s, AInvcheck False) \<in> set trace"
       using steps by (auto simp add: traceCorrect_def)
    
    obtain tr' S_fail
       where "isPrefix tr' trace"
         and "initialState program ~~ tr' \<leadsto>* S_fail"
         and "\<not> invariant_all S_fail"
    by (atomize_elim, rule invCheck_to_failing_state[OF `initialState program ~~ trace \<leadsto>* S` `(s, AInvcheck False) \<in> set trace`], simp)     
    
    text {* No take the first state where the invariant fails *}
    from this
    obtain tr'_min S_fail_min
       where tr'_min_prefix: "isPrefix tr'_min trace"
         and S_fail_min_steps:"initialState program ~~ tr'_min \<leadsto>* S_fail_min"
         and S_fail_min_fail: "\<not> invariant_all S_fail_min"    
         and S_fail_min_min: "\<And>tr' S_fail. \<lbrakk>isPrefix tr' trace; initialState program ~~ tr' \<leadsto>* S_fail; \<not> invariant_all S_fail; tr' \<noteq> tr'_min\<rbrakk> \<Longrightarrow> \<not>isPrefix tr' tr'_min"
      using smallestPrefix_exists[where P="\<lambda>tr x. isPrefix tr trace \<and> (initialState program ~~ tr \<leadsto>* x) \<and> \<not> invariant_all x"]
      by metis
    
    text {* Next get the invocation start before the failure *}  
      
    find_theorems "(\<exists>x y. ?P x y) \<longleftrightarrow> (\<exists>y x. ?P x y)"
    
    have inv_init: "invariant_all (initialState program)"
      by (simp add: programCorrect_s_inv_initial works_in_single_session)
      
    obtain tr'_s S_fail_s s'
      where "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        and "\<exists>a. (a, False) \<in> set tr'_s"
    proof (atomize_elim)
      have "\<exists>tr'_s S_fail_s s'. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
      proof (rule convert_to_single_session_trace_invFail[OF `initialState program ~~ tr' \<leadsto>* S_fail`])
        show "state_wellFormed (initialState program)" by simp
        show "packed_trace tr'"
          using \<open>isPrefix tr' trace\<close> packed prefixes_are_packed by blast
        show "\<And>s'. (s', AFail) \<notin> set tr'"
          using `isPrefix tr' trace` noFail apply (auto simp add: isPrefix_def) (* IMPROVE extract lemma for isPrefix with \<in> or \<subseteq>*)
          by (metis in_set_takeD)
        show "invariant_all (initialState program)"
          using inv_init .
        show "\<not> invariant_all S_fail"
          by (simp add: \<open>\<not> invariant_all S_fail\<close>)
      qed
      thus "\<exists>s' tr'_s S_fail_s. (initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s) \<and> (\<exists>a. (a, False) \<in> set tr'_s)"
        by blast
    qed
    
    have not_correct: "\<not>traceCorrect_s program tr'_s"
      by (simp add: \<open>\<exists>a. (a, False) \<in> set tr'_s\<close> traceCorrect_s_def)
      
 
      
    
    from works_in_single_session
    have use_single_session: "traceCorrect_s program trace" if "invariant program (invContext init s)" and "prog init = program" and "init ~~ (s, trace) \<leadsto>\<^sub>S* S" for init trace s S
      using that by (auto simp add: programCorrect_s_def)

    have correct: "traceCorrect_s program tr'_s" 
    proof (rule use_single_session)
      show "initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s"
        using `initialState program ~~ (s', tr'_s) \<leadsto>\<^sub>S* S_fail_s` .
      show "prog (initialState program) = program"
        by (simp add: initialState_def)
      show "invariant program (invContext (initialState program) s')"
        using inv_init apply (auto simp add: invariant_all_def)
        apply (drule_tac x="{}" in spec)
        apply (drule mp)
        by (auto simp add: consistentSnapshot_def initialState_def causallyConsistent_def transactionConsistent_def invContextH_def)
    qed    
    
    with not_correct
    show False ..
  qed
qed  
   



end