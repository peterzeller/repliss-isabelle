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
    and singleSession: "\<And>a. a\<in>set tr \<Longrightarrow> fst a = s"
    (* invariant holds on all states in the execution *)
    and inv: "\<And>s' S' tr'. \<lbrakk>isPrefix tr' tr; S ~~ tr' \<leadsto>* S'\<rbrakk> \<Longrightarrow> invariant (prog S) (invContext S' s')"
shows "\<exists>tr'. (S ~~ (s, tr') \<leadsto>\<^sub>S* S') 
        \<and> (\<forall>a. (a, False)\<notin>set tr')"
using steps singleSession inv proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case
    by (meson in_set_member member_rec(2) steps_s_refl)
next
  case (steps_step S tr S' a S'')
  hence  steps: "S ~~ tr \<leadsto>* S'"
    and  IH: "\<lbrakk>\<And>a. a \<in> set tr \<Longrightarrow> fst a = s\<rbrakk>
        \<Longrightarrow> \<exists>tr' S'' a. 
              (S ~~ (s, tr') \<leadsto>\<^sub>S* S'') 
            \<and> ((s, AInvcheck False) \<in> set tr \<longrightarrow> (a, False) \<in> set tr') 
            \<and> S'' = S'"
    and  step: "S' ~~ a \<leadsto> S''"
    and  singleSession: "\<And>a'. a' \<in> set (tr @ [a]) \<Longrightarrow> fst a' = s"
    by auto
 
    from IH obtain tr' S''_s a_s
      where ih1: "S ~~ (s, tr') \<leadsto>\<^sub>S* S''_s"
        and ih2: "(s, AInvcheck False) \<in> set tr \<longrightarrow> (a_s, False) \<in> set tr'"
        and ih3: "S''_s = S'"
      using singleSession by auto 
    
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
    

        
    (*with step_s  a1*)
    from ih1
    have steps_s: "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''"
    proof (rule steps_s_step)
      from step_s
      show "S''_s ~~ (s, ALocal, True) \<leadsto>\<^sub>S S''"
        using a1 ih3 by blast
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ALocal, True)]) \<leadsto>\<^sub>S* S''" using steps_s .
      show "S'' = S''" by simp
      show "(s, AInvcheck False) \<in> set (tr @ [a]) \<longrightarrow> (a_s, False) \<in> set (tr' @ [(ALocal, True)])"
        using ih2 \<open>a = (s, ALocal)\<close> by simp
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
      show "S''_s ~~ (s, ANewId uid, True) \<leadsto>\<^sub>S S''"
        by (simp add: a1 ih3) 
    qed  
      
    show ?thesis 
    proof (intro exI conjI)
      show "S ~~ (s, tr'@[(ANewId uid, True)]) \<leadsto>\<^sub>S* S''" using steps_s .
      show "S'' = S''" by simp
      show "(s, AInvcheck False) \<in> set (tr @ [a]) \<longrightarrow> (a_s, False) \<in> set (tr' @ [(ANewId uid, True)])"
        using ih2 by simp
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
    
    have "invariant (prog S') (invContext S' s')" for s'
      
    
      
    from a2 a3 a4 a5 a6
    have step_s: "S' ~~ (s,(ABeginAtomic txId,True)) \<leadsto>\<^sub>S S'\<lparr>
                localState := localState S'(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S'(s \<mapsto> txId), 
                transactionStatus := transactionStatus S'(txId \<mapsto> Uncommited)\<rparr>"
      proof (rule step_s.beginAtomic)  
      
    then show ?thesis sorry
  next
    case AEndAtomic
    then show ?thesis sorry
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis sorry
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