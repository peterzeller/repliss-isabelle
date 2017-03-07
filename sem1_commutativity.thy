theory sem1_commutativity
imports replissSem1
begin



definition commutativeS :: "state \<Rightarrow> session \<times> action \<Rightarrow> session \<times> action \<Rightarrow> bool" where
"commutativeS s a b \<equiv> (\<forall>t. ((s ~~ [a,b] \<leadsto>*  t) \<longleftrightarrow> (s ~~ [b,a] \<leadsto>* t)))"


lemma useCommutativeS:
assumes "commutativeS s a b"
shows "(s ~~ [a,b] \<leadsto>*  t) \<longleftrightarrow> (s ~~ [b,a] \<leadsto>* t)"
using assms by (simp add: commutativeS_def)


definition "precondition a C \<equiv> \<exists>C'. C ~~ a \<leadsto> C'"

lemma usePrecondition: "precondition a C \<Longrightarrow> \<exists>C'. C ~~ a \<leadsto> C'"
apply (simp add: precondition_def)
done

lemma usePrecondition2: "precondition a C \<Longrightarrow> (\<And>C'. C ~~ a \<leadsto> C' \<Longrightarrow> P C') \<Longrightarrow> \<exists>C'. (C ~~ a \<leadsto> C') \<and> P C'"
  using usePrecondition by blast

lemma commutativeS_switchArgs: 
"commutativeS s a b \<longleftrightarrow> commutativeS s b a"
by (auto simp add: commutativeS_def)
  

lemma existsAndH: "P x \<Longrightarrow> Q x \<Longrightarrow>   \<exists>x. P x \<and> Q x"
by auto

lemma preconditionI[simp]: "\<lbrakk>s ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> precondition a s"
by (auto simp add: precondition_def)

lemma show_commutativeS[case_names preAB preBA commute ]: 
assumes a1:  "\<And>s1 s2. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ b \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ a \<leadsto> s2)" 
    and a2:  "\<And>s1 s2. \<lbrakk>s ~~ b \<leadsto> s1; s1 ~~ a \<leadsto> s2\<rbrakk> \<Longrightarrow> \<exists>s1. (s ~~ a \<leadsto> s1) \<and> (\<exists>s2. s1 ~~ b \<leadsto> s2)" 
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
shows "commutativeS s a b"
apply (auto simp add: commutativeS_def  steps_appendFront)
  using a1 a4 apply blast
  using a2 a4 by blast

lemma show_commutativeS_pres[case_names preBfront preAfront preAback preBback commute ]: 
assumes a1:  "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s1\<rbrakk> \<Longrightarrow> precondition b s"
    and a1': "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s1\<rbrakk> \<Longrightarrow> precondition a s"
    and a2:  "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s\<rbrakk> \<Longrightarrow> precondition a s1"
    and a2': "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s\<rbrakk> \<Longrightarrow> precondition b s1"
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
shows "commutativeS s a b"
apply (auto simp add: commutativeS_def precondition_def steps_appendFront)
apply (rule usePrecondition2)
  using a1 precondition_def apply blast 
  apply (frule a2)
  apply simp
  using a4 usePrecondition apply blast
apply (rule usePrecondition2)
  using a1' precondition_def apply blast 
  apply (frule a2')
  apply simp
  using a4 usePrecondition apply blast 
done  

definition differentIds :: "(session \<times> action) \<Rightarrow> (session \<times> action) \<Rightarrow> bool" where
"differentIds a b \<equiv> case (a,b) of
   ((s1, ANewId u1), (s2, ANewId u2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ABeginAtomic u1), (s2, ABeginAtomic u2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ADbOp u1 o1 a1 r1), (s2, ADbOp u2 o2 a2 r2)) \<Rightarrow> (u1 \<noteq> u2)
 | _ \<Rightarrow> True"
 
lemma differentIds_newId[simp]:
"differentIds (s1, ANewId u1) (s2, ANewId u2) \<longleftrightarrow> (u1 \<noteq> u2)"
by (simp add: differentIds_def)

lemma differentIds_beginAtomic[simp]:
"differentIds (s1, ABeginAtomic u1) (s2, ABeginAtomic u2) \<longleftrightarrow> (u1 \<noteq> u2)"
by (simp add: differentIds_def)

lemma differentIds_dbop[simp]:
"differentIds (s1, ADbOp u1 o1 a1 r1) (s2, ADbOp u2 o2 a2 r2) \<longleftrightarrow> (u1 \<noteq> u2)"
by (simp add: differentIds_def)

lemma steps_to_differentIds: 
assumes step1: "s ~~ (sa,a) \<leadsto> B" and step2: "B ~~ (sb,b) \<leadsto> t"
shows "differentIds (sa,a) (sb,b)"
apply (cases a; cases b)
apply (auto simp add: differentIds_def)
using step1 step2 apply (auto simp add: step_simps split: if_splits)
done

lemma steps_to_differentIds2: 
assumes step1: "s ~~ a \<leadsto> B" and step2: "B ~~ b \<leadsto> t"
shows "differentIds a b"
  by (metis prod.swap_def step1 step2 steps_to_differentIds swap_swap)

lemma differentIds_commute: 
shows "differentIds a b = differentIds b a"
by (auto simp add: differentIds_def split: action.splits)
  

lemma show_commutativeS_pres2[case_names preBfront preAfront preAback preBback commute ]: 
assumes a1:  "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s1; differentIds a b\<rbrakk> \<Longrightarrow> precondition b s"
    and a1': "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s1; differentIds a b\<rbrakk> \<Longrightarrow> precondition a s"
    and a2:  "\<And>s1. \<lbrakk>s ~~ b \<leadsto> s1; precondition a s; differentIds a b\<rbrakk> \<Longrightarrow> precondition a s1"
    and a2': "\<And>s1. \<lbrakk>s ~~ a \<leadsto> s1; precondition b s; differentIds a b\<rbrakk> \<Longrightarrow> precondition b s1"
    and a4:  "\<And>s1 s2 s1' s2'. \<lbrakk>s ~~ a \<leadsto> s1; s1 ~~ b \<leadsto> s2; s ~~ b \<leadsto> s1'; s1' ~~ a \<leadsto> s2'\<rbrakk> \<Longrightarrow> s2 = s2'"
shows "commutativeS s a b"
proof (auto simp add: commutativeS_def precondition_def steps_appendFront)
  fix t B
  assume step1: "s ~~ a \<leadsto> B" and step2: "B ~~ b \<leadsto> t"
  
  hence dIds: "differentIds a b"
    using steps_to_differentIds2 by auto
  
  show "\<exists>B. (s ~~ b \<leadsto> B) \<and> (B ~~ a \<leadsto> t)"
    by (metis a1 a2 a4 dIds preconditionI step1 step2 usePrecondition)
next   
  fix t B
  assume step1: "s ~~ b \<leadsto> B" and step2: "B ~~ a \<leadsto> t"
  
  hence dIds: "differentIds a b"
    using steps_to_differentIds2
    using differentIds_commute by blast 
  
  show "\<exists>B. (s ~~ a \<leadsto> B) \<and> (B ~~ b \<leadsto> t)"
    by (metis a1' a2' a4 dIds preconditionI step1 step2 usePrecondition)
qed  


lemma precondition_alocal:
"precondition (s, ALocal) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = LocalStep ls')"
apply (auto simp add: precondition_def intro: step.intros elim: step_elims)
done

lemma precondition_newid:
"precondition (s, ANewId uid) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = NewId ls' \<and> uid \<notin> generatedIds C)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_beginAtomic:
"precondition (s, ABeginAtomic tx) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = BeginAtomic ls' \<and> currentTransaction C s = None \<and> transactionStatus C tx = None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_endAtomic:
"precondition (s, AEndAtomic) C = (\<exists>ls f ls'. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = EndAtomic ls' \<and> currentTransaction C s \<noteq> None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_invoc:
"precondition (s, AInvoc procName args) C = (\<exists>initialState impl. invocationOp C s = None \<and> localState C s = None \<and> procedure (prog C) procName args \<triangleq> (initialState, impl) \<and> uniqueIdsInList args \<subseteq> knownIds C)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_dbop:
"precondition (s, ADbOp c operation args res) C = (\<exists>ls f ls' t vis. calls C c = None \<and> localState C s \<triangleq> ls 
    \<and> currentProc C s \<triangleq> f \<and> f ls = DbOperation operation args ls' \<and> currentTransaction C s \<triangleq> t \<and> querySpec (prog C) operation args (getContext C s) res \<and> visibleCalls C s \<triangleq> vis)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_pull:
"precondition (s, APull txs) C = (\<exists>ls vis. localState C s \<triangleq> ls \<and> currentTransaction C s = None \<and> visibleCalls C s \<triangleq> vis \<and> (txs \<subseteq> commitedTransactions C))"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done


lemma precondition_return:
"precondition (s, AReturn res) C = (\<exists>ls f. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = Return res \<and> currentTransaction C s = None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_fail:
"precondition (s, AFail) C = True" (* failures occur anywhere and anytime ;) *)
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_invcheck:
"precondition (s, AInvcheck b) C = (\<exists>vis. currentTransaction C s = None \<and> visibleCalls C s \<triangleq> vis \<and> invariant (prog C) (invContext C s) = b)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

(*
  | AInvcheck bool
*)



lemma step_existsH:
"\<lbrakk>precondition a A; \<And>B. A ~~ a \<leadsto> B \<Longrightarrow> P B \<rbrakk> \<Longrightarrow> \<exists>B. (A ~~ a \<leadsto> B) \<and> P B"
  using usePrecondition by blast

lemma unchanged_in_step:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and exec: "A ~~ (sa, a) \<leadsto> B"
shows
    "localState A sb = localState B sb"
 and "currentProc A sb = currentProc B sb"
 and "currentTransaction A sb = currentTransaction B sb"
 and "visibleCalls A sb = visibleCalls B sb"
 and "invocationOp A sb = invocationOp B sb"
 and "invocationRes A sb = invocationRes B sb"
apply (case_tac a)
using exec apply (auto simp add: differentSessions[symmetric] elim!: step_elims)
done

lemma unchangedInTransaction_knownIds:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
shows "knownIds A = knownIds B"
apply (case_tac a)
using exec apply (auto simp add: differentSessions[symmetric] elim!: step_elims)
  by (simp add: aIsInTransaction)

lemmas unchangedInTransaction = unchanged_in_step unchangedInTransaction_knownIds

lemma getContext_happensBefore:
"getContext (A\<lparr>happensBefore := hb\<rparr>) s = (
    case visibleCalls A s of 
      None \<Rightarrow> emptyOperationContext 
    | Some vis \<Rightarrow> \<lparr>calls = calls A |` vis, happensBefore = hb |r vis\<rparr>)"
apply (auto simp add: getContextH_def split: option.splits)
done

-- "getContext is not changed by actions in other transactions"
lemma unchangedInTransaction_getContext:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
shows
    "getContext A sb = getContext B sb"
proof (cases a)
  case ALocal
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ANewId x2)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ABeginAtomic x3)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AEndAtomic
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ADbOp callId operation args res)
  from this
  obtain ls f ls' vis 
    where 1: "localState A sa \<triangleq> ls"
      and 2: "currentProc A sa \<triangleq> f"
      and 3: "f ls = DbOperation operation args ls'"
      and 4: "querySpec (prog A) operation args (getContext A sa) res"
      and 5: "visibleCalls A sa \<triangleq> vis"
      and 6: "B = A\<lparr>localState := localState A(sa \<mapsto> ls' res), calls := calls A(callId \<mapsto> Call operation args res), callOrigin := callOrigin A(callId \<mapsto> tx), visibleCalls := visibleCalls A(sa \<mapsto> {callId} \<union> vis),
                happensBefore := happensBefore A \<union> vis \<times> {callId}\<rparr>"
    apply atomize_elim
    using exec apply (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
    done
  have case1: "getContext B sb = getContext A sb" if "visibleCalls A sb = None"
    apply (auto simp add: that getContextH_def split: option.splits)
    using aIsInTransaction differentSessions exec that unchangedInTransaction(4) by fastforce+
    
  have case2: "getContext B sb = getContext A sb" if visi_def[simp]: "visibleCalls A sb \<triangleq> visi" for visi
  proof -
    from visi_def
    have [simp]: "visibleCalls B sb \<triangleq> visi"
      using aIsInTransaction differentSessions exec unchangedInTransaction(4) by fastforce
      
    hence "visi \<subseteq> dom (calls A)"  
      using visibleCalls_inv  using visi_def by blast 
    show "getContext B sb = getContext A sb"
      apply (simp add:  getContextH_def split: option.splits)
      proof
        have "(calls B |` visi) c = (calls A |` visi) c" for c
          apply (auto simp add: restrict_map_def 6)
          by (smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD domIff exec step_elim_ADbOp)
        thus "calls B |` visi = calls A |` visi" ..
      next
        show "happensBefore B |r visi = happensBefore A |r visi"
          apply (auto simp add: restrict_relation_def 6)
          by (smt ADbOp \<open>visi \<subseteq> dom (calls A)\<close> contra_subsetD domIff exec step_elim_ADbOp)
      qed    
    qed 
  from case1 case2 show ?thesis by fastforce 
next
  case (APull x6)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvoc x71 x72)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AReturn x8)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AFail
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvcheck x10)
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
qed




-- "invcontext is not changed by actions in other transactions"
lemma unchangedInTransaction_getInvContext:
assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and aIsInInvoc: "localState A sa \<triangleq> lsa"
    and txUncommited[simp]: "transactionStatus A tx \<triangleq> Uncommited" 
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    and origin_inv: "dom (callOrigin A) = dom (calls A)"
shows
    "invContext A sb = invContext B sb"
proof (cases a)
  case ALocal
  then show ?thesis using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ANewId x2)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (ABeginAtomic x3)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AEndAtomic
  then show ?thesis
    using aIsNotCommit by blast  
next
  case (ADbOp callId operation args res)
  with exec obtain ls f ls' vis
       where 1: "a = ADbOp callId operation args res"
         and B_def: "B = A\<lparr>localState := localState A(sa \<mapsto> ls' res), 
                calls := calls A(callId \<mapsto> Call operation args res), callOrigin := callOrigin A(callId \<mapsto> tx), visibleCalls := visibleCalls A(sa \<mapsto> {callId} \<union> vis),
                happensBefore := happensBefore A \<union> vis \<times> {callId}\<rparr>"
         and 3: "localState A sa \<triangleq> ls"
         and 4: "currentProc A sa \<triangleq> f"
         and 5: "f ls = DbOperation operation args ls'"
         and 6: "querySpec (prog A) operation args (getContext A sa) res"
         and 7: "visibleCalls A sa \<triangleq> vis"
         and 8: "calls A callId = None"
         apply atomize_elim
        using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
  have commitedSame: "commitedCalls B = commitedCalls A"        
    apply (auto simp add: commitedCallsH_def  B_def)
    using "8" origin_inv by auto
  
  have commitedCallsSame: "\<And>x. x \<in> commitedCalls A \<Longrightarrow> calls A x = calls B x"
    apply (auto simp add: B_def)
    using "8" commitedCallsH_def origin_inv
    by (smt domI domIff mem_Collect_eq) 
  
  have [simp]: "callId \<notin> commitedCalls A"
    by (smt "8" domIff commitedCallsH_def domI mem_Collect_eq origin_inv) 
    
        
  show ?thesis 
    proof (rule invariantContext_eqI)
      show "i_calls (invContext A sb) = i_calls (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        done
      show "i_happensBefore (invContext A sb) = i_happensBefore (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: restrict_relation_def B_def)
        done
        
      show "i_visibleCalls (invContext A sb) = i_visibleCalls (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def differentSessions[symmetric] split: if_splits option.splits)
        done
      show "i_callOrigin (invContext A sb) = i_callOrigin (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
        
      show "i_knownIds (invContext A sb) = i_knownIds (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
      show "i_invocationOp (invContext A sb) = i_invocationOp (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
      show "i_invocationRes (invContext A sb) = i_invocationRes (invContext B sb)"
        apply (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def)
        apply (auto simp add: B_def)
        done
    qed
    
  
next
  case (APull x6)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvoc x71 x72)
  then show ?thesis  using exec 
    by (auto simp add: aIsInTransaction aIsInInvoc differentSessions[symmetric] elim!: step_elims split: option.splits)
    
next
  case (AReturn x8)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case AFail
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
next
  case (AInvcheck x10)
  then show ?thesis  using exec by (auto simp add: aIsInTransaction differentSessions[symmetric] elim!: step_elims split: option.splits)
qed


lemma generatedIds_mono:
"\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> generatedIds A \<subseteq> generatedIds B"
apply (erule step.cases, auto)
done

lemma generatedIds_mono2:
"\<lbrakk>x\<in>generatedIds A; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> x\<in>generatedIds B"
  using generatedIds_mono by blast


lemma transactionStatus_mono:
"\<lbrakk>transactionStatus B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> transactionStatus A tx = None"
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma transactionStatus_mono2:
"\<lbrakk>transactionStatus B tx \<triangleq> Commited; A ~~ a \<leadsto> B; snd a\<noteq>AEndAtomic\<rbrakk> \<Longrightarrow> transactionStatus A tx \<triangleq> Commited"
apply (erule step.cases)
apply (auto split: if_splits)
done


lemma calls_mono:
"\<lbrakk>calls B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> calls A tx = None"
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma prog_inv:
"\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> prog B = prog A"
apply (erule step.cases)
apply (auto split: if_splits)
done




lemma commitedCalls_unchanged_callOrigin[simp]:
assumes a1: "ts t \<triangleq> Uncommited"
    and a2: "co c = None"
shows "commitedCallsH (co(c \<mapsto> t)) ts = commitedCallsH co ts"
using a1 a2 by (auto simp add: commitedCallsH_def)

  
lemma commutativePreservesPrecondition:
assumes preconditionHolds: "precondition (sb,b) B"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommited: "transactionStatus A tx \<triangleq> Uncommited"
    and aIsInLocal: "localState A sa \<triangleq> lsa"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
shows "precondition (sb,b) A"
proof -
  
  have origin_inv: "dom (callOrigin A) = dom (calls A)"
    by (simp add: wellFormed wellFormed_callOrigin_dom)
  
  have visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    by (simp add: wellFormed wellFormed_visibleCallsSubsetCalls_h(2))
  

show ?thesis
proof (cases b)
  case ALocal
  show ?thesis using precondition_alocal unchangedInTransaction
    by (metis ALocal aIsInTransaction differentSessions exec preconditionHolds) 
    
next
  case (ANewId x2)
  with preconditionHolds
  obtain ls f ls' 
    where 1: "localState B sb \<triangleq> ls" 
      and 2: "currentProc B sb \<triangleq> f" 
      and 3: "x2 \<notin> generatedIds B" 
      and 4: "f ls = NewId ls'"
    by (auto simp add: precondition_newid)
  have 5: "x2 \<notin> generatedIds A"
    using 3 exec generatedIds_mono2 by blast
  thus ?thesis
    by (metis "1" "2" "4" ANewId aIsInTransaction differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
next
  case (ABeginAtomic tx)
  with preconditionHolds obtain ls f ls' 
      where 1: "localState B sb \<triangleq> ls"
        and 2: "currentProc B sb \<triangleq> f"
        and 3: "f ls = BeginAtomic ls'"
        and 4: "currentTransaction B sb = None"
        and 5: "transactionStatus B tx = None"
    by (auto simp add: precondition_beginAtomic)
  moreover have "transactionStatus A tx = None" using transactionStatus_mono 5 exec by blast 
  ultimately show ?thesis using unchangedInTransaction
    by (metis ABeginAtomic aIsInTransaction differentSessions exec precondition_beginAtomic) 
next
  case AEndAtomic
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3))
next
  case (ADbOp callId operation args res)
  with preconditionHolds obtain ls f ls' vis t 
      where 1: "calls B callId = None"
        and 2: "localState B sb \<triangleq> ls"
        and 3: "currentProc B sb \<triangleq> f"
        and 4: "f ls = DbOperation operation args ls'"
        and 5: "currentTransaction B sb \<triangleq> t"
        and 6: "querySpec (prog B) operation args (getContext B sb) res"
        and 7: "visibleCalls B sb \<triangleq> vis"
    by (auto simp add: precondition_dbop)
  moreover have "calls A callId = None"
    using "1" calls_mono exec by blast   
  moreover have "prog B = prog A"
    using exec prog_inv by auto  
  moreover have "getContext B sb = getContext A sb"
    by (metis aIsInTransaction differentSessions exec unchangedInTransaction_getContext visibleCalls_inv) 
  ultimately show ?thesis  using unchangedInTransaction
    by (smt ADbOp aIsInTransaction differentSessions exec precondition_dbop)
    
next
  case (APull txns) 
  with preconditionHolds obtain ls vis
      where 1: "localState B sb \<triangleq> ls"
      and 2: "currentTransaction B sb = None"
      and 3: "visibleCalls B sb \<triangleq> vis"
      and 4: "\<forall>txn\<in>txns. transactionStatus B txn \<triangleq> Commited"
    by (auto simp add: precondition_pull)
  
  then show ?thesis
    by (metis (mono_tags, lifting) APull aIsInTransaction aIsNotCommit differentSessions exec mem_Collect_eq precondition_pull snd_conv subsetI transactionStatus_mono2 unchangedInTransaction(1) unchangedInTransaction(3) unchangedInTransaction(4))
next
  case (AInvoc procName args)
  with preconditionHolds obtain initialState impl
      where "invocationOp B sb = None"
      and "localState B sb = None"
      and "procedure (prog B) procName args \<triangleq> (initialState, impl)"
      and "uniqueIdsInList args \<subseteq> knownIds B"
    by (auto simp add: precondition_invoc)
  moreover have "invocationOp A sb = None"
    using aIsInTransaction calculation(1) differentSessions exec unchangedInTransaction(5) by fastforce
    
  ultimately show ?thesis using unchangedInTransaction
    by (metis (mono_tags, lifting) AInvoc aIsInTransaction differentSessions exec precondition_invoc prog_inv) 
next
  case (AReturn x8)
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case AFail
  then show ?thesis
    using precondition_fail by blast 
next
  case (AInvcheck b)
  with preconditionHolds obtain vis 
     where 1: "currentTransaction B sb = None"
       and 2: "visibleCalls B sb \<triangleq> vis"
       and 3: "invariant (prog B) (invContext B sb) = b"
    by (auto simp add: precondition_invcheck)
  
    
  moreover have "invContext A sb = invContext B sb"
    using unchangedInTransaction_getInvContext aIsInLocal aIsInTransaction aIsNotCommit differentSessions exec origin_inv txIsUncommited visibleCalls_inv by blast 

    ultimately show ?thesis  using unchangedInTransaction
      by (smt AInvcheck aIsInTransaction differentSessions exec precondition_invcheck prog_inv)
    
qed
qed

 (*
\<And>ls f ls' t vis visa.
       a = AInvcheck True \<Longrightarrow>
       currentTransaction S sb = None \<Longrightarrow>
       visibleCalls S sb \<triangleq> visa \<Longrightarrow>
       localState S sa \<triangleq> ls \<Longrightarrow>
       currentProc S sa \<triangleq> f \<Longrightarrow>
       f ls = DbOperation operation args ls' \<Longrightarrow>
       currentTransaction S sa \<triangleq> t \<Longrightarrow>
       querySpec (prog S) operation args (getContext S sa) res \<Longrightarrow>
       visibleCalls S sa \<triangleq> vis \<Longrightarrow>
       x10 \<Longrightarrow> invariant (prog S)
                (invContext
                  (S\<lparr>
  localState := localState S(sa \<mapsto> ls' res), 
    calls := calls S(c \<mapsto> Call operation args res), 
  
callOrigin := callOrigin S(c \<mapsto> t),
visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis), 
happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
                  sb) \<Longrightarrow>
               calls S c = None \<Longrightarrow> invariant (prog S) (invContext S sb)


*)
  
lemma invContext_unchanged_happensBefore[simp]:
assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommited"
shows "invContextH co ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs s
    = invContextH co ts hbOld cs ki io ir vcs s"
apply (simp add: invContextH_def)
using assms apply (auto simp add: restrict_relation_def commitedCallsH_def)
done  

lemma invContext_unchanged_happensBefore2[simp]:
assumes "co c = None"
shows "invContextH co ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs s
    = invContextH co ts hbOld cs ki io ir vcs s"
apply (simp add: invContextH_def)
using assms apply (auto simp add: restrict_relation_def commitedCallsH_def)
done  

lemma commitedCalls_uncommitedNotIn:
assumes "callOrigin S c \<triangleq> t"
   and "transactionStatus S t \<triangleq> Uncommited"
shows  "c \<notin> commitedCalls S"
using assms by (auto simp add: commitedCallsH_def)
    
   
find_consts "'a \<Rightarrow> 'a option \<Rightarrow> 'a"

lemma invContext_changeVisibleCalls[simp]:
shows "i_visibleCalls (invContextH co ts hbOld cs ki io ir vcs s)
     = vcs orElse {}"
by (auto simp add: invContextH_def split: option.splits)  


lemma wellFormed_commitedCallsExist:
assumes a1: "calls S c = None"
    and a2: "state_wellFormed S"
shows "c \<notin> commitedCalls S"
using a1 a2
  by (smt commitedCallsH_def domIff mem_Collect_eq option.simps(3) wellFormed_callOrigin_dom) 
    
lemma noOrigin_notCommited:
  "callOrigin S c = None \<Longrightarrow> c \<notin> commitedCalls S"  
by (auto simp add: commitedCallsH_def)
  

  
    
lemma commutative_ALocal_other[simp]:
assumes a1: "sa \<noteq> sb"
shows "commutativeS S (sa, ALocal) (sb, a)"
apply (case_tac a)
by (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist)


lemma commutative_other_ALocal[simp]:
assumes a1: "sa \<noteq> sb"
shows "commutativeS S (sa, a) (sb, ALocal)"
  using assms commutativeS_switchArgs by force
  
lemma commitedCallsH_notin[simp]:
assumes "co c = None"
shows "c \<notin> commitedCallsH co ts"
  by (simp add: assms commitedCallsH_def)
                                                     
lemma commitedCallsH_in:
shows "(c \<in> commitedCallsH co ts) \<longleftrightarrow> (case co c of None \<Rightarrow> False | Some t \<Rightarrow> ts t \<triangleq> Commited) "
  by (auto simp add: commitedCallsH_def split: option.splits)
    
lemma invContextH_update_callOrigin[simp]:
assumes "co c = None" and "ts t \<triangleq> Uncommited"
shows "invContextH (co(c \<mapsto> t)) ts hb cs ki io ir vis s =
       invContextH co ts hb cs ki io ir vis s"
using assms by (auto simp add: invContextH_def)

lemma invContextH_update_calls[simp]:
assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommited"
shows "invContextH co ts hb (cs(c \<mapsto> newCall)) ki io ir vis s =
       invContextH co ts hb cs ki io ir vis s"
using assms by (auto simp add: invContextH_def commitedCallsH_in)

lemma commitedCallsH_update_uncommited[simp]:
assumes "ts t = None"
shows "commitedCallsH co (ts(t \<mapsto> Uncommited))
     = commitedCallsH co ts"
using assms apply (auto simp add: commitedCallsH_def)
  by force


lemma invContextH_update_txstatus[simp]:
assumes "ts t = None"
shows "invContextH co (ts(t\<mapsto>Uncommited)) hb cs ki io ir vis s =
       invContextH co ts hb cs ki io ir vis s"
using assms by (auto simp add: invContextH_def)

lemma test:
assumes a7: "currentTransaction S sa \<triangleq> t"
assumes a10: "state_wellFormed S"
assumes a11: "sb\<noteq>sa"
assumes a12: "calls S c = None"
shows "invContext
           (S\<lparr>localState := localState S(sa \<mapsto> ls' res), calls := calls S(c \<mapsto> Call operation args res),
                callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis),
                happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
           sb
  = invContext (S::state) sb"
  using assms by auto

lemma getContextH_visUpdate[simp]:
assumes "c \<notin> vis"
shows "getContextH cs (hb \<union> v \<times> {c}) (Some vis)
     = getContextH cs hb (Some vis)"
using assms by (auto simp add: getContextH_def restrict_relation_def split: option.splits)

lemma getContextH_callsUpdate[simp]:
assumes "c \<notin> vis"
shows "getContextH (cs(c\<mapsto>newCall)) hb (Some vis)
     = getContextH cs hb (Some vis)"
using assms by (auto simp add: getContextH_def split: option.splits)

lemma wellFormed_visibleCallsSubsetCalls2: "\<lbrakk> 
      visibleCalls S sb \<triangleq> visa; 
      calls S c = None;
      state_wellFormed S
    \<rbrakk> \<Longrightarrow> c\<notin>visa"
by (meson domIff set_mp wellFormed_visibleCallsSubsetCalls_h(2))

lemma callsInTransactionH_originUpdate_unchanged[simp]:
assumes a1: "currentTransaction S sa \<triangleq> t"
    and a2: "state_wellFormed S"
    and a3: "calls S c = None"
    and a4: "txns \<subseteq> commitedTransactions S"
shows "callsInTransactionH (callOrigin S(c \<mapsto> t)) txns
           = callsInTransactionH (callOrigin S) txns"
  apply (auto simp add: callsInTransactionH_def)
  using a1 a2 a4 apply auto[1]
  by (simp add: a2 a3)
  

lemma callsInTransaction_down_hb_unchanged[simp]:"
\<lbrakk> calls S c = None;
 state_wellFormed S\<rbrakk>
 \<Longrightarrow> callsInTransaction S txns \<down> (happensBefore S \<union> visa \<times> {c})
   = callsInTransaction S txns \<down> (happensBefore S)"
by (auto simp add: downwardsClosure_def callsInTransactionH_def)

lemma commutative_Dbop_other[simp]:
assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
shows "commutativeS S (sa, ADbOp c operation args res) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis by simp
next
  case (ANewId x2)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case (ABeginAtomic x3)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case AEndAtomic
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case AFail
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront  a1[symmetric]  step_simps fun_upd_twist)
next
  case (AInvoc p a)
  show ?thesis 
    proof (induct rule: show_commutativeS_pres)
      case (preBfront s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_invoc step_simps split: if_splits)
    next
      case (preAfront s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_dbop step_simps)
    next
      case (preAback s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_dbop step_simps)
    next
      case (preBback s1)
      then show ?case 
        by (auto simp add: AInvoc precondition_invoc step_simps)
    next
      case (commute s1 s2 s1' s2')
      then show ?case 
        by (auto simp add: AInvoc commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
    qed
    
next
  case (AReturn x8)
  then show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    by (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
    
next
  case (AInvcheck x10)
  with a2 show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    by (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist)
next
  case (ADbOp c' operation' args' res')
  with a2 show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres2)
    apply (auto simp add: precondition_dbop)
    by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits, auto simp add: state_ext)
next
  case (APull txns)
  then show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres2)
    apply (auto simp add: precondition_dbop precondition_pull)
    apply (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)[12]
    proof -
      fix s1 s2 s1' s2'
      assume b1: "a = APull txns"
         and step1: "S ~~ (sa, ADbOp c operation args res) \<leadsto> s1"
         and step2: "s1 ~~ (sb, APull txns) \<leadsto> s2"
         and step3: "S ~~ (sb, APull txns) \<leadsto> s1'"
         and step4: "s1' ~~ (sa, ADbOp c operation args res) \<leadsto> s2'"
      show "s2 = s2'"
    
      proof (subst state_ext; intro conjI)
          
        show "visibleCalls s2 = visibleCalls s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)

        show "calls s2 = calls s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "happensBefore s2 = happensBefore s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "prog s2 = prog s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "localState s2 = localState s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "currentProc s2 = currentProc s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "currentTransaction s2 = currentTransaction s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "transactionStatus s2 = transactionStatus s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "callOrigin s2 = callOrigin s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "generatedIds s2 = generatedIds s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "knownIds s2 = knownIds s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "invocationOp s2 = invocationOp s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
        show "invocationRes s2 = invocationRes s2'"
          using a2 step1 step2 step3 step4  by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits)
    qed
  qed
qed

lemma commutative_newId_other[simp]:
assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
shows "commutativeS S (sa, ANewId uid) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis by simp
next
  case (ANewId x2)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (ABeginAtomic x3)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case AEndAtomic
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_Dbop_other by presburger
next
  case (APull x6)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (AInvoc x71 x72)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (AReturn x8)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case AFail
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (AInvcheck x10)
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
qed

lemma commutative_fail_other[simp]:
assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
shows "commutativeS S (sa, AFail) (sb, a)"
apply (case_tac a)
by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)

lemma wellFormed_invoc_notStarted:
assumes "state_wellFormed S"
  and "invocationOp S s = None"
shows "currentTransaction S s = None"  
  and "localState S s = None"
using assms apply (induct rule: wellFormed_induct)
apply (auto simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
apply (erule step.cases)
apply (auto split: if_splits)
done

lemma move_transaction:
assumes a_is_in_transaction: "currentTransaction S sa \<triangleq> t"
  and b_is_a_different_session[simp]: "sa \<noteq> sb"
  and not_endAtomic: "a \<noteq> AEndAtomic"
  and wf[simp]: "state_wellFormed S"
shows "(S ~~ [(sa,a),(sb,b)] \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,a)] \<leadsto>* T)"
proof (rule useCommutativeS)   
  show "commutativeS S (sa, a) (sb, b)"
    proof (cases a)
      case ALocal
      then show ?thesis by simp
    next
      case (ANewId x2)
      then show ?thesis by simp 
    next
      case (ABeginAtomic x3)
      then show ?thesis  by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction)
    next
      case AEndAtomic
      then show ?thesis using not_endAtomic by simp
    next
      case (ADbOp x51 x52 x53 x54)
      then show ?thesis  by simp
    next
      case (APull x6)
      then show ?thesis   by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction)
    next
      case (AInvoc x71 x72)
      then show ?thesis 
        (*apply (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction wellFormed_invoc_notStarted)*)
        apply (auto simp add: commutativeS_def steps_appendFront)
        apply (metis a_is_in_transaction local.wf option.distinct(1) preconditionI precondition_invoc wellFormed_invoc_notStarted(1))
        by (metis a_is_in_transaction b_is_a_different_session local.wf option.distinct(1) preconditionI precondition_invoc unchangedInTransaction(5) wellFormed_invoc_notStarted(1))
    next
      case (AReturn x8)
      then show ?thesis   by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction)
    next
      case AFail
      then show ?thesis  by simp
    next
      case (AInvcheck x10)
      then show ?thesis   by (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction)
    qed
qed

lemma move_transaction2:
assumes a_is_in_transaction: "currentTransaction S (fst a) \<triangleq> t"
  and b_is_a_different_session[simp]: "fst a \<noteq> fst b"
  and not_endAtomic: "snd a \<noteq> AEndAtomic"
  and wf[simp]: "state_wellFormed S"
shows "(S ~~ a#b#xs \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)"
proof -
  have "(S ~~ a#b#xs \<leadsto>* T) \<longleftrightarrow> (\<exists>S'. (S ~~ [a,b] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    using steps_appendFront by auto
  moreover have "... \<longleftrightarrow> (\<exists>S'. (S ~~ [b,a] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    by (metis a_is_in_transaction b_is_a_different_session local.wf move_transaction not_endAtomic prod.collapse)
  moreover have "... \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)" 
    using steps_appendFront by auto
  ultimately show ?thesis
    by blast 
qed   

lemma commutative_beginAtomic_other[simp]:
assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
shows "commutativeS S (sa, ABeginAtomic t) (sb, a)"
proof (cases a)
  case ALocal
  then show ?thesis
    by simp 
next
  case (ANewId x2)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_newId_other by presburger
next
  case (ABeginAtomic x3)
  then show ?thesis 
   by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case AEndAtomic
  then show ?thesis 
    by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute split: if_splits)
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_Dbop_other by presburger 
next
  case (APull x6)
  then show ?thesis 
  by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute,
    auto, smt mem_Collect_eq option.inject subsetCE transactionStatus.distinct(1))
next
  case (AInvoc x71 x72)
  then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute split: if_splits)
next
  case (AReturn x8)
  then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute split: if_splits)
next
  case AFail
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_fail_other by presburger 
next
  case (AInvcheck x10)
  then show ?thesis 
    by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute split: if_splits)
qed



lemma move_outside_transaction:
assumes b_is_a_different_session[simp]: "sa \<noteq> sb"
  and wf[simp]: "state_wellFormed S"
shows "(S ~~ [(sa,ABeginAtomic t),(sb,b)] \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,ABeginAtomic t)] \<leadsto>* T)"
  by (simp add: useCommutativeS)
  
 


(* todo and now move everything out of transactions ... *)

lemma show_programCorrect:
assumes "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s \<rbrakk> \<Longrightarrow> traceCorrect program trace"
shows "programCorrect program"
  by (simp add: assms programCorrect_def)

lemma currentTransaction_unchangedInternalSteps:
assumes "S ~~ tr \<leadsto>* S'"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AEndAtomic"
  and "\<And>a tx.  a \<in> set tr \<Longrightarrow> snd a \<noteq> ABeginAtomic tx"
shows "currentTransaction S' s = currentTransaction S s"  
using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by auto
next
  case (steps_step S tr S' a S'')
  then show ?case 
  proof (cases "snd a")
    case ALocal
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (ANewId x2)
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (ABeginAtomic x3)
    then show ?thesis using steps_step by auto 
  next
    case AEndAtomic
    then show ?thesis using steps_step by auto
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (APull x6)
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (AInvoc x71 x72)
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (AReturn x8)
    then show ?thesis using steps_step by (case_tac a, case_tac "currentTransaction S s", auto elim: step_elims)
  next
  case AFail
    then show ?thesis using steps_step by (case_tac a, case_tac "currentTransaction S s", auto elim: step_elims)
  next
    case (AInvcheck x10)
    then show ?thesis using steps_step by (case_tac a, case_tac "currentTransaction S s", auto elim: step_elims)
  qed
qed






lemma currentTransaction_unchangedInternalSteps2:
assumes "S ~~ tr \<leadsto>* S'"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AEndAtomic"
(*  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AFail"*)
  and "currentTransaction S s = Some t"  
  and wf: "state_wellFormed S"
shows "currentTransaction S' s = Some t"  and "a \<in> set tr \<Longrightarrow> a \<noteq> (s, ABeginAtomic tx)" 
using assms apply (induct arbitrary: a tx rule: steps.induct)  
 using currentTransaction_unchangedInternalSteps by (auto simp add: step_simps split: if_splits, fastforce+)


lemma currentTransaction_unchangedInternalSteps3:
assumes a1: "s_init ~~ (s, ABeginAtomic tx) # as \<leadsto>* S'"
  and a2: "\<And>st at.  (st, at) \<in> set as \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic"
  and wf: "state_wellFormed s_init"
shows "currentTransaction S' s \<triangleq> tx"
proof -
  from a1 
  obtain S where 1: "s_init ~~ (s, ABeginAtomic tx) \<leadsto> S" and 2: "S ~~ as \<leadsto>* S'"
    using steps_appendFront by blast
  from 2
  show "currentTransaction S' s \<triangleq> tx"
  proof (rule currentTransaction_unchangedInternalSteps2)
    from a2
    show "\<And>a. a \<in> set as \<Longrightarrow> snd a \<noteq> AEndAtomic"
      by auto    
    
    from 1
    show "currentTransaction S s \<triangleq> tx"
      by (auto simp add: step_simps)

    from wf 1
    show "state_wellFormed S"
      using state_wellFormed_combine steps_refl steps_step by blast
  qed
qed
  
  
lemma one_compaction_step:
assumes splitTrace: "tr = (s, ABeginAtomic tx) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx) # txa @ rest \<leadsto>* C)"
using splitTrace txaInTx xOutside proof (induct txa arbitrary: tr x rest rule: rev_induct)
  case Nil
  
  have "(s_init ~~ tr \<leadsto>* C) 
      = (s_init ~~ (s, ABeginAtomic tx) # x # rest \<leadsto>* C)" 
    using Nil by simp
  moreover have "... = (\<exists>S'. (s_init ~~ [(s, ABeginAtomic tx), x] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    by (auto simp add: steps_appendFront)
  moreover have "... = (\<exists>S'. (s_init ~~ [x, (s, ABeginAtomic tx)] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    by (metis Nil.prems(3) commutative_beginAtomic_other local.wf prod.collapse useCommutativeS)  
  moreover have "... = ( s_init ~~ x # (s, ABeginAtomic tx) # [] @ rest \<leadsto>* C)"
    by (auto simp add: steps_appendFront)
    
  ultimately show ?case by auto
next
  case (snoc a as)
  
  have "(s_init ~~ x # (s, ABeginAtomic tx) # (as @ [a]) @ rest \<leadsto>* C)
      = (s_init ~~ x # (s, ABeginAtomic tx) # as @ ([a] @ rest) \<leadsto>* C)"
      by simp
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx) # as @ [x] @ ([a] @ rest) \<leadsto>* C)"
    using snoc.hyps  by (metis append_Cons append_Nil butlast_snoc in_set_butlastD snoc.prems(2) snoc.prems(3))
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx) # as @ x # a # rest \<leadsto>* C)"
    by simp
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx) # as \<leadsto>* S') \<and> (S' ~~  x # a # rest \<leadsto>* C))"
    by (auto simp add:  steps_append steps_appendFront)
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx) # as \<leadsto>* S') \<and> (S' ~~  a # x # rest \<leadsto>* C))" (is ?eq1)
    proof -
      have "(S' ~~ x # a # rest \<leadsto>* C)
        \<longleftrightarrow> (S' ~~ a # x # rest \<leadsto>* C)" 
        if "(s_init ~~ (s, ABeginAtomic tx) # as \<leadsto>* S')"
        for S'
        proof (rule move_transaction2[symmetric])
          have [simp]: "fst a = s" using snoc
            by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1) 
          show "currentTransaction S' (fst a) \<triangleq> tx" 
            using currentTransaction_unchangedInternalSteps3
            by (metis \<open>fst a = s\<close> butlast_snoc in_set_butlastD local.wf snoc.prems(2) that) 
          show "fst a \<noteq> fst x"
            using snoc
            by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing) 
          show "snd a \<noteq> AEndAtomic"
            using snoc 
            by (metis list.set_intros(1) rotate1.simps(2) set_rotate1 surjective_pairing)  
          show "state_wellFormed S'"
            using wf that state_wellFormed_combine by blast 
        qed
      thus ?eq1 by blast
    qed
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx) # as @ a # x # rest \<leadsto>* C)"  
    by (auto simp add: steps_append steps_appendFront)
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx) # (as @ [a]) @ x # rest \<leadsto>* C)"  
    by auto
  ultimately show ?case
    using snoc.prems(1) by blast 
qed    
 

lemma one_compaction_step2:
assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ trStart @ x # (s, ABeginAtomic tx) # txa @ rest \<leadsto>* C)"
  by (smt local.wf one_compaction_step splitTrace state_wellFormed_combine steps_append txaInTx xOutside)

lemma one_compaction_step3:
assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx) # txa @ x # rest" 
    and splitTrace': "tr' = trStart @ x # (s, ABeginAtomic tx) # txa @ rest"
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr' \<leadsto>* C)"
  using local.wf one_compaction_step2 splitTrace splitTrace' txaInTx xOutside by blast

definition indexInOtherTransaction :: "trace \<Rightarrow> txid \<Rightarrow> nat \<Rightarrow> bool" where
"indexInOtherTransaction tr tx k \<equiv> 
  \<exists>i s. 
      k<length tr 
    \<and> i<k 
    \<and> tr!i = (s, ABeginAtomic tx)  
    \<and> fst (tr!k) \<noteq> s
    \<and> \<not>(\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"
  
definition transactionIsPacked :: "trace \<Rightarrow> txid \<Rightarrow> bool" where
"transactionIsPacked tr tx \<equiv> 
  \<forall>k. \<not>indexInOtherTransaction tr tx k"  
  
definition transactionIsPackedMeasure :: "trace \<Rightarrow> txid \<Rightarrow> nat" where
"transactionIsPackedMeasure tr tx \<equiv>
  card {k . indexInOtherTransaction tr tx k}"  
    
lemma indexInOtherTransaction_finite[simp]: "finite {k. indexInOtherTransaction tr tx k}"
by (auto simp add: indexInOtherTransaction_def)

lemma transactionIsPackedMeasure_zero_iff: 
  "transactionIsPackedMeasure tr tx = 0 \<longleftrightarrow>  transactionIsPacked tr tx" 
by (auto simp add: transactionIsPackedMeasure_def transactionIsPacked_def)

(* this is an alternative definition, which might be easier to work with in some cases *)
definition transactionIsPackedAlt :: "trace \<Rightarrow> txid \<Rightarrow> bool" where
"transactionIsPackedAlt tr tx \<equiv> 
  if \<exists>i s. i < length tr \<and> tr!i = (s, ABeginAtomic tx) then
    \<exists>i s end. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx)
        \<and> end > i  
        \<and> (end < length tr \<and> tr!end = (s, AEndAtomic) \<or> end = length tr)  
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> fst (tr!j) = s) 
  else
    True
  "  

lemma transactionIsPackedAlt_eq:
assumes uniqueTxs: "\<And>i j s s'. \<lbrakk>i<length tr; j<length tr; tr!i = (s, ABeginAtomic tx); tr!j = (s', ABeginAtomic tx)\<rbrakk> \<Longrightarrow> i = j"
shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
proof (auto simp add: transactionIsPackedAlt_def )
  fix i s ia sa
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx)"
     and a2: "ia < length tr"
     and a3: "tr ! ia = (sa, ABeginAtomic tx)"
     and a4: "\<forall>j. ia \<le> j \<and> j < length tr \<longrightarrow> fst (tr ! j) = sa"
  
  with uniqueTxs have [simp]: "ia = i"
    by blast   
  hence [simp]: "sa = s"
    using a1 a3 by auto  
  hence a4': "\<And>j. i \<le> j \<Longrightarrow> j < length tr \<Longrightarrow> fst (tr ! j) = s"  
    using a4 by auto
     
  show "transactionIsPacked tr tx"
  
  proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s')
    fix k i' s'
    assume b0: "k < length tr"
       and b1: "i' < k"
       and b2: "tr ! i' = (s', ABeginAtomic tx)"
       and b3: "\<forall>j>i'. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
    
    from uniqueTxs have [simp]: "i' = i"
      using a0 a1 b0 b1 b2 by auto 
      
    hence [simp]: "s' = s"
      using a1 b2 by auto
       
    show "fst (tr ! k) = s'"
      apply (simp, rule a4')
      using \<open>i' = i\<close> b1 less_imp_le_nat apply blast
      by (simp add: b0) 
  qed
next
  fix i s
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx)"
     and a2: "transactionIsPacked tr tx"
  
  from a2
  have a2': "fst (tr ! k) = s \<or> (\<exists>j<k. i < j \<and> tr ! j = (s, AEndAtomic))" 
    if "k<length tr" "i<k"
    for k
    apply (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
    using a1 that(1) that(2) by blast
    
    
     
  show "\<exists>i<length tr. \<exists>s. tr ! i = (s, ABeginAtomic tx) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"
  proof (rule_tac x=i in exI, (auto simp add: a0))
    show "\<exists>s. tr ! i = (s, ABeginAtomic tx) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"
    proof (rule_tac x=s in exI, safe)
      show "tr ! i = (s, ABeginAtomic tx)"
        by (simp add: a1) 
      define endPos where "endPos = (if \<exists>j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) then LEAST j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic) else length tr)"
      show "\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s) "
      proof (rule_tac x="endPos" in exI, (auto simp add: endPos_def))
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) < length tr"
          by (smt less_trans neqE not_less_Least)
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) \<noteq> length tr\<rbrakk> \<Longrightarrow> tr ! (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic)) = (s, AEndAtomic)"
          by (smt LeastI)
        show "\<And>j ja. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic); i \<le> ja; ja < (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic))\<rbrakk> \<Longrightarrow> fst (tr ! ja) = s"
          by (smt a1 a2' dual_order.strict_trans fst_conv neqE not_le not_less_Least)
        show "\<And>j. \<lbrakk>\<forall>j<length tr. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic); i \<le> j; j < length tr\<rbrakk> \<Longrightarrow> fst (tr ! j) = s"
          by (metis a1 a2' dual_order.strict_trans fst_conv le_eq_less_or_eq)
        show "\<And>j. \<lbrakk>i < j; j < length tr; tr ! j = (s, AEndAtomic)\<rbrakk> \<Longrightarrow> i < (LEAST j. i < j \<and> j < length tr \<and> tr ! j = (s, AEndAtomic))"
          by (metis (mono_tags, lifting) LeastI_ex)
        show "\<forall>j<length tr. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic) \<Longrightarrow> i < length tr"
          using a0 by blast  
      qed
    qed
  qed  
next
  show "\<forall>i<length tr. \<forall>s. tr ! i \<noteq> (s, ABeginAtomic tx) \<Longrightarrow> transactionIsPacked tr tx"
   by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
next
  fix i s ia sa ende
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx)"
     and a3: "tr ! ia = (sa, ABeginAtomic tx)"
     and a7: "ia < ende"
     and a4: "\<forall>j. ia \<le> j \<and> j < ende \<longrightarrow> fst (tr ! j) = sa"
     and a5: "ende < length tr"
     and a6: "tr ! ende = (sa, AEndAtomic)"
  
  have a2: "ia < length tr"
    using a5 a7 less_trans by blast
    
     
  with uniqueTxs have [simp]: "ia = i"
    using a0 a1 a3 by blast
    
  hence [simp]: "sa = s"
    using a1 a3 by auto     
  
  have a4': "fst (tr ! j) = s" if "i \<le> j" and "j < ende" for j
    by (auto simp add: that a4)  
    
    
  show "transactionIsPacked tr tx"
    proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s')
      fix k i' s'
      assume b0: "k < length tr"
         and b1: "i' < k"
         and b2: "tr ! i' = (s', ABeginAtomic tx)"
         and b3: "\<forall>j>i'. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
      
      have " i' < length tr"
        using b0 b1 order.strict_trans by blast 
      
         
      hence [simp]: "i' = i"
      using uniqueTxs b2 a1 a0 by blast 
        
      hence [simp]: "s' = s"
        using a1 b2 by auto
         
      have b3': "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic)"
        using b3 by simp      
      have "fst (tr ! k) = s"
        proof (cases "k < ende")
        case True
          show ?thesis
          proof (rule a4')
            show "i \<le> k"
              using \<open>i' = i\<close> b1 dual_order.strict_implies_order by blast 
            show "k < ende" using True .
          qed
        next case False
          hence "k \<ge> ende" by simp
          show ?thesis
          proof (cases "k = ende")
            case True
            then show ?thesis
              by (simp add: a6) 
          next
            case False
            hence "k > ende"
              by (simp add: \<open>ende \<le> k\<close> dual_order.strict_iff_order) 
            from b3' have "ende>i \<and> ende < k \<longrightarrow> tr ! ende \<noteq> (s, AEndAtomic)"
              by blast
            with `k > ende` have "tr ! ende \<noteq> (s, AEndAtomic)"
              using \<open>ia = i\<close> a7 by blast
              
            then show ?thesis
              by (simp add: a6) 
          qed
        qed      
    thus "fst (tr ! k) = s'" by simp
  qed
qed

  
  

find_theorems "finite _" "_ \<subseteq> _"

find_theorems "card _ = 0"
    
(* the set of transactions occurring in the trace *)    
definition traceTransactions :: "trace \<Rightarrow> txid set" where
"traceTransactions tr \<equiv> {tx | s tx . (s, ABeginAtomic tx) \<in> set tr}"
    
text {* between begin and end of a transaction there are no actions from other sessions  *}
definition transactionsArePacked :: "trace \<Rightarrow> bool" where
"transactionsArePacked tr \<equiv>
  \<forall>i k s t. 
      i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t)  
    \<and> fst (tr!k) \<noteq> s
    \<longrightarrow>  (\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

text {*
For termination proofs, we want to measure how far a trace is from being packed.
For this we take the sum over all actions in the trace and count in how many transactions
it appears.
*}


(* checks if sessions s is in a transaction at position i in trace tr *)
definition inTransaction :: "trace \<Rightarrow> nat \<Rightarrow> session \<Rightarrow> bool"  where 
"inTransaction tr i s \<equiv>
  \<exists>j. j<length tr \<and> j\<le>i \<and> (\<exists>t. tr!j = (s, ABeginAtomic t))
     \<and> (\<forall>k. j<k \<and> k < length tr \<and> k\<le>i \<longrightarrow> tr!k \<noteq> (s, AEndAtomic))
"

(* returns the set of all transactions, which are in a transaction at point i in the trace*)
definition sessionsInTransaction :: "trace \<Rightarrow> nat \<Rightarrow> session set"  where 
"sessionsInTransaction tr i \<equiv> {s. inTransaction tr i s}"

(* counts how many concurrent transactions are active *)
definition transactionsArePackedMeasure :: "trace \<Rightarrow> nat" where
"transactionsArePackedMeasure tr \<equiv> 
\<Sum>i\<in>{..<length tr}. card (sessionsInTransaction tr i - {fst (tr!i)})  "


lemma inTransactionEmpty[simp]: "\<not>inTransaction [] i s"
by (auto simp add: inTransaction_def)

lemma sessionsInTransactionEmpty[simp]: 
"sessionsInTransaction [] i = {}"
by (simp add: sessionsInTransaction_def)


lemma " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1), (s\<^sub>1, AEndAtomic)] 3 = {}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done


lemma " sessionsInTransaction [(s1, ABeginAtomic t\<^sub>1)] 1= {s1}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done

lemma " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1), (s\<^sub>1, AEndAtomic)] 1 = {}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done

(*
fun sessionsInTransactionRevAlt :: "trace \<Rightarrow> nat \<Rightarrow> session set"  where
  "sessionsInTransactionRevAlt [] i = {}"
| "sessionsInTransactionRevAlt ((s, ABeginAtomic t)#as) i = sessionsInTransactionRevAlt as (i-1) \<union> {s}"
| "sessionsInTransactionRevAlt as 0 = {}"
| "sessionsInTransactionRevAlt ((s, AEndAtomic)#as) i = sessionsInTransactionRevAlt as (i-1) - {s}"
| "sessionsInTransactionRevAlt (a#as) i = sessionsInTransactionRevAlt as (i-1)"

lemma "sessionsInTransactionRevAlt tr i = sessionsInTransaction (rev tr) i"
apply (induct tr i rule: sessionsInTransactionRevAlt.induct)
apply auto[1]
apply auto[1]
*)


lemma sessionsInTransaction_append[simp]:
"i<length xs \<Longrightarrow> sessionsInTransaction (xs@ys) i = sessionsInTransaction xs i"
by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def)

lemma sessionsInTransactionEmptySnoc: 
"sessionsInTransaction (tr@[a]) i = (
if i\<ge>length tr then
  if \<exists>t. snd a = ABeginAtomic t then
       sessionsInTransaction tr (length tr - 1) \<union> {fst a}
  else if snd a = AEndAtomic then
       sessionsInTransaction tr (length tr - 1) - {fst a}
  else 
       sessionsInTransaction tr (length tr - 1)
else 
  sessionsInTransaction tr i)"
apply (case_tac a)
apply (auto split: if_splits)
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
  apply (metis Nitpick.size_list_simp(2) One_nat_def le_zero_eq length_tl less_Suc_eq_le less_imp_le_nat)
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
  apply (smt Nitpick.size_list_simp(2) One_nat_def le_Suc_eq length_tl lessI less_imp_le_nat less_trans nat_neq_iff zero_order(3))
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
done


lemma sessionsInTransaction_finite[simp]:
"finite (sessionsInTransaction tr i)"
apply (induct tr arbitrary: i rule: rev_induct)
apply (auto simp add: sessionsInTransactionEmptySnoc)
done


lemma subset_h1: "X \<subseteq> Y \<Longrightarrow> \<forall>x. x\<in>X \<longrightarrow> x\<in>Y"
  by blast

lemma transactionsArePackedMeasure_iff:
"transactionsArePacked tr \<longleftrightarrow> transactionsArePackedMeasure tr = 0"
apply (auto simp add: transactionsArePacked_def transactionsArePackedMeasure_def )
apply (auto simp add: sessionsInTransaction_def inTransaction_def)
  apply (smt dual_order.order_iff_strict fst_conv less_le_trans)
apply (drule_tac x=k in bspec)
apply auto
apply (drule subset_h1, clarsimp)
apply (drule_tac x=s in spec)
apply auto
by (metis antisym_conv2 less_imp_le_nat prod.collapse prod.inject)
(* TODO nicer proof*)

lemma not_packed_example:
assumes notPacked: "\<not>transactionsArePacked tr"
shows "\<exists>i k s t a s'. 
      tr ! k = (s', a) 
    \<and> i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t)  
    \<and> s' \<noteq> s
    \<and>  (\<forall>j. i < j \<and> j < k \<longrightarrow> tr!j \<noteq> (s, AEndAtomic))"
using assms apply (auto simp add: transactionsArePacked_def)
  by (metis prod.collapse)

lemma sumExists:
fixes f :: "'a \<Rightarrow> nat"
shows "0 < (\<Sum>x\<leftarrow>xs. f x) \<Longrightarrow> \<exists>i<length xs. f (xs!i) > 0"
by (induct xs, auto, auto)

lemma sumExists2:
fixes f :: "'a \<Rightarrow> nat"
assumes "finite S"
shows "0 < sum f S \<Longrightarrow> \<exists>x\<in>S. f x > 0"
using assms
by (meson not_less sum_nonpos) 

lemma not_packed_example2:
assumes notPacked: "transactionsArePackedMeasure tr > 0"
shows "\<exists>i s a.
    i<length tr
  \<and> tr!i = (s,a)
  \<and> sessionsInTransaction tr i - {s} \<noteq> {}" (is ?goal)
proof -
  from notPacked
  have "0 < (\<Sum>i<length tr. card (sessionsInTransaction tr i - {fst (tr ! i)}))"
    by (auto simp add: transactionsArePackedMeasure_def)
  from this 
  obtain i 
    where a: "i < length tr" 
      and b: "card (sessionsInTransaction tr i - {fst (tr ! i)}) > 0"
    by (meson lessThan_iff not_less sum_nonpos)
  
  from b 
  have "sessionsInTransaction tr i - {fst (tr!i)} \<noteq> {}"
    by fastforce
  
  thus ?thesis
    by (metis a prod.collapse)
qed  


lemma LeastI2:
"\<lbrakk>x = (LEAST x::nat. P x); P y\<rbrakk> \<Longrightarrow> P x"
  by (simp add: LeastI)
  
lemma append_eq_conv_conj2: 
  "(xs = ys @ zs) \<longleftrightarrow> (take (length ys) xs = ys \<and> (drop (length ys) xs) = zs)"  for xs ys zs
  by (metis append_eq_conv_conj)


lemma cons_eq_conv_conj: 
  "(xs = y # ys) \<longleftrightarrow> (xs \<noteq> [] \<and> y = hd xs \<and> ys = tl xs)"  for xs ys zs
  by force
  
lemma hd_drop_conv_nth2:  "\<lbrakk>i<length xs; a = hd (drop i xs)\<rbrakk> \<Longrightarrow> xs ! i = a"
  by (simp add: hd_drop_conv_nth)      
  
lemma eq_tl: "\<lbrakk>xs \<noteq> []; \<And>a as. xs = a#as \<Longrightarrow> drop i ys = as\<rbrakk> \<Longrightarrow> drop i ys = tl xs"
by (case_tac xs, auto)

lemma split_trace_min_i:
assumes min_i_def: "min_i = (LEAST i. i < length tr \<and> sessionsInTransaction tr i - {fst (tr ! i)} \<noteq> {})"
  and i1: "i < length tr"
  and i2: "sessionsInTransaction tr i - {fst (tr ! i)} \<noteq> {}"
shows "\<exists>trStart s tx txa rest.
       tr = trStart @ (s, ABeginAtomic tx) # txa @ tr!min_i # rest 
     \<and> length (trStart @ (s, ABeginAtomic tx) # txa) = min_i
     \<and> (\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)
     \<and> (s \<noteq> fst (tr!min_i))"
proof -
  from min_i_def
  have "min_i < length tr \<and> sessionsInTransaction tr min_i - {fst (tr ! min_i)} \<noteq> {}"
    apply (rule LeastI2)
    using i1 i2 by auto
  hence min_i1: "min_i < length tr" 
    and min_i2: "sessionsInTransaction tr min_i - {fst (tr ! min_i)} \<noteq> {}" by auto
  
  from min_i2
  obtain j s tx
    where j1: "j < length tr"
      and j2: "j \<le> min_i"
      and noEndAtomic: "\<forall>k. j < k \<and> k < length tr \<and> k \<le> min_i \<longrightarrow> tr ! k \<noteq> (s, AEndAtomic)"
      and tr_j: "tr ! j = (s, ABeginAtomic tx)"
      and otherS: "s \<noteq> fst (tr ! min_i)"
    by (auto simp add: sessionsInTransaction_def inTransaction_def)
    
   obtain trStart where trStart_def: 
      "trStart = take j tr" by simp
   
   obtain txa where txa_def:
      "txa = take (min_i - j - 1) (drop (Suc j) tr)" by simp
      
   obtain rest where rest_def:
      "rest = drop (Suc min_i) tr" by simp
      
   have min_simp1[simp]: "(min (length tr - Suc j) (min_i - Suc j)) = min_i - Suc j"
     using min_i1 by linarith
   
   have min_simp2[simp]: "min (length tr) j = j"
     using j1 by linarith 
    
   have arith_simp[simp]: "i < min_i - Suc j \<Longrightarrow> Suc j + i \<le> length tr" for i
     using min_simp1 by linarith
    
   have arith_simp2[simp]: "i < min_i - Suc j \<Longrightarrow> Suc (j + i) \<le> length tr" for i
     using arith_simp by auto
    
  
    
    
     
   have "tr = trStart @ (s, ABeginAtomic tx) # txa @ (tr!min_i) # rest"
     (* this proof should be easier ... *)
     apply (auto simp add: trStart_def txa_def rest_def append_eq_conv_conj2 cons_eq_conv_conj)
     using j1 apply auto[1]
     apply (simp add: hd_drop_conv_nth j1 less_imp_le_nat min.absorb2 tr_j)
     apply (auto simp add: append_eq_conv_conj)
     apply (simp add: drop_Suc j1 less_or_eq_imp_le min_absorb2 min_diff min_i1 tl_drop)
     apply (rule sym)
     apply (auto simp add: cons_eq_conv_conj)
     apply (metis Suc_leI j1 j2 le_diff_iff min_i1 not_less order.not_eq_order_implies_strict otherS prod.collapse prod.inject tr_j)
     apply (smt Suc_diff_Suc add_diff_cancel_left' drop_Suc fst_conv hd_drop_conv_nth j1 j2 leD le_Suc_ex le_diff_iff length_drop less_imp_le_nat min_i1 nth_drop order.not_eq_order_implies_strict otherS tr_j)
     apply (subst tl_drop)
     apply (case_tac j)
     apply auto
     apply (metis Suc_diff_Suc diff_zero drop_Suc fst_conv j2 le_less otherS tr_j)
     apply (case_tac nat)
     apply auto
     apply (metis (mono_tags, lifting) One_nat_def Suc_diff_Suc diff_zero drop_0 drop_Suc dual_order.order_iff_strict fst_conv j2 less_le_trans less_numeral_extra(1) otherS tr_j)
     by (smt Suc_diff_Suc add.commute add_diff_cancel_left' drop_Suc drop_drop dual_order.order_iff_strict fst_conv j2 le_Suc_ex otherS tl_drop tr_j)
     
     
   hence "tr = trStart @ (s, ABeginAtomic tx) # txa @ (tr!min_i) # rest
       \<and> length (trStart @ (s, ABeginAtomic tx) # txa) = min_i"
       apply auto
     by (metis One_nat_def Suc_diff_Suc \<open>min (length tr - Suc j) (min_i - Suc j) = min_i - Suc j\<close> \<open>min (length tr) j = j\<close> add.right_neutral add_Suc_right add_diff_cancel_left' diff_diff_left dual_order.order_iff_strict fst_conv j2 le_Suc_ex length_drop length_take otherS trStart_def tr_j txa_def)
   
     
    
   moreover have isFirst: "\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic"
    proof (rule ccontr)
      assume "\<not> (\<forall>a\<in>set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)"
      from this obtain otherI 
        where otherI1: "otherI < length txa"
          and otherI2: "fst (txa ! otherI) \<noteq> s \<or> snd (txa ! otherI) = AEndAtomic"
        by (metis in_set_conv_nth)
      
      have [simp]: "otherI < min_i - Suc j"
        using otherI1 txa_def by auto
        
      
        
      { (* First consider the case where we have an earlier AEndAtomic for s *)
        assume "(txa ! otherI) = (s, AEndAtomic)"
        with noEndAtomic
        have "False"
          apply (auto simp add: txa_def )
          using \<open>otherI < min_i - Suc j\<close> less_imp_le_nat min_i1 by auto
      }
      note case_endAtomic = this
      
      { (* Next, we consider the case where txa contains an action from a different session*)
        assume differentSession: "fst (txa ! otherI) \<noteq> s"
        
        define s' where s'_def: "s' = fst (txa ! otherI)"
        hence differentSession2: "s' \<noteq> s"
          by (simp add: differentSession) 
        
        define min_i' where min_i'_def: "min_i' = otherI + length trStart + 1"
        
        have [simp]: "fst (tr ! min_i') = s'"
          by (smt Suc_eq_plus1 \<open>otherI < min_i - Suc j\<close> add.assoc add.commute arith_simp diff_Suc_eq_diff_pred diff_commute length_take min_i'_def min_simp2 nth_drop nth_take s'_def trStart_def txa_def)
          
          
        
        have other_least_1: "min_i' < length tr"
          using min_i'_def \<open>otherI < min_i - Suc j\<close> less_diff_conv min_i1 trStart_def by auto
        
        have "s \<in> sessionsInTransaction tr min_i'"
          apply (auto simp add: sessionsInTransaction_def inTransaction_def)
          apply (rule_tac x="length (trStart)" in exI)
          apply auto
          apply (simp add: j1 trStart_def)
          apply (simp add: \<open>min_i' \<equiv> otherI + length trStart + 1\<close>)
          apply (simp add: trStart_def tr_j)
          by (metis One_nat_def \<open>otherI < min_i - Suc j\<close> add.right_neutral add_Suc_right dual_order.trans length_take less_diff_conv less_or_eq_imp_le min_i'_def min_simp2 noEndAtomic trStart_def)
          
        hence "s \<in> (sessionsInTransaction tr min_i' - {fst (tr ! min_i')})"
          using differentSession2  by auto
          
        hence other_least_2: "sessionsInTransaction tr min_i' - {fst (tr ! min_i')} \<noteq> {}"
          by auto 
        
        have other_least_3: "min_i' < min_i"
          using \<open>min_i' \<equiv> otherI + length trStart + 1\<close> \<open>otherI < min_i - Suc j\<close> less_diff_conv trStart_def by auto
          
          
        from other_least_1 other_least_2 other_least_3 min_i_def
        have False
          using not_less_Least by blast
      }
      with case_endAtomic
      show False
        by (metis otherI2 surjective_pairing)
    qed    
   moreover have "s \<noteq> fst (tr!min_i)"
     by (simp add: otherS)
    
   ultimately
   show ?thesis
     by blast
qed    
  


lemma split_trace_min_i2:
assumes min_i_def: "min_i = (LEAST i. indexInOtherTransaction tr tx i)"
  and i1: "min_i < length tr"
  and i2: "indexInOtherTransaction tr tx min_i"
shows "\<exists>trStart s txa rest.
       tr = trStart @ (s, ABeginAtomic tx) # txa @ tr!min_i # rest 
     \<and> length (trStart @ (s, ABeginAtomic tx) # txa) = min_i
     \<and> (\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)
     \<and> (s \<noteq> fst (tr!min_i))"
proof -
  
  from i2
  obtain j s
    where j1: "j < length tr"
      and j2: "j \<le> min_i"
      and noEndAtomic: "\<forall>k. j < k \<and> k < length tr \<and> k \<le> min_i \<longrightarrow> tr ! k \<noteq> (s, AEndAtomic)"
      and tr_j: "tr ! j = (s, ABeginAtomic tx)"
      and otherS: "s \<noteq> fst (tr ! min_i)"
    apply (atomize_elim)
    apply (auto simp add: indexInOtherTransaction_def)
    by (smt antisym_conv2 less_imp_le_nat less_trans prod.collapse prod.inject)
    
    
   obtain trStart where trStart_def: 
      "trStart = take j tr" by simp
   
   obtain txa where txa_def:
      "txa = take (min_i - j - 1) (drop (Suc j) tr)" by simp
      
   obtain rest where rest_def:
      "rest = drop (Suc min_i) tr" by simp
      
   have min_simp1[simp]: "(min (length tr - Suc j) (min_i - Suc j)) = min_i - Suc j"
     using i1 by linarith
   
   have min_simp2[simp]: "min (length tr) j = j"
     using j1 by linarith 
    
   have arith_simp[simp]: "i < min_i - Suc j \<Longrightarrow> Suc j + i \<le> length tr" for i
     using min_simp1 by linarith
    
   have arith_simp2[simp]: "i < min_i - Suc j \<Longrightarrow> Suc (j + i) \<le> length tr" for i
     using arith_simp by auto
    
     
   have "tr = trStart @ (s, ABeginAtomic tx) # txa @ (tr!min_i) # rest"
     (* this proof should be easier ... *)
     apply (auto simp add: trStart_def txa_def rest_def append_eq_conv_conj2 cons_eq_conv_conj)
     using j1 apply auto[1]
     apply (simp add: hd_drop_conv_nth j1 less_imp_le_nat min.absorb2 tr_j)
     apply (auto simp add: append_eq_conv_conj)
     apply (simp add: drop_Suc tl_drop)
     apply (rule sym)
     apply (auto simp add: cons_eq_conv_conj)
     apply (metis fst_conv i1 j1 j2 le_diff_iff le_less_Suc_eq not_le not_less_eq_eq otherS tr_j)
     apply (smt Suc_leI drop_Suc fst_conv hd_drop_conv_nth i1 j1 j2 le_add_diff_inverse length_drop length_take less_imp_le_nat min_simp1 nat_neq_iff not_le nth_drop otherS take_all tl_drop tr_j)
     apply (subst tl_drop)
     apply (case_tac j)
     apply auto
     apply (metis Suc_diff_Suc diff_zero drop_Suc fst_conv j2 le_less otherS tr_j)
     apply (case_tac nat)
     apply auto
     apply (metis (mono_tags, lifting) One_nat_def Suc_diff_Suc diff_zero drop_0 drop_Suc dual_order.order_iff_strict fst_conv j2 less_le_trans less_numeral_extra(1) otherS tr_j)
     by (smt Suc_diff_Suc add.commute add_diff_cancel_left' drop_Suc drop_drop dual_order.order_iff_strict fst_conv j2 le_Suc_ex otherS tl_drop tr_j)
     
     
   hence "tr = trStart @ (s, ABeginAtomic tx) # txa @ (tr!min_i) # rest
       \<and> length (trStart @ (s, ABeginAtomic tx) # txa) = min_i"
       apply auto
     by (metis One_nat_def Suc_diff_Suc \<open>min (length tr - Suc j) (min_i - Suc j) = min_i - Suc j\<close> \<open>min (length tr) j = j\<close> add.right_neutral add_Suc_right add_diff_cancel_left' diff_diff_left dual_order.order_iff_strict fst_conv j2 le_Suc_ex length_drop length_take otherS trStart_def tr_j txa_def)
   
     
    
   moreover have isFirst: "\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic"
    proof (rule ccontr)
      assume "\<not> (\<forall>a\<in>set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)"
      from this obtain otherI 
        where otherI1: "otherI < length txa"
          and otherI2: "fst (txa ! otherI) \<noteq> s \<or> snd (txa ! otherI) = AEndAtomic"
        by (metis in_set_conv_nth)
      
      have [simp]: "otherI < min_i - Suc j"
        using otherI1 txa_def by auto
        
      
        
      { (* First consider the case where we have an earlier AEndAtomic for s *)
        assume "(txa ! otherI) = (s, AEndAtomic)"
        with noEndAtomic
        have "False"
          apply (auto simp add: txa_def )
          using \<open>otherI < min_i - Suc j\<close> less_imp_le_nat i1 by auto
      }
      note case_endAtomic = this
      
      { (* Next, we consider the case where txa contains an action from a different session*)
        assume differentSession: "fst (txa ! otherI) \<noteq> s"
        
        define s' where s'_def: "s' = fst (txa ! otherI)"
        hence differentSession2: "s' \<noteq> s"
          by (simp add: differentSession) 
        
        define min_i' where min_i'_def: "min_i' = otherI + length trStart + 1"
        
        have [simp]: "fst (tr ! min_i') = s'"
          by (smt Suc_eq_plus1 \<open>otherI < min_i - Suc j\<close> add.assoc add.commute arith_simp diff_Suc_eq_diff_pred diff_commute length_take min_i'_def min_simp2 nth_drop nth_take s'_def trStart_def txa_def)
          
          
        
        have other_least_1: "min_i' < length tr"
          using min_i'_def \<open>otherI < min_i - Suc j\<close> less_diff_conv i1 trStart_def by auto
        
        have "indexInOtherTransaction tr tx min_i'"
          apply (auto simp add: indexInOtherTransaction_def)
          apply (simp add: other_least_1)
          by (metis Suc_eq_plus1 \<open>otherI < min_i - Suc j\<close> add.assoc differentSession2 le_add2 le_less length_take less_Suc_eq_le less_diff_conv less_trans min_i'_def min_simp2 noEndAtomic other_least_1 trStart_def tr_j)
        
        hence False
          by (metis Suc_eq_plus1 \<open>otherI < min_i - Suc j\<close> add.assoc length_take less_diff_conv min_i'_def min_i_def min_simp2 not_less_Least trStart_def)
      }
      with case_endAtomic
      show False
        by (metis otherI2 surjective_pairing)
    qed    
   moreover have "s \<noteq> fst (tr!min_i)"
     by (simp add: otherS)
    
   ultimately
   show ?thesis
     by blast
qed    
    
lemma show_traceCorrect_same:
assumes sameTraceContent: "set tr = set tr'"
   and sameExecutions: "\<And>S. (initialState program ~~ tr \<leadsto>* S) \<longleftrightarrow> (initialState program ~~ tr' \<leadsto>* S)"
shows "traceCorrect program tr' = traceCorrect program tr"
using assms by (auto simp add: traceCorrect_def)


lemma sumSplit:
fixes f :: "nat \<Rightarrow> nat"
shows "(\<Sum>i<x+y . f i) = (\<Sum>i<x . f i) + (\<Sum>i<y . f (x+i))"
by (induct y, auto)

lemma transactionsArePackedMeasure_append:
"transactionsArePackedMeasure (xs@ys) = 
   (\<Sum>i<length xs. card (sessionsInTransaction xs i - {fst (xs ! i)})) 
 + (\<Sum>i<length ys. card (sessionsInTransaction (xs@ys) (length xs + i) - {fst (ys ! i)}))"
proof -
  have "transactionsArePackedMeasure (xs@ys)
    = (\<Sum>i<length xs + length ys. card (sessionsInTransaction (xs @ ys) i - {fst ((xs @ ys) ! i)}))" 
    by (auto simp add: transactionsArePackedMeasure_def)
  moreover have "... =  
          (\<Sum>i<length xs. card (sessionsInTransaction (xs @ ys) i - {fst ((xs @ ys) ! i)}))
        + (\<Sum>i<length ys. card (sessionsInTransaction (xs @ ys) (length xs + i) - {fst ((xs @ ys) ! (length xs + i))}))"
      using sumSplit by auto
  moreover have "... = 
          (\<Sum>i<length xs. card (sessionsInTransaction xs i - {fst (xs ! i)}))
        + (\<Sum>i<length ys. card (sessionsInTransaction (xs @ ys) (length xs + i) - {fst (ys ! i)}))"
    apply auto
    by (metis (no_types, lifting) lessThan_iff nth_append sum.cong)
  ultimately show ?thesis by simp
qed  

lemma beginAtomicInTrace_to_transactionStatus:
assumes "S ~~ tr \<leadsto>* S'" 
    and "(s, ABeginAtomic tx) \<in> set tr"
shows "tx \<in> dom (transactionStatus S')"
using assms by (induct rule: steps.induct, auto simp add: step_simps)


lemma transactionIdsUnique:
assumes "S ~~ tr \<leadsto>* S'" 
   and "i < length tr" 
   and "tr!i = (s, ABeginAtomic tx)"
   and "j < length tr" 
   and "tr!j = (s', ABeginAtomic tx)"
shows "i = j"    
using assms apply (induct rule: steps.induct)
apply (auto simp add: step_simps Pair_inject  less_Suc_eq nth_append  )
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem)
by (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem)


lemma usePropertyOfLeast:
fixes x :: "'a :: wellorder"
assumes wellDefined: "Q x"
    and weakerProperty: "\<And>x. Q x \<Longrightarrow> P x"
shows "P (LEAST x. Q x)"
  using LeastI weakerProperty wellDefined by auto

lemma showIsLeast: 
fixes x :: "'a :: wellorder"
assumes "P x"
  and "\<And>y. P y \<Longrightarrow> x \<le> y"
shows "x = (LEAST x. P x)"
  using Least_equality assms(1) assms(2) by auto
  
lemma nth_secondHalf_eq:
assumes "i\<ge>length xs"
   and "length xs = length ys"
shows "(xs@zs)!i = (ys@zs)!i"
using assms by (auto simp add: nth_append)

lemma nth_append_second:
"i \<ge> length xs \<Longrightarrow> (xs@ys)!i = ys!(i - length xs)"
by (auto simp add:  nth_append split: if_splits)

lemma nth_cons_tail:
"i > 0 \<Longrightarrow> (x#xs)!i = xs!(i - 1)"
by (auto simp add:  nth_Cons split: nat.splits)

lemma nth_append_first:
"i < length xs \<Longrightarrow> (xs@ys)!i = xs!i"
by (auto simp add:  nth_append split: if_splits)

lemma show_appendEqH: 
"\<lbrakk>n \<le> length ys; length xs \<ge> n; take n xs = take n ys; drop n xs = zs\<rbrakk> \<Longrightarrow> xs = (take n ys) @ zs"
by (metis append_take_drop_id) 


(*TODO we can drop uncommited transaction, without changing the correctness of a trace, 
 however this will not end in the same state anymore (maybe in the same invcontext)

 
 TODO therefore, I can also simplify the definition of packedness
 *)
lemma canPackOneTransaction:
assumes "initialState program ~~ tr \<leadsto>* S'"
    and "beginAtomic < length tr"
    and "tr ! beginAtomic = (s, ABeginAtomic tx)"
    and "endAtomic < length tr"
    and "beginAtomic < endAtomic"
    and "tr ! endAtomic = (s, AEndAtomic) "
    and "\<And>i. \<lbrakk>beginAtomic<i; i<endAtomic\<rbrakk> \<Longrightarrow> tr ! i \<noteq> (s, AEndAtomic)"
    and "length insideTx = endAtomic - beginAtomic - 1"
    and "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
    and "tr'' = trStart @ insideTxOther @  (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
     (* NOTE from this assumption, we can later show that everything that was already packed is still packed *)
    and "insideTxOther = filter (\<lambda>a. fst a \<noteq> s) insideTx"
    and "insideTxSame = filter (\<lambda>a. fst a = s) insideTx"
shows "transactionIsPacked tr'' tx 
        \<and> (initialState program ~~ tr'' \<leadsto>* S') 
        \<and> (traceCorrect program tr'' \<longleftrightarrow> traceCorrect program tr)"
using assms
proof (induct "transactionIsPackedMeasure tr tx"  arbitrary: tr tr'' trStart beginAtomic insideTx insideTxOther insideTxSame rule: nat_less_induct )
  case 1
  fix tr tr'' trStart :: "(session \<times> action)  list" 
  fix beginAtomic :: nat
  fix insideTx :: "(session \<times> action)  list" 
  fix insideTxOther insideTxSame :: "(session \<times> action)  list" 
  assume tr_steps: "initialState program ~~ tr \<leadsto>* S'"
  assume beginAtomic_len: "beginAtomic < length tr"
  assume tr_beginAtomic: "tr ! beginAtomic = (s, ABeginAtomic tx)"
  assume endAtomic_len: "endAtomic < length tr"
  assume beginBeforeEnd: "beginAtomic < endAtomic"
  assume tr_endAtomic: "tr ! endAtomic = (s, AEndAtomic)"
  assume noEndAtomicInTx: "\<And>i. \<lbrakk>beginAtomic < i; i < endAtomic\<rbrakk> \<Longrightarrow> tr ! i \<noteq> (s, AEndAtomic)"
  assume insideTx_len: "length insideTx = endAtomic - beginAtomic - 1"
  assume tr_splitLemma: "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
  assume tr''_split: "tr'' = trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
  assume insideTxOther_def: "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]"
  assume insideTxSame_def: "insideTxSame = [a\<leftarrow>insideTx . fst a = s]" 
  assume ih: "\<forall>m<transactionIsPackedMeasure tr tx.
       \<forall>x. m = transactionIsPackedMeasure x tx \<longrightarrow>
           initialState program ~~ x \<leadsto>* S' \<longrightarrow>
           (\<forall>xa xb xc. xc < length x \<longrightarrow>
                       x ! xc = (s, ABeginAtomic tx) \<longrightarrow>
                       endAtomic < length x \<longrightarrow>
                       xc < endAtomic \<longrightarrow>
                       x ! endAtomic = (s, AEndAtomic) \<longrightarrow>
                       (\<forall>xa>xc. xa < endAtomic \<longrightarrow> x ! xa \<noteq> (s, AEndAtomic)) \<longrightarrow>
                       (\<forall>xd. length xd = endAtomic - xc - 1 \<longrightarrow>
                             x = xb @ (s, ABeginAtomic tx) # xd @ (s, AEndAtomic) # trRest \<longrightarrow>
                             (\<forall>xc xe. xa = xb @ xc @ (s, ABeginAtomic tx) # xe @ (s, AEndAtomic) # trRest \<longrightarrow>
                                      xc = [a\<leftarrow>xd . fst a \<noteq> s] \<longrightarrow> xe = [a\<leftarrow>xd . fst a = s] \<longrightarrow> transactionIsPacked xa tx \<and> initialState program ~~ xa \<leadsto>* S' \<and> traceCorrect program xa = traceCorrect program x)))"
  (* show "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect program tr'' = traceCorrect program tr" *)
    
  have inductionHypothesis2: 
          "transactionIsPacked tr'' tx 
        \<and> (initialState program ~~ tr'' \<leadsto>* S') 
        \<and> (traceCorrect program tr'' \<longleftrightarrow> traceCorrect program tr')"
     if a1: "initialState program ~~ tr' \<leadsto>* S'"
    and a2: "Suc beginAtomic < length tr'"
    and a3: "tr' ! Suc beginAtomic = (s, ABeginAtomic tx)"
    and a4: "endAtomic < length tr'"
    and a5: "Suc beginAtomic < endAtomic"
    and a6: "tr' ! endAtomic = (s, AEndAtomic)"
    and a7: "\<And>i. \<lbrakk>Suc beginAtomic<i; i<endAtomic\<rbrakk> \<Longrightarrow> tr' ! i \<noteq> (s, AEndAtomic)"
    and a8: "length insideTx = endAtomic - Suc beginAtomic - 1"
    and a9: "tr' = trStart' @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
    and a10: " tr'' = trStart' @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
    and a11: "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]"
    and a12: "insideTxSame = [a\<leftarrow>insideTx . fst a = s]"
    and measureDecr: "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
    for tr' tr'' trStart' insideTx insideTxOther insideTxSame::"(session \<times> action) list" and beginAtomic::nat
    using that ih  by blast
    (* manual proof: *) (*
    apply (insert ih)
    apply (drule_tac x="transactionIsPackedMeasure tr' tx" in spec)
    apply (drule mp)
    apply (rule measureDecr)
    apply (drule_tac x="tr'" in spec)
    apply (drule mp)
    apply simp
    apply (drule mp)
    apply (rule a1)
    apply (drule_tac x="tr''" in spec)
    apply (drule_tac x="trStart'" in spec)
    apply (drule_tac x="Suc beginAtomic" in spec)
    apply (drule mp)
    apply (rule a2)
    apply (drule mp)
    apply (rule a3)
    apply (drule mp)
    apply (rule a4)
    apply (drule mp)
    apply (rule a5)   
    apply (drule mp)
    apply (rule a6) 
    apply (drule mp)
    using a7 apply blast
    apply (drule_tac x="insideTx" in spec)
    apply (drule mp)
    apply (rule a8)
    apply (drule mp)
    apply (rule a9)
    apply (drule_tac x="insideTxOther" in spec)
    apply (drule_tac x="insideTxSame" in spec)
    apply (drule mp)
    apply (rule a10)
    apply (drule mp)
    apply (rule a11)
    apply (drule mp)
    apply (rule a12)
    apply assumption
    done
    *)
    
  have beginAtomicUnique: "i = beginAtomic" if "tr!i = (c', ABeginAtomic tx)" and "i<length tr"  for i c'
    using transactionIdsUnique that beginAtomic_len tr_beginAtomic tr_steps by blast 
   
  have trStart_len: "length trStart = beginAtomic"
    using tr_beginAtomic apply (auto simp add: tr_splitLemma)
    using beginAtomic_len tr_splitLemma tr_steps transactionIdsUnique by auto 
  
  
  
  have insideTx_noEnd: "insideTx ! i \<noteq> (s, AEndAtomic)" if "i < length insideTx" for i
  proof -
    have "tr ! (beginAtomic + 1 + i) \<noteq> (s, AEndAtomic)"
    using noEndAtomicInTx insideTx_len that by auto 
    thus ?thesis
      apply (simp add: tr_splitLemma)
      by (simp add: nth_append that trStart_len)
  qed   
  
  
  
  have trRest_len: "length trRest = length tr - endAtomic - 1"
  proof -
    have "length tr - endAtomic - 1 = (Suc (length trStart + (length insideTx + length trRest))) - endAtomic"
      by (auto simp add: tr_splitLemma)
    moreover have "... = 1 + length trStart + length insideTx + length trRest - endAtomic"
      by simp
    moreover have "... = 1 + length trStart + (endAtomic - beginAtomic - 1) + length trRest - endAtomic" 
      by (simp add: insideTx_len)
    moreover have "... = length trStart + (endAtomic - beginAtomic) + length trRest - endAtomic"
      using beginBeforeEnd by auto 
    moreover have "... = length trStart + endAtomic + length trRest - endAtomic - beginAtomic"  
      by (simp add: beginBeforeEnd order_less_imp_le trStart_len)
    moreover have "... = length trStart + length trRest - beginAtomic"
      by simp
    moreover have "... = length trRest"   
      by (simp add: trStart_len)
    ultimately show ?thesis
      by linarith    
  qed  
  
(*
  hence tr_steps: "initialState program ~~ tr \<leadsto>* S'" ..
  
  from 1
  have inductionHypothesis:
   "\<exists>tr''. transactionIsPacked tr'' tx
      \<and> (\<forall>t. transactionIsPacked tr' t \<longrightarrow> transactionIsPacked tr'' t)
      \<and> (initialState program ~~ tr'' \<leadsto>* S') 
      \<and> (traceCorrect program tr'' \<longleftrightarrow> traceCorrect program tr')"
      if "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
      and "initialState program ~~ tr' \<leadsto>* S'"
      for tr' 
    apply (insert 1)
    apply (drule_tac x="transactionIsPackedMeasure tr' tx" in spec)
    apply (simp add: that)
    done
*)      
    
  
  show "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect program tr'' = traceCorrect program tr"
  proof (cases "transactionIsPackedMeasure tr tx")
    case 0
    text "If the measure is zero, transaction is already packed"
    hence "transactionIsPacked tr tx"
      by (simp add: transactionIsPackedMeasure_zero_iff)
      
    hence "fst a = s" if  "a \<in> set insideTx" for a
    proof -
      from that obtain ii where "insideTx ! ii = a" and "ii < length insideTx" 
        by (auto simp add: in_set_conv_nth)
      thm tr_splitLemma
      define i where i_def: "i = ii + 1 + length trStart"
      from i_def
      have [simp]: "beginAtomic < i"
          and "i < endAtomic"
          and "tr!i = a"
        apply (auto simp add: tr_splitLemma)
        apply (simp add: trStart_len)
        using \<open>ii < length insideTx\<close> insideTx_len trStart_len apply linarith
        apply (auto simp add: nth_append nth_Cons split: nat.splits)
        using \<open>insideTx ! ii = a\<close> apply blast
        using \<open>ii < length insideTx\<close> apply blast
        using \<open>ii < length insideTx\<close> by blast
      have [simp]: "i < length tr"
        using \<open>i < endAtomic\<close> dual_order.strict_trans endAtomic_len by blast 
        
      assume "transactionIsPacked tr tx"
      hence "\<not> indexInOtherTransaction tr tx i"
        by (simp add: transactionIsPacked_def)
      hence "s = fst a"
        apply (auto simp add: indexInOtherTransaction_def)
        apply (drule_tac x=beginAtomic in spec)
        apply auto
        apply (drule_tac x=s in spec)
        apply auto
        apply (simp add: tr_beginAtomic)
        apply (simp add: `tr!i = a`)
        using \<open>i < endAtomic\<close> dual_order.strict_trans noEndAtomicInTx by blast
      thus "fst a = s" by simp
    qed  
          
    hence "tr'' = tr"  
      by (auto simp add: tr''_split tr_splitLemma insideTxOther_def insideTxSame_def)
      
      
    thus ?thesis
      using \<open>transactionIsPacked tr tx\<close> tr_steps by auto
  next
    case (Suc n)
    
    text {*
      We can find the smallest i, such that the action is concurrent to another transaction
    *}
    from Suc
    obtain k
      where k_inTx: "indexInOtherTransaction tr tx k"
      apply (auto simp add: transactionIsPackedMeasure_def)
      by fastforce
    
    obtain kmin
      where kmin_def: "kmin = (LEAST k. indexInOtherTransaction tr tx k)" 
      and kmin_inTx: "indexInOtherTransaction tr tx kmin"
      using LeastI k_inTx by auto
    
    have kmin_least: 
      "kmin \<le> k"
      if "indexInOtherTransaction tr tx k"
      for k
      using that
      by (simp add: Least_le kmin_def) 
    
    have "kmin > beginAtomic"
      by (smt beginAtomic_len indexInOtherTransaction_def kmin_inTx less_trans tr_beginAtomic tr_steps transactionIdsUnique)
    
    have "kmin < endAtomic"
      by (smt beginBeforeEnd dual_order.strict_trans fst_conv indexInOtherTransaction_def kmin_inTx linorder_neqE_nat tr_beginAtomic tr_endAtomic tr_steps transactionIdsUnique)
    
    have kmin_noOtherBefore:  "fst (tr!i) = s" if "i > beginAtomic" and "i<kmin" for i
      proof (rule ccontr)
        assume "fst (tr ! i) \<noteq> s" 
        hence "indexInOtherTransaction tr tx i"
          using that apply (auto simp add: indexInOtherTransaction_def)
          using \<open>kmin < endAtomic\<close> endAtomic_len apply auto[1]
          using \<open>kmin < endAtomic\<close> noEndAtomicInTx tr_beginAtomic by auto
        with kmin_least
        have "kmin \<le> i"
          by blast
        with that
        show False
          using not_less by blast
      qed    
      
      
      
    (*use one_compaction_step on kmin*)
    thm one_compaction_step2
    
    
    obtain min_s where min_s_def: "min_s = fst (tr!kmin)" by simp
    obtain min_a where min_a_def: "min_a = snd (tr!kmin)" by simp
    
    have kmin_length: "kmin < length tr"
      using indexInOtherTransaction_def kmin_inTx by blast
    
    have insideTx_len: "kmin - length trStart - 1 < length insideTx"
      using \<open>beginAtomic < kmin\<close> \<open>kmin < endAtomic\<close> insideTx_len trStart_len by linarith
      
    
    have insideTx_kmin: "insideTx ! (kmin - length trStart - 1) = (tr!kmin)"
      using \<open>beginAtomic < kmin\<close> order.asym trStart_len apply (auto simp add: tr_splitLemma nth_append nth_Cons split: nat.splits)
      apply (simp add: minus_nat.simps(2))
      using \<open>kmin < endAtomic\<close> insideTx_len apply linarith
      using \<open>kmin < endAtomic\<close> insideTx_len by linarith
      
      
    hence "(tr!kmin) \<in> set insideTx"
      using insideTx_len nth_mem by force
    
    hence "(min_s, min_a) \<in> set insideTx"
      by (simp add: min_a_def min_s_def)  
      
    from insideTx_kmin  
    obtain txa txb
      where insideTx_split: "insideTx = txa @ (min_s, min_a) # txb"
        and txa_len: "length txa = kmin - length trStart - 1"
      apply (atomize_elim)  
      apply (rule_tac x="take (kmin - length trStart - 1) insideTx" in exI)
      apply (rule_tac x="drop (kmin - length trStart) insideTx" in exI)
      using insideTx_len apply auto
      by (metis Cons_nth_drop_Suc Suc_diff_Suc \<open>beginAtomic < kmin\<close> less_or_eq_imp_le min_a_def min_s_def prod.collapse show_appendEqH trStart_len)

    have txa_txb_len: "length txa + length txb = length insideTx - 1"
      by (simp add: insideTx_split)
      
    define rest where "rest = txb @ (s, AEndAtomic) # trRest"  
    
    have tr_split: "tr = trStart @ (s, ABeginAtomic tx) # txa @ (min_s, min_a) # rest"
      using rest_def insideTx_split tr_splitLemma by auto
    have tr_split1: "length (trStart @ (s, ABeginAtomic tx) # txa) = kmin"
      by (simp add: Suc_diff_Suc \<open>beginAtomic < kmin\<close> less_or_eq_imp_le trStart_len txa_len) 
    have tr_split2h: "a \<noteq> (s, AEndAtomic)" if "a \<in> set txa" for  a
      using that noEndAtomicInTx apply (auto simp add: in_set_conv_nth)
      by (metis (no_types, lifting) Suc_less_eq insideTx_len insideTx_noEnd insideTx_split less_SucI less_trans_Suc nth_append_first txa_len)
    hence tr_split2: "fst a = s \<and> snd a \<noteq> AEndAtomic" if "a \<in> set txa" for a
      proof -
        from that
        obtain i where "txa ! i = a" and "i < length txa" 
          by (auto simp add: in_set_conv_nth)
        hence "tr!(1+i+length trStart) = a"
          apply (auto simp add: tr_splitLemma)
          by (simp add: insideTx_split nth_append)
        moreover have "1+i+length trStart > beginAtomic"
          using trStart_len by auto
        moreover have "1+i+length trStart < kmin"
          using \<open>i < length txa\<close> txa_len by linarith
        moreover have "fst a = s"
          using kmin_noOtherBefore
          using calculation by blast  
        ultimately show "fst a = s \<and> snd a \<noteq> AEndAtomic"
          using that tr_split2h by fastforce
      qed
    
    have tr_split3: "s \<noteq> fst (tr ! kmin)"
      using beginAtomicUnique indexInOtherTransaction_def kmin_inTx tr_beginAtomic by auto  
      
      
    have "min_s \<noteq> s"
      using min_s_def tr_split3 by auto
      
    (*
    have endAtomicPos1: "endAtomic > beginAtomic"
      by (simp add: beginBeforeEnd) 
    *)
    
    (*
    have endAtomicPos2: "\<forall>i. i>beginAtomic \<and>  i<endAtomic \<longrightarrow> tr!i \<noteq> (s, AEndAtomic)"
      apply (auto simp add: endAtomicPos_def)
      by (smt dual_order.strict_trans not_less_Least not_less_iff_gr_or_eq)
    
    have endAtomicPos3: 
      "tr ! endAtomic = (s, AEndAtomic)" if "endAtomic < length tr"
      apply (auto simp add: endAtomicPos_def)
      apply (smt sem1_commutativity.LeastI2 that)
      by (metis endAtomicPos_def not_less_iff_gr_or_eq that)
    
        
    have "endAtomic \<le> length tr"
      apply (auto simp add: endAtomicPos_def)
      by (metis (no_types, lifting) dual_order.strict_trans endAtomicPos2 endAtomicPos_def leI)
     
    have endAtomicPos_least: 
      "endAtomic \<le> p"
      if "p>beginAtomic" and "p<length tr" and "tr!p = (s, AEndAtomic)"
      for p
      using endAtomicPos2 that(1) that(3) by auto
      
    
    have endAtomicPos1a: "endAtomic \<noteq> length txa + Suc beginAtomic"
      apply (rule ccontr)
      apply auto
      using endAtomicPos3 tr_split apply auto
      apply (auto simp add: nth_append nth_Cons split: nat.splits if_splits)
      using \<open>min_s \<noteq> s\<close> beginAtomicPos_def by force
      
    have endAtomicPos1b: "endAtomic > length txa + Suc beginAtomic"
      by (smt "1"(2) One_nat_def Suc_eq_plus1 add.left_commute beginAtomicPos_def dual_order.strict_trans endAtomicPos1 endAtomicPos3 fst_conv indexInOtherTransaction_def kmin_inTx length_append linorder_neqE_nat list.size(4) nth_append_length tr_split tr_split1 transactionIdsUnique)  
    *)  
      
      
    obtain tr' where tr'_def:
      "tr' = trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ rest" by simp
    
    have tr'_def2:
      "tr' = trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ txb @ (s, AEndAtomic) # trRest"
      by (simp add: \<open>rest \<equiv> txb @ (s, AEndAtomic) # trRest\<close> tr'_def)
      
      
    from tr_split2
    have tr_split2': "\<And>st at. (st, at) \<in> set txa \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic"
      by force
    
    have tr'_sameSet: "set tr' = set tr" 
      apply (auto simp add: tr_split2 tr'_def kmin_length min_a_def min_s_def)
      apply (auto simp add: tr_split)
      using min_a_def min_s_def tr_split apply fastforce
      using min_a_def min_s_def tr_split by force
      
    have  tr'_sameAfterTxa: 
      "tr' ! i = tr ! i"
      if "i > 1 +beginAtomic + length txa"
      for i
      using that apply (auto simp add: tr'_def tr_split nth_append_first nth_append nth_Cons trStart_len split: nat.splits)
      by (metis Suc_eq_plus1 diff_Suc_1 diff_diff_add)
      
      
      
      
    (* now, we can swap the min_i action before the beginAtomic action *)
    have tr'_steps_eq: "(initialState program ~~ tr \<leadsto>* S') \<longleftrightarrow> (initialState program ~~ tr' \<leadsto>* S')"
      using tr_split tr'_def tr_split2' proof (rule one_compaction_step3)
        show "\<And>st at. (st, at) \<in> set txa \<Longrightarrow> (st, at) \<in> set txa"
          by simp
        show "fst (min_s, min_a) \<noteq> s"
          by (simp add: \<open>min_s \<noteq> s\<close>)
        show "state_wellFormed (initialState program)"
          by simp
      qed
    hence tr'_steps: "initialState program ~~ tr' \<leadsto>* S'"
      using tr_steps by auto
    
    have tr'_rest_eq: "tr' ! i = tr ! i" if "i \<ge> Suc ( Suc (length trStart + length txa))"  for i
    proof -
      have "tr' ! i = (trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ rest) ! i"
        by (auto simp add: tr'_def)
      moreover have "... = ((trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa) @ rest) ! i"
        by simp
      moreover have "... = ((trStart @ (s, ABeginAtomic tx) # txa @ [(min_s, min_a)]) @ rest) ! i"  
        apply (rule nth_secondHalf_eq)
        using that by auto
      moreover have "... = tr ! i"
        by (auto simp add: tr_split)
      ultimately show ?thesis
        by presburger 
    qed    
      
      
    have tr'_endAtomicPos: "tr' ! endAtomic = (s, AEndAtomic)" if "endAtomic < length tr'"
      using \<open>kmin < endAtomic\<close> tr'_rest_eq tr_endAtomic tr_split1 by auto
      
      
      
      
    (* 
    the above preserves  the correctness of the trace...
    *) 
    have preservesCorrectness: "traceCorrect program tr' = traceCorrect program tr"
      proof (rule show_traceCorrect_same)
        show "set tr = set tr'"
          by (auto simp add: tr'_def tr_split )
        show "\<And>S. (initialState program ~~ tr \<leadsto>* S) \<longleftrightarrow> (initialState program ~~ tr' \<leadsto>* S)"
          using tr'_steps_eq tr_steps traceDeterministic by blast
      qed  
      
    have noOtherBeginAtomic: "(s', ABeginAtomic tx) \<notin> set trStart" for s'
    proof 
      assume "(s', ABeginAtomic tx) \<in> set trStart"
      from this obtain ii 
        where "ii < length trStart"
        and "trStart ! ii = (s', ABeginAtomic tx)"
        by (meson in_set_conv_nth)
      hence "ii < length tr" and  "tr ! ii = (s', ABeginAtomic tx)"
        using tr_split by (auto simp add: nth_append)
      thus False
        by (metis transactionIdsUnique \<open>ii < length trStart\<close> kmin_length length_append nat_neq_iff not_le nth_append_length tr_split tr_split1 tr_steps trans_le_add1) 
    qed
        
    have tr'_beginAtomicPos: "tr' ! (Suc beginAtomic) = (s, ABeginAtomic tx)"
      by (metis One_nat_def Suc_eq_plus1 nth_Cons_0 nth_Cons_Suc nth_append_length_plus tr'_def trStart_len)
      
    have tr'_beginAtomicPos_unique:
      "i = Suc beginAtomic" 
      if "tr' ! i = (s', ABeginAtomic tx)" 
      and "i<length tr'"
      for i s'
      using that transactionIdsUnique tr'_steps tr'_beginAtomicPos tr'_def tr'_steps
      using beginBeforeEnd endAtomic_len tr_split by auto 
    
    have tr_beginAtomicPos:  "tr ! beginAtomic = (s, ABeginAtomic tx)"
      by (simp add: tr_beginAtomic)
    have tr_beginAtomicPos_unique:
      "i = beginAtomic" 
      if "tr ! i = (s', ABeginAtomic tx)" 
      and "i<length tr"
      for i s'
      using that  transactionIdsUnique tr_beginAtomicPos "1"(2)
      using beginAtomicUnique by blast 
    
      
    have kmin_before_endAtomic: "kmin < endAtomic"
      by (simp add: \<open>kmin < endAtomic\<close>)
      
    (*
    this move also reduces our measure, which is probably the difficult thing to show
    *)  
    have measureDecreased: "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
    proof -
      have "transactionIsPackedMeasure tr tx 
         =  card {k. indexInOtherTransaction tr tx k}"
        by (simp add: transactionIsPackedMeasure_def)
      moreover have "... 
        = card {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
        apply (rule_tac f=card in arg_cong)
        apply (auto simp add: indexInOtherTransaction_def)
        using tr_beginAtomicPos_unique apply auto[1]
        by (metis beginBeforeEnd dual_order.strict_trans fst_conv not_less_iff_gr_or_eq tr_beginAtomicPos tr_beginAtomicPos_unique tr_endAtomic)
        
      moreover have "... 
        > card {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i}" 
        proof (rule psubset_card_mono)
          show "finite {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
            by simp
          show "{i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i}
              \<subset> {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
          proof
            show "{i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i}
               \<subseteq> {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
            proof auto
              fix x
              assume a1: "beginAtomic < x"
                 and a2: "x < endAtomic"
                 and a3: "indexInOtherTransaction tr' tx x"
              
              (* since this is in another transaction, we know that the index must be greater than ... 
               it cannot be in txa *)
              hence "x > beginAtomic + length txa"
                (* proof by aggressive splitting and sledgehammering *)
                apply (auto simp add: indexInOtherTransaction_def tr'_def)
                apply (auto simp add:  nth_append split: if_splits)
                using order.asym trStart_len apply blast
                using noOtherBeginAtomic nth_mem apply force
                apply (auto simp add:  nth_Cons split: nat.splits)
                apply (metis \<open>beginAtomic < kmin\<close> dual_order.strict_implies_not_eq kmin_length min_a_def surjective_pairing tr_beginAtomicPos_unique)
                apply (metis \<open>beginAtomic < kmin\<close> dual_order.strict_iff_order kmin_length min_a_def prod.collapse tr_beginAtomicPos_unique)
                apply (auto simp add:  nth_append split: if_splits)[1]
                using nth_mem tr_split2 apply blast
                using trStart_len apply linarith
                apply (auto simp add:  nth_append split: if_splits)[1]
                apply (metis nth_mem prod.collapse tr_split2')
                using trStart_len apply linarith
                using trStart_len by linarith
                
              from a3 obtain i s'
                where h1: "x < length tr'"
                  and h2: "i < x"
                  and h3: "tr' ! i = (s', ABeginAtomic tx)"
                  and h4: "fst (tr' ! x) \<noteq> s'"
                  and h5: "\<forall>j<x. i < j \<longrightarrow> tr' ! j \<noteq> (s', AEndAtomic)"
                by (auto simp add: indexInOtherTransaction_def)
              
              have i_def: "i = Suc beginAtomic"
               using h3 h1 h2 less_trans tr'_beginAtomicPos_unique by blast 
              
              have s'_def[simp]: "s' = s"
                using \<open>i = Suc beginAtomic\<close> h3 tr'_beginAtomicPos by auto
                
              have [simp]: "x < length tr"
                using \<open>endAtomic < length tr\<close> a2 less_trans by blast 
                
                
              show "indexInOtherTransaction tr tx x"
                proof (auto simp add: indexInOtherTransaction_def)
                  show "\<exists>i<x. \<exists>s. tr ! i = (s, ABeginAtomic tx) \<and> fst (tr ! x) \<noteq> s \<and> (\<forall>j<x. i < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic))"
                  proof (rule_tac x="beginAtomic" in exI, intro conjI)
                    show "beginAtomic < x"
                      by (simp add: a1)
                    show "\<exists>s. tr ! beginAtomic = (s, ABeginAtomic tx) \<and> fst (tr ! x) \<noteq> s \<and> (\<forall>j<x. beginAtomic < j \<longrightarrow> tr ! j \<noteq> (s, AEndAtomic))"
                    proof (rule_tac x="s" in exI, auto)
                      show "tr ! beginAtomic = (s, ABeginAtomic tx)"
                        using tr_beginAtomicPos by auto
                      show "s = fst (tr ! x) \<Longrightarrow> False"
                        using h4
                        apply (auto simp add: tr_split tr'_def nth_append split: if_splits)
                        using s'_def apply auto[1]
                        apply (auto simp add: nth_append nth_Cons split: nat.splits if_splits)
                        using a1 trStart_len apply blast
                        using Suc_lessD nth_mem tr_split2 apply blast
                        using \<open>min_s \<noteq> s\<close> apply blast
                        by (metis Suc_diff_le Suc_inject leI)
                      show "\<And>j. \<lbrakk>j < x; beginAtomic < j; tr ! j = (s, AEndAtomic)\<rbrakk> \<Longrightarrow> False"
                        using a2 noEndAtomicInTx order.strict_trans by blast
                    qed    
                  qed  
                qed
            qed
          next 
            show "{i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i}
               \<noteq> {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
              proof -
                have "kmin \<in> {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr tx i}"
                  proof auto
                    show "beginAtomic < kmin"
                      by (simp add: \<open>beginAtomic < kmin\<close>)
                    show "kmin < endAtomic"
                      by (simp add: kmin_before_endAtomic)
                    show "indexInOtherTransaction tr tx kmin"
                      by (simp add: kmin_inTx)  
                  qed
                moreover have "kmin \<notin> {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i}"
                  proof (auto simp add: indexInOtherTransaction_def)
                    fix i s'
                    assume a0: "kmin < length tr'"
                       and a1: "kmin < endAtomic"
                       and a2: "beginAtomic < kmin"
                       and a3: "i < kmin"
                       and a4: "tr' ! i = (s', ABeginAtomic tx)"
                       and a5: "\<forall>j>i. j < kmin \<longrightarrow> tr' ! j \<noteq> (s', AEndAtomic)"
                    
                    from a4    
                    have a6: "i = Suc beginAtomic"
                      using a0 a3 less_trans tr'_beginAtomicPos_unique by blast

                    from a4
                    have a7: "s' = s"
                      using a0 a3 tr'_beginAtomicPos tr'_beginAtomicPos_unique by auto
                      
                    have "(tr' ! kmin) \<in> set txa"
                      apply (auto simp add: tr'_def nth_append nth_Cons split: nat.splits)
                      using a2 order.asym trStart_len apply blast
                      using trStart_len tr_beginAtomicPos tr_split3 apply auto[1]
                      using a3 a6 trStart_len apply linarith
                      using tr_split1 by auto
                      
                    thus "fst (tr' ! kmin) = s'"
                      using a7 tr_split2 by blast
                  qed    
                  ultimately show ?thesis
                    by blast
                qed
              qed
        qed        
      moreover have "card {i. beginAtomic < i \<and> i < endAtomic \<and> indexInOtherTransaction tr' tx i} 
                  = card {i. indexInOtherTransaction tr' tx i}"
        apply (rule_tac f=card in arg_cong)
        proof (auto simp add: indexInOtherTransaction_def; (rename_tac s'))
          fix x i s
          assume a0: "x < length tr'"
             and a1: "i < x"
             and a2: "tr' ! i = (s, ABeginAtomic tx)"
             and a3: "fst (tr' ! x) \<noteq> s"
             and a4: "\<forall>j<x. i < j \<longrightarrow> tr' ! j \<noteq> (s, AEndAtomic)"
          
          show "beginAtomic < x"
            using a0 a1 a2 by (metis Suc_le_eq dual_order.strict_trans less_or_eq_imp_le tr'_beginAtomicPos_unique)
        next
          fix x i s'
          assume a0: "x < length tr'"
             and a1: "i < x"
             and a2: "tr' ! i = (s', ABeginAtomic tx)"
             and a3: "fst (tr' ! x) \<noteq> s'"
             and a4: "\<forall>j<x. i < j \<longrightarrow> tr' ! j \<noteq> (s', AEndAtomic)"
          
          from a2
          have a5:"i = Suc beginAtomic"
            using a0 a1 less_trans tr'_beginAtomicPos_unique by blast 
          from a2 
          have a6: "s' = s"
            by (simp add: \<open>i = Suc beginAtomic\<close> tr'_beginAtomicPos)
            
          from a4 
          have a7: "\<forall>j<x. Suc beginAtomic < j \<longrightarrow> tr' ! j \<noteq> (s, AEndAtomic)"
            using \<open>i = Suc beginAtomic\<close> \<open>s' = s\<close> by blast
            
          show "x < endAtomic"
            proof (cases "endAtomic < length tr'")
              case False
                thus "x < endAtomic"
                  using a0 by linarith
            next
              case True
                {
                  assume "x \<ge> endAtomic"
                  with a7 have notEA: "tr' ! endAtomic \<noteq> (s, AEndAtomic)"
                    by (metis \<open>beginAtomic < kmin\<close> a3 a6 antisym_conv2 fst_conv kmin_before_endAtomic less_trans_Suc)
                  have "tr ! endAtomic = (s, AEndAtomic)"
                    by (simp add: tr_endAtomic)
                  hence "tr' ! endAtomic = (s, AEndAtomic)"
                    using True tr'_endAtomicPos by blast 
                  with notEA have False
                    by blast
                }
                thus ?thesis
                  using not_le by blast 
            qed
        qed    
      moreover have "... = transactionIsPackedMeasure tr' tx"
        by (simp add: transactionIsPackedMeasure_def)
      ultimately show "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
        by simp
    qed
    (* "tr = trStart @ (s, ABeginAtomic tx) # txa @ x # rest" *)
    from `initialState program ~~ tr \<leadsto>* S'`
    have steps_tr': "initialState program ~~ tr' \<leadsto>* S'"
      using tr'_steps_eq by blast
    
    have tr'_len: "length tr' = length tr"
      by (simp add: tr'_def tr_split)
      
    have "Suc beginAtomic < length tr'"
      using beginBeforeEnd endAtomic_len tr'_len by linarith
      
    define insideTx' where "insideTx' = txa @ txb"
    define insideTxOther' where "insideTxOther' = [a\<leftarrow>insideTx' . fst a \<noteq> s]"
    define insideTxSame' where "insideTxSame' = [a\<leftarrow>insideTx' . fst a = s]"
    
    (*
    have "tr' = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
      apply (simp add: tr'_def)
      *)
    have [simp]: "[a\<leftarrow>txa . fst a \<noteq> s] = []"   
      apply (auto simp add: filter_empty_conv)
      by (simp add: tr_split2')
    
    hence insideTxOther_cons: "insideTxOther = (min_s, min_a) # insideTxOther'"
      by (auto simp add: insideTxOther_def insideTxOther'_def insideTx_split insideTx'_def \<open>min_s \<noteq> s\<close>)
      
    have insideTxSame_unchanged[simp]: "insideTxSame' = insideTxSame"
      by (auto simp add: insideTxSame'_def insideTxSame_def insideTx'_def insideTx_split \<open>min_s \<noteq> s\<close>)
      
      
      
    
    have "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect program tr'' = traceCorrect program tr'"  
    proof (rule inductionHypothesis2)
      show "initialState program ~~ tr' \<leadsto>* S'" 
        using `initialState program ~~ tr' \<leadsto>* S'` .
      show "Suc beginAtomic < length tr'"
        by (simp add: \<open>Suc beginAtomic < length tr'\<close>)
      show "tr' ! Suc beginAtomic = (s, ABeginAtomic tx)"
        by (simp add: tr'_beginAtomicPos)
      show "endAtomic < length tr'"
        by (simp add: endAtomic_len tr'_len)
      show "Suc beginAtomic < endAtomic"
        using \<open>beginAtomic < kmin\<close> kmin_before_endAtomic less_trans_Suc by blast
      show "tr' ! endAtomic = (s, AEndAtomic)"
        using \<open>endAtomic < length tr'\<close> tr'_endAtomicPos by blast
      show "tr' ! i \<noteq> (s, AEndAtomic)" if "Suc beginAtomic < i" and "i < endAtomic" for i
        proof (cases "1 + beginAtomic + length txa < i")
          case True
            hence "tr' ! i = tr ! i"
              by (rule tr'_sameAfterTxa)
            thus "tr' ! i \<noteq> (s, AEndAtomic)"
              using that apply simp
              using Suc_lessD noEndAtomicInTx by blast 
        next
          case False
            thus "tr' ! i \<noteq> (s, AEndAtomic)" 
              apply (auto simp add: tr'_def nth_append nth_Cons split: nat.splits)
              using Suc_lessD order.asym that(1) trStart_len apply blast
              apply (simp add: \<open>min_s \<noteq> s\<close>)
              using nth_mem tr_split2' apply fastforce
              using trStart_len by linarith
        qed      
      show "length insideTx' = endAtomic - Suc beginAtomic - 1"  
        apply (auto simp add: insideTx'_def  min_def)
        using endAtomic_len insideTx_len kmin_before_endAtomic trStart_len tr_split tr_split1 apply auto[1]
        apply (simp add: rest_def insideTx_split)
        by (smt One_nat_def Suc_diff_Suc Suc_eq_plus1 Suc_leI \<open>beginAtomic < kmin\<close> \<open>rest \<equiv> txb @ (s, AEndAtomic) # trRest\<close> add.commute add_Suc_right add_diff_cancel_left' add_diff_cancel_right' add_eq_if diff_Suc_1 diff_add_inverse diff_diff_add diff_diff_left diff_zero dual_order.strict_implies_not_eq endAtomic_len insideTx_split kmin_before_endAtomic le_add_diff_inverse length_Cons length_append less_not_refl2 less_or_eq_imp_le list.size(4) minus_nat.diff_0 minus_nat.simps(2) nat.simps(3) rest_def tr'_def tr'_len trRest_len trStart_len tr_split1 txa_txb_len zero_less_diff)
      (*have lenH: "length insideTx - Suc (length txa) \<le> length rest"
        by (smt Suc_diff_Suc Suc_eq_plus1 \<open>beginAtomic < kmin\<close> \<open>length insideTx' = endAtomic - Suc beginAtomic - 1\<close> add_diff_inverse_nat beginBeforeEnd diff_diff_left endAtomic_len insideTx'_def kmin_before_endAtomic le_cases length_Cons length_append less_trans_Suc order.asym take_all tr'_def tr'_len trStart_len)*)
      show "tr' = (trStart @ [(min_s, min_a)]) @ (s, ABeginAtomic tx) # insideTx' @ (s, AEndAtomic) # trRest" 
        using  txa_txb_len by (auto simp add: tr'_def2 insideTx'_def rest_def)
      show "tr'' = (trStart @ [(min_s, min_a)]) @ insideTxOther' @ (s, ABeginAtomic tx) # insideTxSame' @ (s, AEndAtomic) # trRest" 
        apply (auto simp add: tr''_split insideTx'_def)
        by (simp add: insideTxOther_cons)
      show "insideTxOther' = [a\<leftarrow>insideTx' . fst a \<noteq> s]" 
        by (simp add: insideTxOther'_def) 
      show "insideTxSame' = [a\<leftarrow>insideTx' . fst a = s]"
        by (rule insideTxSame'_def)
      show "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
        using measureDecreased by auto 
    qed    
      
                              
    thus ?thesis
      using preservesCorrectness by auto
  qed
qed  
 
  
lemma canPackTransactions:
assumes "initialState program ~~ tr \<leadsto>* S'"
shows "\<exists>tr'. transactionsArePacked tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* S') 
        \<and> (traceCorrect program tr' \<longleftrightarrow> traceCorrect program tr)"
using assms
proof (induct "transactionsArePackedMeasure tr"  arbitrary: tr S' rule: full_nat_induct )
  case 1
  
  hence tr_steps: "initialState program ~~ tr \<leadsto>* S'" ..
  
  from 1
  have inductionHypothesis:
   "\<exists>tr'. transactionsArePacked tr' 
      \<and> (initialState program ~~ tr' \<leadsto>* S) 
      \<and> traceCorrect program tr' \<longleftrightarrow> traceCorrect program tr'"
      if "transactionsArePackedMeasure tr' < transactionsArePackedMeasure tr"
      and "initialState program ~~ tr' \<leadsto>* S"
      for tr' S
    using Suc_leI that by blast
    
  
  show ?case
  proof (cases "transactionsArePackedMeasure tr")
    case 0
    text "If the measure is zero, transactions are already packed"
    hence "transactionsArePacked tr"
      by (simp add: transactionsArePackedMeasure_iff)
    thus ?thesis
      using tr_steps by blast
  next
    case (Suc n)
    
    text {*
      We can find the smallest i, such that the action is concurrent to another transaction
    *}
    from Suc
    obtain i 
      where i1: "i<length tr"
        and i2: "sessionsInTransaction tr i - {fst (tr!i)} \<noteq> {}"
      using not_packed_example2 by force
    
    obtain min_i
        where min_i_def: "min_i = (LEAST i. i<length tr \<and> sessionsInTransaction tr i - {fst (tr!i)} \<noteq> {})"
      by blast
      
    (*use one_compaction_step on min_i*)
    thm one_compaction_step2
      
    obtain min_s where min_s_def: "min_s = fst (tr!min_i)" by simp
    obtain min_a where min_a_def: "min_a = snd (tr!min_i)" by simp
    
    
      
    
    (*from min_i_def*)
    obtain trStart txa rest s tx 
      where tr_split: "tr = trStart @ (s, ABeginAtomic tx) # txa @ (min_s, min_a) # rest"
        and tr_split1: "length (trStart @ (s, ABeginAtomic tx) # txa) = min_i"
        and tr_split2: "(\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)"
        and tr_split3: "s \<noteq> fst (tr ! min_i)"
      apply atomize_elim
      apply (insert split_trace_min_i[OF min_i_def])
      apply auto
      by (metis Diff_eq_empty_iff i1 i2 min_a_def min_s_def prod.collapse)   
   
    have "min_s \<noteq> s"
      using min_s_def tr_split3 by auto
      
      
      
    obtain tr' where tr'_def:
      "tr' = trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ rest" by simp
    
    from tr_split2
    have tr_split2': "\<And>st at. (st, at) \<in> set txa \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic"
      by auto
      
    (* now, we can swap the min_i action before the beginAtomic action *)
    have tr'_steps_eq: "(initialState program ~~ tr \<leadsto>* S') \<longleftrightarrow> (initialState program ~~ tr' \<leadsto>* S')"
      using tr_split tr'_def tr_split2' proof (rule one_compaction_step3)
        show "\<And>st at. (st, at) \<in> set txa \<Longrightarrow> (st, at) \<in> set txa"
          by simp
        show "fst (min_s, min_a) \<noteq> s"
          by (simp add: \<open>min_s \<noteq> s\<close>)
        show "state_wellFormed (initialState program)"
          by simp
      qed
    hence tr'_steps: "initialState program ~~ tr' \<leadsto>* S'"
      using tr_steps by auto
      
      
    (* 
    the above preserves  the correctness of the trace...
    *) 
    have preservesCorrectness: "traceCorrect program tr' = traceCorrect program tr"
      proof (rule show_traceCorrect_same)
        show "set tr = set tr'"
          by (auto simp add: tr'_def tr_split )
        show "\<And>S. (initialState program ~~ tr \<leadsto>* S) \<longleftrightarrow> (initialState program ~~ tr' \<leadsto>* S)"
          using tr'_steps_eq tr_steps traceDeterministic by blast
      qed  
      
    
    (*
    this move also reduces our measure, which is probably the difficult thing to show
    *)  
    have measureDecreased: "transactionsArePackedMeasure tr' < transactionsArePackedMeasure tr"
    proof -
      thm  transactionsArePackedMeasure_append
      have "transactionsArePackedMeasure tr
         = transactionsArePackedMeasure (trStart @ (s, ABeginAtomic tx) # txa @ (min_s, min_a) # rest)"
        by (simp add: tr_split)
      
      moreover have "...
         = (\<Sum>i < length trStart. card (sessionsInTransaction trStart i - {fst (trStart ! i)}))
          + (\<Sum>i < 2 + length txa  + length rest.
              card (sessionsInTransaction (trStart @ (s, ABeginAtomic tx) # txa @ (min_s, min_a) # rest)
                     (length trStart + i) -
                    {fst (((s, ABeginAtomic tx) # txa @ (min_s, min_a) # rest) ! i)}))"
         by (simp add: transactionsArePackedMeasure_append)
      
      
      
    (* "tr = trStart @ (s, ABeginAtomic tx) # txa @ x # rest" *)
    
    then show ?thesis 
      using measureDecreased 
      by (meson "1.hyps" Suc_leI preservesCorrectness tr'_steps)
  qed
qed  



(*
lemma move_out_of_transaction:
assumes splitTrace: "tr = (s, ABeginAtomic tx) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx) # txa @ rest \<leadsto>* C)"
*)

(*
lemma one_compaction_step:
assumes splitTrace: "tr = tr1 @ [(s, ABeginAtomic tx)] @ txa @ [x] @ rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr1 @ [x] @ [(s, ABeginAtomic tx)] @ txa @ rest \<leadsto>* C)"
*)

(* TODO now we need to show, that we can move all actions out of transactions*)

theorem show_programCorrect_noTransactionInterleaving:
assumes packedTracesCorrect: 
  "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; transactionsArePacked trace\<rbrakk> \<Longrightarrow> traceCorrect program trace"
shows "programCorrect program"
proof (rule show_programCorrect) 
  text "Let tr be some trace such that program executes trace to s."
  fix tr s
  assume "initialState program ~~ tr \<leadsto>* s"
  
  text "Then there is a reshuffling of the trace, where transactions are not interleaved, but the final state is still the same."
  then obtain tr'  
    where "initialState program ~~ tr' \<leadsto>* s" 
      and "transactionsArePacked tr'"
      and "traceCorrect program tr' \<longleftrightarrow> traceCorrect program tr"
    using canPackTransactions by blast
  
  text "According to the assumption those traces are correct"
  with packedTracesCorrect
  have "traceCorrect program tr'"  
    by simp
  
  with `traceCorrect program tr' \<longleftrightarrow> traceCorrect program tr`
  show "traceCorrect program tr" ..
qed  



end

(* old stuf:

find_theorems "commutativeS"


lemma commutativePreservesPrecondition_rev:
assumes preconditionHolds: "precondition (sb,b) A"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommited: "transactionStatus A tx \<triangleq> Uncommited"
    and aIsInLocal: "localState A sa \<triangleq> lsa"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    and origin_inv: "dom (callOrigin A) = dom (calls A)"
shows "precondition (sb,b) B"
proof (cases b)
  case ALocal
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_alocal unchangedInTransaction(1) unchangedInTransaction(2)) 
next
  case (ANewId x2)
  then show ?thesis sorry
next
  case (ABeginAtomic x3)
  then show ?thesis sorry
next
  case AEndAtomic
  then show ?thesis
    by (metis aIsInTransaction differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis sorry
next
  case (APull x6)
  then show ?thesis 
     sorry
next
  case (AInvoc x71 x72)
  then show ?thesis 
    sorry
next
  case (AReturn x8)
  then show ?thesis
    by (metis (full_types) aIsInTransaction differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
    
next
  case AFail
  then show ?thesis
    by (simp add: precondition_fail) 
next
  case (AInvcheck x10)
  then show ?thesis
  proof - (* hammered *)
    obtain CC :: "state \<Rightarrow> bool \<Rightarrow> session \<Rightarrow> callId set" where
      "\<forall>x0 x1 x2. (\<exists>v3. currentTransaction x0 x2 = None \<and> visibleCalls x0 x2 \<triangleq> v3 \<and> invariant (prog x0) (invContext x0 x2) = x1) = (currentTransaction x0 x2 = None \<and> visibleCalls x0 x2 \<triangleq> CC x0 x1 x2 \<and> invariant (prog x0) (invContext x0 x2) = x1)"
      by moura
    then have f1: "\<forall>s b z. (\<not> precondition (s, AInvcheck b) z \<or> currentTransaction z s = None \<and> visibleCalls z s \<triangleq> CC z b s \<and> (\<not> invariant (prog z) (invContext z s)) \<noteq> b) \<and> (precondition (s, AInvcheck b) z \<or> (\<forall>C. currentTransaction z s \<noteq> None \<or> visibleCalls z s \<noteq> Some C \<or> (\<not> invariant (prog z) (invContext z s)) = b))"
      by (metis precondition_invcheck)
    then have f2: "currentTransaction A sb = None \<and> visibleCalls A sb \<triangleq> CC A x10 sb \<and> (\<not> invariant (prog A) (invContext A sb)) \<noteq> x10"
      using AInvcheck preconditionHolds by blast
    then have f3: "currentTransaction B sb = None"
    using aIsInTransaction differentSessions exec unchangedInTransaction(3) by auto
  have f4: "visibleCalls B sb \<triangleq> CC A x10 sb"
    using f2 aIsInTransaction differentSessions exec unchangedInTransaction(4) by auto
  have "invContext A sb = invContext B sb"
    by (meson aIsInLocal aIsInTransaction aIsNotCommit differentSessions exec origin_inv txIsUncommited unchangedInTransaction_getInvContext visibleCalls_inv)
  then have "invariant (prog A) (invContext A sb) = invariant (prog B) (invContext B sb)"
    using exec prog_inv by force
  then show ?thesis
    using f4 f3 f2 f1 AInvcheck by blast
qed
    
qed  
  
lemma 
assumes order1: "\<And>B1 B2. \<lbrakk>A ~~ (sa,a) \<leadsto> B1; B1 ~~ (sb,b) \<leadsto> C1; A ~~ (sb,b) \<leadsto> B2; B2 ~~ (sa,a) \<leadsto> C2\<rbrakk> \<Longrightarrow> C1 = C2" 
 and a1: "sa \<noteq> sb"
 and a2: "currentTransaction A sa \<triangleq> tx"
 and a3: "transactionStatus A tx \<triangleq> Uncommited"
 and a4: "localState A sa \<triangleq> lsa"
 and a5: "a \<noteq> AEndAtomic"
 and a6: "A ~~ (sa, a) \<leadsto> B"
 and a7: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
 and a8: "dom (callOrigin A) = dom (calls A)"
shows "(A ~~ [(sa,a),(sb,b)] \<leadsto>* C) \<longleftrightarrow> (A ~~ [(sb,b),(sa,a)] \<leadsto>* C)"
proof (auto simp add: steps_appendFront)
  fix B
  assume a0: "A ~~ (sa, a) \<leadsto> B"
     and a1: "B ~~ (sb, b) \<leadsto> C"

  from a1
  have "precondition (sb, b) B"
    using precondition_def by blast
  with commutativePreservesPrecondition
  have "precondition (sb, b) A"
    using a0 a2 a3 a4 a5 a7 a8 assms(2) by blast
    
  thus "\<exists>B. (A ~~ (sb, b) \<leadsto> B) \<and> (B ~~ (sa, a) \<leadsto> C)"
    apply (rule step_existsH)
    (*
    what we need here is the other direction as well: preconditions are preserved when moving something into a transaction
    
    alternatively I could also just prove one direction first
    *)
    
    
find_theorems "precondition"

lemma swapCommutative:
assumes differentSessions[simp]: "sa \<noteq> sb"
   and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
shows "(A ~~ [(sa,a),(sb,b)] \<leadsto>* C) \<longleftrightarrow> (A ~~ [(sb,b),(sa,a)] \<leadsto>* C)"
proof -
  have differentSessions2[simp]: "sb \<noteq> sa"
    using differentSessions by blast 
  show "?thesis"
    apply (case_tac a; case_tac b)
    apply (auto simp add: steps_appendFront elim!: step_elims)[1]
    apply (rule step_existsH)
    




end

*)
