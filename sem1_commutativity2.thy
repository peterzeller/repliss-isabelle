theory sem1_commutativity2
imports replissSem1 prefix
    "~~/src/HOL/Eisbach/Eisbach"
    execution_invariants
begin

lemma iffI2: "\<lbrakk>A \<Longrightarrow> B; \<not>A \<Longrightarrow> \<not>B\<rbrakk> \<Longrightarrow> A \<longleftrightarrow> B"
by auto

text {*
 The invocation info is set iff there was an invocation in the trace
*}
lemma invation_info_set_iff_invocation_happened:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
shows "(invocationOp S s = None) \<longleftrightarrow> (\<forall>proc args. (s, AInvoc proc args)\<notin> set tr )"
  and "\<forall>proc args. (invocationOp S s = Some (proc, args)) \<longleftrightarrow> ((s, AInvoc proc args) \<in> set tr )"
using steps proof (induct rule: steps_induct)
  case initial
  show "(invocationOp (initialState program) s = None) \<longleftrightarrow> (\<forall>proc args. (s, AInvoc proc args) \<notin> set [])"
    by (auto simp add: initialState_def)
  show "\<forall>proc args. invocationOp (initialState program) s \<triangleq> (proc, args) = ((s, AInvoc proc args) \<in> set [])"
    by (auto simp add: initialState_def)
next
  case (step S' tr a S'')
  
  show "(invocationOp S'' s = None) = (\<forall>proc args. (s, AInvoc proc args) \<notin> set (tr @ [a]))"
    using `S' ~~ a \<leadsto> S''` apply (induct rule: step.cases)
    using step.IH(1) by auto
  
  show "\<forall>proc args. invocationOp S'' s \<triangleq> (proc, args) = ((s, AInvoc proc args) \<in> set (tr @ [a]))"
    using `S' ~~ a \<leadsto> S''` apply (induct rule: step.cases)
    using step.IH(2) by auto
qed

lemma invocation_ops_if_localstate_nonempty:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and loc: "localState S s \<noteq> None"
shows "invocationOp S s \<noteq> None" 
using assms proof (induct arbitrary:   rule: steps_induct)
  case initial
  then show ?case
    by (simp add: initialState_def) 
next
  case (step S' tr a S'')
  
  show ?case
  proof (cases "fst a = s")
    case True
    from this obtain action where [simp]: "a = (s, action)"
      using surjective_pairing by blast 
    show ?thesis 
    using `S' ~~ a \<leadsto> S''` proof (induct rule: step.cases)
      case (local C s ls f ls')
      then show ?case using step.IH by (auto simp add: True)
    next
      case (newId C s ls f ls' uid)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (beginAtomic C s ls f ls' t)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (endAtomic C s ls f ls' t)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (dbop C s ls f Op args ls' t c res vis)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (invocation C s procName args initialState impl)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (return C s ls f res)
      then show ?case  using step.IH by (auto simp add: True)
    next
      case (fail C s')
      with `localState S'' s \<noteq> None` have False
        by auto
      thus ?case ..
    next
      case (invCheck C s' vis res)
      then show ?case  using step.IH
        using step.prems by blast 
    qed
  next
    case False hence [simp]: "fst a \<noteq> s" .
    from `S' ~~ a \<leadsto> S''`
    have "localState S'' s = localState S' s" and "invocationOp S'' s = invocationOp S' s"
      using False by (induct rule: step.cases, auto)
    
    thus ?thesis
      using step.IH step.prems by auto 
  qed
qed
      

text {*
 After a fail or return the local state is None
*}
lemma everything_starts_with_an_invocation:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and fail_or_return: "tr!i = (s, AFail) \<or> tr!i = (s, AReturn res)"
    and i_in_range: "i < length tr"
shows "localState S s = None \<and> invocationOp S s \<noteq> None" 
using steps fail_or_return i_in_range
proof (induct rule: steps_induct)
  case initial
  then show ?case
    by simp 
next
  case (step S' tr a S'')
  
  hence steps'': "initialState program ~~ (tr@[a]) \<leadsto>* S''"
    using steps_step by blast
    
    
  
  show ?case 
  proof (cases "i < length tr")
    case True
    hence "tr ! i = (s, AFail) \<or> tr ! i = (s, AReturn res)"
      using `(tr @ [a]) ! i = (s, AFail) \<or> (tr @ [a]) ! i = (s, AReturn res)`
      by (auto simp add: nth_append)
    hence "localState S' s = None"
      by (simp add: True step.IH) 
      
    show ?thesis 
      using `S' ~~ a \<leadsto> S''` 
      apply (induct rule: step.cases)
      using True \<open>tr ! i = (s, AFail) \<or> tr ! i = (s, AReturn res)\<close> step.IH by auto
  next
    case False
    show ?thesis 
    proof (cases "i = length tr")
      case True
      with `(tr @ [a]) ! i = (s, AFail) \<or> (tr @ [a]) ! i = (s, AReturn res)`
      have cases: "a = (s, AFail) \<or> a = (s, AReturn res)"
        by simp
        
        
      thus ?thesis 
      proof (rule; intro conjI)
        assume "a = (s, AFail)"
        hence "S' ~~ (s, AFail) \<leadsto> S''"
          using step.step by auto
          
          
        thus "localState S'' s = None"
          by (auto simp add: step_simp_AFail)
          (*
        hence "invocationOp S'' s \<noteq> None" 
          using invocation_ops_if_localstate_nonempty[OF steps'']
          *)
          
        have "localState S' s \<noteq> None"
        using `S' ~~ (s, AFail) \<leadsto> S''` 
          by (induct rule: step.cases, auto)
        
        hence "invocationOp S' s \<noteq> None"
          using invocation_ops_if_localstate_nonempty step.steps by blast
        thus "invocationOp S'' s \<noteq> None"  
          using `S' ~~ (s, AFail) \<leadsto> S''` invation_info_set_iff_invocation_happened(1) step.steps steps''
          by (metis butlast_snoc in_set_butlastD)  
      next 
        assume "a = (s, AReturn res)"
        hence "S' ~~ (s, AReturn res) \<leadsto> S''"
          using step.step by auto
        thus "localState S'' s = None"
          by (auto simp add: step_simp_AReturn)
          
        from `S' ~~ (s, AReturn res) \<leadsto> S''`  
        show "invocationOp S'' s \<noteq> None"
          using invocation_ops_if_localstate_nonempty step.steps step_simp_AReturn
          by (metis butlast_snoc in_set_butlastD invation_info_set_iff_invocation_happened(1) option.distinct(1) steps'') 
      qed    
      
    next
      case False
      with `\<not> (i < length tr)` have "i > length tr" by arith
      then show ?thesis
        using step.prems(2) by auto 
    qed
  qed
qed  
  

text {*
 We have visible calls iff we have some local state.
*}
lemma visibleCalls_iff_localState:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
shows "localState S s = None \<longleftrightarrow> visibleCalls S s = None" 
using steps 
proof (induct rule: steps_induct)
  case initial
  then show ?case
    by (simp add: initialState_def)
next
  case (step S' tr a S'')
  from `S' ~~ a \<leadsto> S''`
  show ?case 
  apply (rule step.cases)
  using step.IH  by (auto simp add: step)
qed

text {*
 There can be no action on a invocation after a fail or return:
 (except for invariant checks)
*}
lemma nothing_after_fail_or_return:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
 and fail_or_return: "tr!i = (s, AFail) \<or> tr!i = (s, AReturn res)"
 and i_in_range: "i < length tr"
shows "\<nexists>j. j>i \<and> j<length tr \<and> fst(tr!j) = s \<and> \<not>is_AInvcheck (snd (tr!j))" 
using steps fail_or_return i_in_range proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'')
  show "\<not> (\<exists>j>i. j < length (tr @ [a]) \<and> fst ((tr @ [a]) ! j) = s \<and> \<not> is_AInvcheck (snd ((tr @ [a]) ! j)))"
  proof (rule ccontr, auto)
    fix j
    assume a1: "j < Suc (length tr)"
       and a2: "i < j"
       and a3: "s = fst ((tr @ [a]) ! j)"
       and a4: "\<not> is_AInvcheck (snd ((tr @ [a]) ! j))"
       
    have j_def: "j = length tr"
    proof (rule ccontr)
      assume "j \<noteq> length tr"
      hence "j < length tr" using a1 by simp
      hence "s \<noteq> fst ((tr @ [a]) ! j)"
        by (metis a2 a4 length_append_singleton less_Suc_eq nth_append order.asym step.IH step.prems(1) step.prems(2))
      with a3 show False by simp
    qed
    
    obtain a_op where a_def: "a = (s, a_op)" using j_def a3
      by (metis nth_append_length prod.collapse) 
    
    
    
    from `(tr @ [a]) ! i = (s, AFail) \<or> (tr @ [a]) ! i = (s, AReturn res)`
    have no_ls: "localState S' s = None" 
     and op: "invocationOp S' s \<noteq> None"  
      apply (metis a2 everything_starts_with_an_invocation j_def nth_append step.steps)
      by (metis a2 everything_starts_with_an_invocation j_def nth_append step.prems(1) step.steps)
     
    have fst_a: "fst a = s" using a_def by simp  
    
    from `S' ~~ a \<leadsto> S''` a_def
    have "S' ~~ (s, a_op) \<leadsto> S''" by simp  

    thus False
      apply (rule step.cases)
      apply (auto simp add: no_ls a3 op j_def)
      apply (auto simp add: fst_a no_ls op)
      using a4 a_def is_AInvcheck_def j_def by auto 
    qed
qed

(*
text {*
After a return or a failure no more actions on the same invocation are possible.
*}
lemma nothing_after_fail_or_return:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
 and fail_or_return: "tr!i = (s, AFail) \<or> tr!j = (s, AReturn res)"
shows "\<nexists>j. j>i \<and> fst(tr!j) = s" 
*)

lemma trace_simulationProof[consumes 1, case_names initial f_empty_to_empty induct_step[coupling steps1 steps2 step]]:
assumes steps_tr: "init ~~ tr \<leadsto>* S"
    and P_initial: "P [] [] init init"
    and f_empty_to_empty: "f [] = []"
    and induct_step: "\<And>tr a S1 S2 S1'. \<lbrakk>P tr (f tr) S1 S2; init ~~ tr \<leadsto>* S1; init ~~ f tr \<leadsto>* S2; S1 ~~ a \<leadsto> S1'\<rbrakk> 
      \<Longrightarrow> \<exists>S2'. (init ~~ f (tr@[a]) \<leadsto>* S2') \<and> P (tr@[a]) (f (tr@[a])) S1' S2'"
shows "\<exists>S'. (init ~~ f tr \<leadsto>* S') \<and>  P tr (f tr) S S'"
using steps_tr proof (induct rule: steps_induct)
  case initial
  show ?case
    by (simp add: f_empty_to_empty P_initial) 
next
  case (step S' tr a S'')
  from this
  obtain S1' 
    where S1'_step: "init ~~ f tr \<leadsto>* S1'" 
      and S1'_P: "P tr (f tr) S' S1'"
    by blast
  
  from induct_step[OF S1'_P `init ~~ tr \<leadsto>* S'` S1'_step ` S' ~~ a \<leadsto> S''`]  
  obtain S2' 
    where S2'_steps: "init ~~ f (tr @ [a]) \<leadsto>* S2'"
      and S2'_P: "P (tr @ [a]) (f (tr @ [a])) S'' S2'"
      by blast
  
  thus " \<exists>S'. (init ~~ f (tr @ [a]) \<leadsto>* S') \<and> P (tr @ [a]) (f (tr @ [a])) S'' S'"
    by blast
qed


definition 
"isAFail a \<equiv> case a of AFail \<Rightarrow> True | _ \<Rightarrow> False"

schematic_goal [simp]: "isAFail (ALocal) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ANewId u) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ABeginAtomic t newTxns) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AEndAtomic) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ADbOp c oper args res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvoc pname args) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AReturn res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AFail) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvcheck t c) = ?x" by (auto simp add: isAFail_def)                            

lemma exI_eq: 
assumes "P y True"
shows "\<exists>x. P x (x = y)"
using assms by (metis (full_types))


lemma can_ignore_fails:
shows "(\<forall>tr\<in>traces program. traceCorrect tr) 
  \<longleftrightarrow> (\<forall>tr\<in>traces program. (\<nexists>s. (s, AFail) \<in> set tr) \<longrightarrow>  traceCorrect tr)"
proof (rule iffI2; clarsimp)
  fix tr
  assume is_trace: "tr \<in> traces program"
     and tr_fail: "\<not> traceCorrect tr"
  
  from this obtain s txns S' where "(s, AInvcheck txns False) \<in> set tr" and "initialState program ~~ tr \<leadsto>* S'"
    by (auto simp add: traceCorrect_def traces_def)  
    
  
  text {*
  Idea: a failed node and a node without progress are not really distinguishable in practice.
  In our semantics there are two small differences:
  
  1) state is different after failure
  *}
  
  show "\<exists>tr\<in>traces program. (\<forall>s. (s, AFail) \<notin> set tr) \<and> \<not> traceCorrect tr"
  proof (rule bexI[where x="[x\<leftarrow>tr . \<not>isAFail (snd x)]"], intro conjI allI)
  
    show "\<And>s. (s, AFail) \<notin> set [x\<leftarrow>tr . \<not>isAFail (snd x)]"
      by (auto simp add: isAFail_def)
      
    show "\<not> traceCorrect [tr\<leftarrow>tr . \<not> isAFail (snd tr)]"
      using tr_fail by (auto simp add: traceCorrect_def isAFail_def) 
    
    thm state_ext  
      
    from `initialState program ~~ tr \<leadsto>* S'`
    have "\<exists>S''. (initialState program ~~ [tr\<leftarrow>tr . \<not> isAFail (snd tr)] \<leadsto>* S'') 
        \<and> (
           calls S'' = calls S'
         \<and> happensBefore S'' = happensBefore S'
         \<and> prog S'' = prog S'
         \<and> transactionStatus S'' = transactionStatus S' 
         \<and> callOrigin S'' = callOrigin S' 
         \<and> transactionOrigin S'' = transactionOrigin S' 
         \<and> generatedIds S'' = generatedIds S' 
         \<and> knownIds S'' = knownIds S' 
         \<and> invocationOp S'' = invocationOp S' 
         \<and> invocationRes S'' = invocationRes S'
         \<and> (\<forall>s. (s, AFail) \<notin> set tr \<longrightarrow> ( 
             localState S'' s = localState S' s
           \<and> currentTransaction S'' s = currentTransaction S' s
           \<and> currentProc S'' s = currentProc S' s
           \<and> visibleCalls S'' s = visibleCalls S' s 
         ))
        )"
    proof (induct rule: trace_simulationProof)
      case initial
        thus ?case by auto
      next
        case f_empty_to_empty
        thus ?case by auto
      next
      case (induct_step tr a S1 S2 S1')
      from steps_append2[OF induct_step.steps2]
      have [simp]: "(initialState program ~~ [tr\<leftarrow>tr . \<not> isAFail (snd tr)] @ trb \<leadsto>* C) \<longleftrightarrow> (S2 ~~ trb \<leadsto>* C)" for trb C .
        
      
      from `S1 ~~ a \<leadsto> S1'`
      show ?case 
      proof (cases rule: step.cases)
        case (local s ls f ls')

        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr>"])
          using induct_step.coupling no_fail local
          apply (intro conjI)
          by (auto simp add: step_simps state_ext local induct_step)
      next
        case (newId s ls f ls' uid)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls' uid), generatedIds := generatedIds S2 \<union> {uid}\<rparr>"])
          using induct_step.coupling no_fail newId
          by (auto simp add: step_simps state_ext  induct_step)
          
      next
        case (beginAtomic s ls f ls' t vis newTxns newCalls snapshot)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
        
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>
                localState := localState S2(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S2(s \<mapsto> t), 
                transactionStatus := transactionStatus S1(t \<mapsto> Uncommited),
                transactionOrigin := transactionOrigin S2(t \<mapsto> s),
                visibleCalls := visibleCalls S2(s \<mapsto> vis \<union> newCalls)\<rparr>"])
          using induct_step.coupling no_fail beginAtomic
          by (auto simp add: step_simps state_ext  induct_step)
          
      next
        case (endAtomic s ls f ls' t)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S1(t \<mapsto> Commited)\<rparr>"])
          using induct_step.coupling no_fail endAtomic
          by (auto simp add: step_simps state_ext  induct_step)
      next
        case (dbop s ls f Op args ls' t c res vis)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls' res), calls := calls S2(c \<mapsto> Call Op args res), callOrigin := callOrigin S1(c \<mapsto> t), visibleCalls := visibleCalls S2(s \<mapsto> vis \<union> {c}), happensBefore := happensBefore S1 \<union> vis \<times> {c}\<rparr>"])
          using induct_step.coupling no_fail dbop
          by (auto simp add: step_simps state_ext  induct_step)

      next
        case (invocation s procName args initialLocalState impl)
        from `initialState program ~~ tr \<leadsto>* S1` `invocationOp S1 s = None`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (meson everything_starts_with_an_invocation in_set_conv_nth)
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> initialLocalState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"])
          using induct_step.coupling no_fail invocation
          by (auto simp add: step_simps state_ext  induct_step)
      next
        case (return s ls f res)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S1(s \<mapsto> res), knownIds := knownIds S1 \<union> uniqueIds res\<rparr>"])
          using induct_step.coupling no_fail return
          by (auto simp add: step_simps state_ext  induct_step)
      next
        case (fail s ls)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
        show ?thesis 
          apply (rule exI[where x="S2"])
          by (auto simp add: step_simps state_ext  induct_step  fail)
                    
      next
        case (invCheck txns res s)
          
        show ?thesis 
          apply (rule exI[where x="S2"])
          using induct_step.coupling  invCheck
          by (auto simp add: step_simps state_ext  induct_step)
      qed
    qed
      
      
    thus "[tr\<leftarrow>tr . \<not> isAFail (snd tr)] \<in> traces program"
      by (auto simp add: traces_def)
  qed
qed
  

definition commutativeS :: "('localState, 'any) state \<Rightarrow> invocation \<times> 'any action \<Rightarrow> invocation \<times> 'any action \<Rightarrow> bool" where
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

definition differentIds :: "(invocation \<times> 'any action) \<Rightarrow> (invocation \<times> 'any action) \<Rightarrow> bool" where
"differentIds a b \<equiv> case (a,b) of
   ((s1, ANewId u1), (s2, ANewId u2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ABeginAtomic u1 nt1), (s2, ABeginAtomic u2 nt2)) \<Rightarrow> (u1 \<noteq> u2)
 | ((s1, ADbOp u1 o1 a1 r1), (s2, ADbOp u2 o2 a2 r2)) \<Rightarrow> (u1 \<noteq> u2)
 | _ \<Rightarrow> True"
 
lemma differentIds_newId[simp]:
"differentIds (s1, ANewId u1) (s2, ANewId u2) \<longleftrightarrow> (u1 \<noteq> u2)"
by (simp add: differentIds_def)

lemma differentIds_beginAtomic[simp]:
"differentIds (s1, ABeginAtomic u1 nt1) (s2, ABeginAtomic u2 nt2) \<longleftrightarrow> (u1 \<noteq> u2)"
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
    using steps_to_differentIds2 by blast
  
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
"precondition (s, ABeginAtomic tx newTxns) C = 
    (\<exists>ls f ls'. 
        localState C s \<triangleq> ls 
      \<and> currentProc C s \<triangleq> f 
      \<and> f ls = BeginAtomic ls' 
      \<and> currentTransaction C s = None 
      \<and> transactionStatus C tx = None
      \<and> visibleCalls C s \<noteq> None
      \<and> newTxns \<subseteq> commitedTransactions C)"
by (auto simp add: precondition_def step_simps )

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



lemma precondition_return:
"precondition (s, AReturn res) C = (\<exists>ls f. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = Return res \<and> currentTransaction C s = None)"
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_fail:
"precondition (s, AFail) C = (\<exists>ls. localState C s \<triangleq> ls)" (* failures occur wherever something is running ;) *)
apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
done

lemma precondition_invcheck:
"precondition (s, AInvcheck txns res) C = ((\<forall>t\<in>txns. transactionStatus C t \<triangleq> Commited) \<and> res = invariant (prog C) (invContextSnapshot C txns))"
apply (auto simp add: precondition_def step_simps intro: step.intros elim!: step_elims)
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
using exec apply (auto simp add: differentSessions[symmetric] elim!: step_elim_general)
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
        by (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def B_def)
      show "i_invocationOp (invContext A sb) = i_invocationOp (invContext B sb)"
        by (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def B_def)
      show "i_invocationRes (invContext A sb) = i_invocationRes (invContext B sb)"
        by (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def B_def)
      show "i_transactionOrigin (invContext A sb) = i_transactionOrigin (invContext B sb)"
        by (auto simp add: invContextH_def commitedSame commitedCallsSame restrict_map_def B_def)
    qed
    
  
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

lemma generatedIds_mono2_rev:
"\<lbrakk>x\<notin>generatedIds B; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> x\<notin>generatedIds A"
  by (meson generatedIds_mono2)

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






lemma committed_same: 
assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
shows "transactionStatus A t \<triangleq> Commited \<longleftrightarrow> transactionStatus B t \<triangleq> Commited" 
    using exec apply (rule step.cases)
    by (auto simp add: aIsNotCommit)    
    
lemma happensBefore_same_committed2: 
assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Commited " 
    and orig_y: "callOrigin A y \<triangleq> tx"
shows "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
    using exec apply (rule step.cases)
    using wellFormed committed orig_y by auto      
    
lemma invContextSame_h: 
assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Commited"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
shows "(callsInTransaction A txns \<down> happensBefore A) = (callsInTransaction B txns \<down> happensBefore B)"
apply (auto simp add: callsInTransactionH_def downwardsClosure_in)
   apply (metis "1" aIsNotCommit callOrigin_same_committed exec snd_conv transactionStatus_mono2 wellFormed)
  apply (metis (mono_tags, lifting) "1" aIsNotCommit callOrigin_same_committed exec happensBefore_same_committed2 snd_conv transactionStatus_mono2 wellFormed)
 apply (metis "1" aIsNotCommit callOrigin_same_committed exec snd_conv transactionStatus_mono2 wellFormed)
by (metis (no_types, lifting) "1" aIsNotCommit callOrigin_same_committed exec happensBefore_same_committed2 snd_eqD transactionStatus_mono2 wellFormed)

lemma inTransaction_localState:
assumes wf: "state_wellFormed A"
    and tx: "currentTransaction A s \<triangleq> tx"
shows "localState A s \<noteq> None"
using wf tx apply (induct arbitrary: s tx rule: wellFormed_induct )
apply (auto simp add: initialState_def)
apply (erule step.cases)
apply (auto split: if_splits)
done



lemma invContextSnapshot_same: 
assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Commited"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommited: "transactionStatus A tx \<triangleq> Uncommited"
shows "(invContextSnapshot A txns) = (invContextSnapshot B txns)"
proof (auto simp add: invContextH_def invContextSame_h[OF exec wellFormed 1 aIsNotCommit])
  have committed_same: "commitedCalls B = commitedCalls A"
    using exec apply (rule step.cases)
    apply (auto simp add: commitedCallsH_def aIsNotCommit wellFormed)
    apply force
    done
    
  have committed_subset: "commitedCalls A \<subseteq> dom (calls A)"
    apply (auto simp add: commitedCallsH_def aIsNotCommit wellFormed)
    using wellFormed wellFormed_callOrigin_dom by fastforce
    
  
    
  show "calls A |` commitedCalls A = calls B |` commitedCalls B"
    using exec apply (rule step.cases)
    apply (auto simp add: commitedCallsH_def aIsInTransaction aIsNotCommit )
    apply (metis option.inject transactionStatus.distinct(1) txIsUncommited)
    by (metis (no_types, lifting) option.distinct(1) wellFormed wellFormed_callOrigin_dom2)
  
  show "\<And>a b. (a, b) \<in> happensBefore A |r commitedCalls A \<Longrightarrow> (a, b) \<in> happensBefore B |r commitedCalls B"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
    by (auto simp add: restrict_relation_def commitedCallsH_def)
    
  
  show "\<And>a b. (a, b) \<in> happensBefore B |r commitedCalls B \<Longrightarrow> (a, b) \<in> happensBefore A |r commitedCalls A"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
    by (auto simp add: restrict_relation_def commitedCallsH_def wellFormed)
    
  show "callOrigin A |` commitedCalls A = callOrigin B |` commitedCalls B"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
    apply (auto simp add:  commitedCallsH_def )
    by (meson domI domIff wellFormed wellFormed_callOrigin_dom2)
    
    
  show "\<And>x. x \<in> knownIds A \<Longrightarrow> x \<in> knownIds B"
    using exec apply (rule step.cases)
    by auto
    
  show "\<And>x. x \<in> knownIds B \<Longrightarrow> x \<in> knownIds A"
    using exec apply (rule step.cases)
    apply auto
    by (simp add: aIsInTransaction)
    
  from wellFormed and aIsInTransaction
  have "localState A sa \<noteq> None"
    by (simp add: inTransaction_localState)
    
    
  show "invocationOp A = invocationOp B"
    using exec apply (rule step.cases)
    apply auto
    using \<open>localState A sa \<noteq> None\<close> by blast
    
  show "invocationRes A = invocationRes B"
    using exec apply (rule step.cases)
    by (auto simp add: aIsInTransaction)
    
    
  have "transactionOrigin A t = transactionOrigin B t"  for t
    using exec apply (rule step.cases)
    by (auto simp add: aIsInTransaction)
    
  
  show "transactionOrigin A |` commitedTransactions A = transactionOrigin B |` commitedTransactions B"
    using exec apply (rule step.cases)
    apply (auto simp add: restrict_map_def aIsInTransaction)
    using aIsNotCommit exec sem1_commutativity2.committed_same by auto[1]
    
    
    
qed    
  
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
 
  from exec
  have committed_same: "transactionStatus A t \<triangleq> Commited \<longleftrightarrow> transactionStatus B t \<triangleq> Commited" for t
    using aIsNotCommit committed_same by blast
    
  from exec
  have callOrigin_same_committed: "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx" if "transactionStatus A tx \<triangleq> Commited " for c tx
    using callOrigin_same_committed that wellFormed by blast    

  from exec
  have happensBefore_same_committed2: "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
        if "transactionStatus A tx \<triangleq> Commited " 
        and "callOrigin A y \<triangleq> tx"
        for tx x y
    using that happensBefore_same_committed2 wellFormed by blast 
    
show ?thesis
proof (cases b)
  case ALocal
  show ?thesis using precondition_alocal unchangedInTransaction
    by (metis ALocal differentSessions exec preconditionHolds) 
    
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
    using generatedIds_mono2_rev[OF 3 exec] by blast
  thus ?thesis
    by (metis "1" "2" "4" ANewId differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
next
  case (ABeginAtomic tx newTxns)
  with preconditionHolds obtain ls f ls' vis
      where 1: "localState B sb \<triangleq> ls"
        and 2: "currentProc B sb \<triangleq> f"
        and 3: "f ls = BeginAtomic ls'"
        and 4: "currentTransaction B sb = None"
        and 5: "transactionStatus B tx = None"
        and 6: "newTxns \<subseteq> commitedTransactions B"
        and 7: "visibleCalls B sb \<triangleq> vis"
    by (auto simp add: precondition_beginAtomic)
  moreover have "transactionStatus A tx = None" using transactionStatus_mono 5 exec by blast 
  ultimately show ?thesis using unchangedInTransaction
    by (smt ABeginAtomic aIsNotCommit contra_subsetD differentSessions exec mem_Collect_eq option.distinct(1) precondition_beginAtomic snd_conv subsetI transactionStatus_mono2)
next
  case AEndAtomic
  then show ?thesis
    by (metis differentSessions exec preconditionHolds precondition_endAtomic unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3))
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
    by (smt AInvoc aIsInTransaction differentSessions exec precondition_invoc prog_inv)
next
  case (AReturn x8)
  then show ?thesis
    by (metis differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case AFail
  then show ?thesis
    by (metis differentSessions exec preconditionHolds precondition_fail unchangedInTransaction(1))
next
  case (AInvcheck txns res)
  with preconditionHolds 
  have 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Commited"
   and 2: "res = invariant (prog B) (invContextSnapshot B txns)"
    by (auto simp add: precondition_invcheck)
  
  have invContextSame_h: "(callsInTransaction A txns \<down> happensBefore A) = (callsInTransaction B txns \<down> happensBefore B)"
    apply (auto simp add: callsInTransactionH_def downwardsClosure_in "1" callOrigin_same_committed committed_same)
    using "1" callOrigin_same_committed committed_same happensBefore_same_committed2 by blast+
  
  have invContextSame: "(invContextSnapshot A txns) = (invContextSnapshot B txns)"
    using "1" aIsInTransaction aIsNotCommit exec invContextSnapshot_same txIsUncommited wellFormed by blast
    
  moreover have "invContext A sb = invContext B sb"
    using unchangedInTransaction_getInvContext[OF differentSessions aIsInTransaction aIsInLocal txIsUncommited aIsNotCommit exec ] origin_inv  visibleCalls_inv   by blast 

  have "precondition (sb, AInvcheck txns res) A"  
    using prog_inv[OF exec] by (auto simp add: precondition_invcheck "1" committed_same 2 invContextSame)
      
  
  thus ?thesis
    using AInvcheck by blast  
    
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
shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs
    = invContextH co to ts hbOld cs ki io ir vcs"
apply (simp add: invContextH_def)
using assms apply (auto simp add: restrict_relation_def commitedCallsH_def)
done  

lemma invContext_unchanged_happensBefore2[simp]:
assumes "co c = None"
shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs 
    = invContextH co to ts hbOld cs ki io ir vcs "
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
shows "i_visibleCalls (invContextH co to ts hbOld cs ki io ir vcs )
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
shows "invContextH (co(c \<mapsto> t)) to ts hb cs ki io ir vis  =
       invContextH co to ts hb cs ki io ir vis "
using assms by (auto simp add: invContextH_def)

lemma invContextH_update_calls[simp]:
assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommited"
shows "invContextH co to ts hb (cs(c \<mapsto> newCall)) ki io ir vis  =
       invContextH co to ts hb cs ki io ir vis "
using assms by (auto simp add: invContextH_def commitedCallsH_in)

lemma commitedCallsH_update_uncommited[simp]:
assumes "ts t = None"
shows "commitedCallsH co (ts(t \<mapsto> Uncommited))
     = commitedCallsH co ts"
using assms apply (auto simp add: commitedCallsH_def)
  by force


lemma invContextH_update_txstatus[simp]:
assumes "ts t = None" 
shows "invContextH co to (ts(t\<mapsto>Uncommited)) hb cs ki io ir vis =
       invContextH co to ts hb cs ki io ir vis"
using assms by (auto simp add: invContextH_def restrict_map_def)

lemma test:
fixes S:: "('localState, 'any) state"
assumes a7: "currentTransaction S sa \<triangleq> t"
assumes a10: "state_wellFormed S"
assumes a11: "sb\<noteq>sa"
assumes a12: "calls S c = None"
shows "invContext
           (S\<lparr>localState := localState S(sa \<mapsto> ls' res), calls := calls S(c \<mapsto> Call operation args res),
                callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis),
                happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
           sb
  = invContext S sb"
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
  case (AInvcheck txns res)
  with a2 show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    by (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist subset_eq)
next
  case (ADbOp c' operation' args' res')
  with a2 show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres2)
    apply (auto simp add: precondition_dbop)
    by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits, auto simp add: state_ext)
next
next
  case (ABeginAtomic tx txns)
  hence a_def[simp]: "a = ABeginAtomic tx txns" .
(*  case (APull txns) *)
  show ?thesis
  proof (induct rule: show_commutativeS_pres2)
    case (preBfront s1)
    then show "precondition (sb, a) S" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps split: if_splits)
  next
    case (preAfront s1)
    then show "precondition (sa, ADbOp c operation args res) S" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps)
  next
    case (preAback s1)
    then show "precondition (sa, ADbOp c operation args res) s1" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps)
  next
    case (preBback s1)
    then show "precondition (sb, a) s1" 
      by (auto simp add: precondition_dbop precondition_beginAtomic step_simps)
  next
    case (commute s1 s2 s1' s2')
    hence step1: "S ~~ (sa, ADbOp c operation args res) \<leadsto> s1"
      and step2: "s1 ~~ (sb, ABeginAtomic tx txns) \<leadsto> s2"
      and step3: "S ~~ (sb, ABeginAtomic tx txns) \<leadsto> s1'"
      and step4: "s1' ~~ (sa, ADbOp c operation args res) \<leadsto> s2'"
        by auto
    show "s2 = s2'" 
    apply (subst state_ext)
    using a2 step1 step2 step3 step4  
    by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits) (* takes long*)
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
  and not_invCheck: "\<not>is_AInvcheck a"
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
      then show ?thesis  
        apply (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction )
        by (metis a_is_in_transaction b_is_a_different_session option.simps(3) unchangedInTransaction(3))
    next
      case AEndAtomic
      then show ?thesis using not_endAtomic by simp
    next
      case (ADbOp x51 x52 x53 x54)
      then show ?thesis  by simp
    next
      case (AInvoc x71 x72)
      then show ?thesis 
        (*apply (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction wellFormed_invoc_notStarted)*)
        apply (auto simp add: commutativeS_def steps_appendFront)
        apply (metis a_is_in_transaction local.wf option.distinct(1) preconditionI precondition_invoc wellFormed_invoc_notStarted(1))
        by (metis a_is_in_transaction b_is_a_different_session local.wf option.distinct(1) preconditionI precondition_invoc unchangedInTransaction(5) wellFormed_invoc_notStarted(1))
    next
      case (AReturn x8)
      then show ?thesis   
        apply (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction)
        by (metis a_is_in_transaction b_is_a_different_session option.distinct(1) unchangedInTransaction(3))
      
    next
      case AFail
      then show ?thesis  by simp
    next
      case (AInvcheck txns res)
      then show ?thesis
        using is_AInvcheck_def not_invCheck by auto   
    qed
qed

lemma move_transaction2:
assumes a_is_in_transaction: "currentTransaction S (fst a) \<triangleq> t"
  and b_is_a_different_session[simp]: "fst a \<noteq> fst b"
  and not_endAtomic: "snd a \<noteq> AEndAtomic"
  and not_invCheck: "\<not>is_AInvcheck (snd a)"
  and wf[simp]: "state_wellFormed S"
shows "(S ~~ a#b#xs \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)"
proof -
  have "(S ~~ a#b#xs \<leadsto>* T) \<longleftrightarrow> (\<exists>S'. (S ~~ [a,b] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    using steps_appendFront by auto
  moreover have "... \<longleftrightarrow> (\<exists>S'. (S ~~ [b,a] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    by (metis a_is_in_transaction b_is_a_different_session local.wf move_transaction not_endAtomic prod.collapse not_invCheck)
  moreover have "... \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)" 
    using steps_appendFront by auto
  ultimately show ?thesis
    by blast 
qed   

lemma commutative_beginAtomic_other[simp]:
assumes a1[simp]: "sa \<noteq> sb"
    and a2: "state_wellFormed S"
    and no_end_atomic: "a \<noteq> AEndAtomic" 
shows "commutativeS S (sa, ABeginAtomic t newTxns) (sb, a)"
proof -
have a1'[simp]: "sb \<noteq> sa" using a1 ..
show "?thesis"
proof (cases a)
  case ALocal
  then show ?thesis
    by simp 
next
  case (ANewId x2)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_newId_other
    by metis 
next
  case (ABeginAtomic t txns)
  show ?thesis 
    apply  (rule show_commutativeS)
    using ABeginAtomic apply (auto simp add: step_simps contra_subsetD split: if_splits)[1]
    using ABeginAtomic   apply (auto simp add: step_simps contra_subsetD split: if_splits)[1]
    apply (subst state_ext)
    using ABeginAtomic   apply (auto simp add: step_simps)
    using fun_upd_twist map_upd_nonempty by force
   
next
  case AEndAtomic (* this is not commutative, since the transaction committed could be included in ht next snapshot*)
  thus ?thesis
    using no_end_atomic by auto 
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_Dbop_other by presburger 
(**next
  case (APull x6)
  then show ?thesis 
  by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute,
    auto, smt mem_Collect_eq option.inject subsetCE transactionStatus.distinct(1))*)
next
  case (AInvoc x71 x72)
  then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits)
next
  case (AReturn x8)
  then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits)
next
  case AFail
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_fail_other by presburger 
next
  case (AInvcheck x10)
  then show ?thesis 
    by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits, auto simp add: invContextH_def)
qed
qed


lemma move_outside_transaction:
assumes b_is_a_different_session[simp]: "sa \<noteq> sb"
  and wf[simp]: "state_wellFormed S"
  and no_end_atomic: "b \<noteq> AEndAtomic" 
shows "(S ~~ [(sa,ABeginAtomic t newTxns),(sb,b)] \<leadsto>* T) 
   \<longleftrightarrow> (S ~~ [(sb,b),(sa,ABeginAtomic t newTxns)] \<leadsto>* T)"
proof (rule useCommutativeS)
  show "commutativeS S (sa, ABeginAtomic t newTxns) (sb, b)"
    using assms by (rule commutative_beginAtomic_other)
qed
  
 


(* todo and now move everything out of transactions ... *)

lemma show_programCorrect:
assumes "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s \<rbrakk> \<Longrightarrow> traceCorrect trace"
shows "programCorrect program"
  by (auto simp add: assms programCorrect_def traces_def)

lemma currentTransaction_unchangedInternalSteps:
assumes "S ~~ tr \<leadsto>* S'"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AEndAtomic"
  and "\<And>a tx ntxns.  a \<in> set tr \<Longrightarrow> snd a \<noteq> ABeginAtomic tx ntxns"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AFail"
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
    case (AInvoc x71 x72)
    then show ?thesis using steps_step by (case_tac a, auto simp add: step_simps)
  next
    case (AReturn x8)
    then show ?thesis using steps_step by (case_tac a, case_tac "currentTransaction S s", auto elim: step_elims)
  next
  case AFail
    then show ?thesis using steps_step
      by auto
  next
    case (AInvcheck x10)
    then show ?thesis using steps_step by (case_tac a, case_tac "currentTransaction S s", auto elim: step_elims)
  qed
qed






lemma currentTransaction_unchangedInternalSteps2:
assumes "S ~~ tr \<leadsto>* S'"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AEndAtomic"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AFail"
  and "currentTransaction S s = Some t"  
  and wf: "state_wellFormed S"
shows "currentTransaction S' s = Some t"  and "a \<in> set tr \<Longrightarrow> a \<noteq> (s, ABeginAtomic tx ntxn)" 
using assms apply (induct arbitrary: a tx ntxn rule: steps.induct)  
 using currentTransaction_unchangedInternalSteps by (auto simp add: step_simps_all split: if_splits, blast+)
 
 


lemma currentTransaction_unchangedInternalSteps3:
assumes a1: "s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S'"
  and a2: "\<And>st at.  (st, at) \<in> set as \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
  and wf: "state_wellFormed s_init"
shows "currentTransaction S' s \<triangleq> tx"
proof -
  from a1 
  obtain S where 1: "s_init ~~ (s, ABeginAtomic tx ntxns) \<leadsto> S" and 2: "S ~~ as \<leadsto>* S'"
    using steps_appendFront by blast
  from 2
  show "currentTransaction S' s \<triangleq> tx"
  proof (rule currentTransaction_unchangedInternalSteps2)
    from a2
    show "\<And>a. a \<in> set as \<Longrightarrow> snd a \<noteq> AEndAtomic" and "\<And>a. a \<in> set as \<Longrightarrow> snd a \<noteq> AFail"
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
assumes splitTrace: "tr = (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endAtomic: "snd x \<noteq> AEndAtomic"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
using splitTrace txaInTx xOutside no_endAtomic  proof (induct txa arbitrary: tr x rest rule: rev_induct)
  case Nil
  
  have "(s_init ~~ tr \<leadsto>* C) 
      = (s_init ~~ (s, ABeginAtomic tx ntxns) # x # rest \<leadsto>* C)" 
    using Nil by simp
  moreover have "... = (\<exists>S'. (s_init ~~ [(s, ABeginAtomic tx ntxns), x] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    by (auto simp add: steps_appendFront)
  moreover have "... = (\<exists>S'. (s_init ~~ [x, (s, ABeginAtomic tx ntxns)] \<leadsto>* S') \<and> (S' ~~ rest \<leadsto>* C))"
    using useCommutativeS[OF commutative_beginAtomic_other[OF `fst x \<noteq> s`[symmetric] wf `snd x \<noteq> AEndAtomic`]]
      by simp 
  moreover have "... = ( s_init ~~ x # (s, ABeginAtomic tx ntxns) # [] @ rest \<leadsto>* C)"
    by (auto simp add: steps_appendFront)
    
  ultimately show ?case by auto
next
  case (snoc a as)
  
  have "(s_init ~~ x # (s, ABeginAtomic tx ntxns) # (as @ [a]) @ rest \<leadsto>* C)
      = (s_init ~~ x # (s, ABeginAtomic tx ntxns) # as @ ([a] @ rest) \<leadsto>* C)"
      by simp
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ [x] @ ([a] @ rest) \<leadsto>* C)"
    using snoc.hyps by (metis append_Cons append_Nil butlast_snoc in_set_butlastD snoc.prems) 
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ x # a # rest \<leadsto>* C)"
    by simp
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S') \<and> (S' ~~  x # a # rest \<leadsto>* C))"
    by (auto simp add:  steps_append steps_appendFront)
  moreover have "... = (\<exists>S'. (s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S') \<and> (S' ~~  a # x # rest \<leadsto>* C))" (is ?eq1)
    proof -
        have "(S' ~~ x # a # rest \<leadsto>* C)
          \<longleftrightarrow> (S' ~~ a # x # rest \<leadsto>* C)" 
          if "(s_init ~~ (s, ABeginAtomic tx ntxns) # as \<leadsto>* S')"
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
            show " \<not> is_AInvcheck (snd a)"
              by (metis list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1 snoc.prems(2))
          qed
      thus ?eq1 by blast
    qed
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # as @ a # x # rest \<leadsto>* C)"  
    by (auto simp add: steps_append steps_appendFront)
  moreover have "... = (s_init ~~ (s, ABeginAtomic tx ntxns) # (as @ [a]) @ x # rest \<leadsto>* C)"  
    by auto
  ultimately show ?case
    using snoc.prems(1) by blast 
qed    
 

lemma one_compaction_step2:
assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "snd x \<noteq> AEndAtomic"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
apply (auto simp add: steps_append splitTrace)
using local.wf one_compaction_step state_wellFormed_combine txaInTx xOutside no_endatomic by blast+


lemma one_compaction_step3:
assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and splitTrace': "tr' = trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest"
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "snd x \<noteq> AEndAtomic"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr' \<leadsto>* C)"
  using local.wf one_compaction_step2 splitTrace splitTrace' txaInTx xOutside no_endatomic by blast

definition indexInOtherTransaction :: "trace \<Rightarrow> txid \<Rightarrow> nat \<Rightarrow> bool" where
"indexInOtherTransaction tr tx k \<equiv> 
  \<exists>i s ntxns. 
      k<length tr 
    \<and> i<k 
    \<and> tr!i = (s, ABeginAtomic tx ntxns)  
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
  if \<exists>i s ntxns. i < length tr \<and> tr!i = (s, ABeginAtomic tx ntxns) then
    \<exists>i s end ntxns. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx ntxns)
        \<and> end > i  
        \<and> (end < length tr \<and> tr!end = (s, AEndAtomic) \<or> end = length tr)  
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> fst (tr!j) = s) 
  else
    True
  "  

lemma transactionIsPackedAlt_case_tx_exists:
assumes "(s, ABeginAtomic tx ntxns) \<in> set tr"
shows "transactionIsPackedAlt tr tx \<equiv> 
    \<exists>i s end ntxns. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx ntxns)
        \<and> end > i  
        \<and> (end < length tr \<and> tr!end = (s, AEndAtomic) \<or> end = length tr)  
        \<and> (\<forall>j. i\<le>j \<and> j< end \<longrightarrow> fst (tr!j) = s) 
  "  
apply (subst transactionIsPackedAlt_def)
apply (subst if_P)
using assms apply (meson in_set_conv_nth)
by simp 


lemma beginAtomicInTrace_to_transactionStatus:
assumes "S ~~ tr \<leadsto>* S'" 
    and "(s, ABeginAtomic tx ntxns) \<in> set tr"
shows "tx \<in> dom (transactionStatus S')"
using assms by (induct rule: steps.induct, auto simp add: step_simps_all)


lemma transactionIdsUnique:
assumes "S ~~ tr \<leadsto>* S'" 
   and "i < length tr" 
   and "tr!i = (s, ABeginAtomic tx ntxns)"
   and "j < length tr" 
   and "tr!j = (s', ABeginAtomic tx ntxns')"
shows "i = j"    
using assms apply (induct rule: steps.induct)
apply (auto simp add: step_simps Pair_inject  less_Suc_eq nth_append  )
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem)
by (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem)

lemma transactionIdsUnique2:
assumes "S ~~ tr \<leadsto>* S'" 
   and "(s, ABeginAtomic tx ntxns)\<in>set tr" 
   and "(s', ABeginAtomic tx ntxns')\<in>set tr" 
shows "s' = s"
  by (metis Pair_inject assms(1) assms(2) assms(3) in_set_conv_nth transactionIdsUnique)


lemma currentTransaction:
assumes steps: "S ~~ tr \<leadsto>* S'"
   and "i < length tr"
   and "tr!i = (s, ABeginAtomic txi ntxns)"
shows "(\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (s, AEndAtomic) \<and> tr!j \<noteq> (s, AFail)) \<longleftrightarrow> currentTransaction S' s \<triangleq> txi"
using assms apply (induct arbitrary: txi i ntxns rule: steps.induct)
apply simp
apply (auto simp add: step_simps_all)
apply (auto simp add: less_Suc_eq nth_append split: if_splits )
apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem order.strict_trans)
using less_trans apply blast
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem order.strict_trans)
using less_trans by blast+
  
  
lemma noNestedTransactions:
assumes steps: "S ~~ tr \<leadsto>* S'" 
   and "tr!i = (s, ABeginAtomic txi ntxnsi)"
   and "i<j"
   and "j < length tr" 
   and "tr!j = (s, ABeginAtomic txj ntxnsj)"
shows "\<exists>k. i<k \<and> k < j \<and> (tr!k = (s, AEndAtomic) \<or> tr!k = (s, AFail))"
using assms apply (induct rule: steps.induct)
  apply simp
  apply (case_tac "j < length tr")
  apply (metis (no_types, hide_lams) less_trans nth_append)
  apply (subgoal_tac "j = length tr")
  apply auto
  apply (auto simp add: step_simps nth_append)
  using currentTransaction by (metis option.simps(3)) 

lemma noNestedTransactions':
assumes steps: "S ~~ tr \<leadsto>* S'" 
   and "tr!i = (s, ABeginAtomic txi ntxnsi)"
   and "i<j"
   and "j < length tr" 
   and "tr!j = (s, ABeginAtomic txj ntxnsj)"
   and "(s, AFail) \<notin> set tr"
shows "\<exists>k. i<k \<and> k < j \<and> tr!k = (s, AEndAtomic) "
using noNestedTransactions[OF steps assms(2) assms(3) assms(4) assms(5) ] assms(6)
  by (metis assms(4) dual_order.strict_trans nth_mem)

  
lemma transactionIsPackedAlt_eq:
assumes uniqueTxs: "\<And>i j s s' tnxns tnxns'. \<lbrakk>i<length tr; j<length tr; tr!i = (s, ABeginAtomic tx tnxns); tr!j = (s', ABeginAtomic tx tnxns')\<rbrakk> \<Longrightarrow> i = j"
shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
proof (auto simp add: transactionIsPackedAlt_def )
  fix i s ntxns ia sa ntxns'
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
     and a2: "ia < length tr"
     and a3: "tr ! ia = (sa, ABeginAtomic tx ntxns')"
     and a4: "\<forall>j. ia \<le> j \<and> j < length tr \<longrightarrow> fst (tr ! j) = sa"
  
  have [simp]: "ia = i"
    using a2 a0 a3 a1 by (rule uniqueTxs)
    
    
    
  hence [simp]: "sa = s"
    using a1 a3 by auto  
  hence a4': "\<And>j. i \<le> j \<Longrightarrow> j < length tr \<Longrightarrow> fst (tr ! j) = s"  
    using a4 by auto
     
  show "transactionIsPacked tr tx"
    apply (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s')
    by (smt \<open>ia = i\<close> \<open>sa = s\<close> a2 a3 a4' le_eq_less_or_eq le_less_trans prod.inject uniqueTxs)
next
  fix i s ntxns
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
     and a2: "transactionIsPacked tr tx"
  
  from a2
  have a2': "fst (tr ! k) = s \<or> (\<exists>j<k. i < j \<and> tr ! j = (s, AEndAtomic))" 
    if "k<length tr" "i<k"
    for k
    apply (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
    using a1 that(1) that(2) by blast
    
  show "\<exists>i<length tr. \<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"  
  proof (rule_tac x=i in exI, (auto simp add: a0))
    show "\<exists>s. (\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)) \<and> (\<exists>end>i. (end < length tr \<and> tr ! end = (s, AEndAtomic) \<or> end = length tr) \<and> (\<forall>j. i \<le> j \<and> j < end \<longrightarrow> fst (tr ! j) = s))"
    proof (rule_tac x=s in exI, safe)
      show "\<exists>ntxns. tr ! i = (s, ABeginAtomic tx ntxns)"
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
  show "\<forall>i<length tr. \<forall>s ntxns. tr ! i \<noteq> (s, ABeginAtomic tx ntxns) \<Longrightarrow> transactionIsPacked tr tx"
   by (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
next
  fix i s ntxns ia sa ntxns' ende
  assume a0: "i < length tr"
     and a1: "tr ! i = (s, ABeginAtomic tx ntxns)"
     and a3: "tr ! ia = (sa, ABeginAtomic tx ntxns')"
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
    proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def, rename_tac i' s' ntxns)
      fix k i' s' ntxns
      assume b0: "k < length tr"
         and b1: "i' < k"
         and b2: "tr ! i' = (s', ABeginAtomic tx ntxns)"
         and b3: "\<forall>j>i'. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
         and b4: "fst (tr ! k) \<noteq> s'"
         
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
    with b4 show False  by simp
  qed
qed

lemma transactionIsPackedAlt_eq2:
assumes steps: "initialState p ~~ tr \<leadsto>* S"
shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
  using steps transactionIdsUnique transactionIsPackedAlt_eq by auto  

find_theorems steps ABeginAtomic

find_theorems "card _ = 0"
    

lemma transactionIsPacked_show:
assumes steps: "initialState p ~~ tr \<leadsto>* S"
    and beginAtomic1: "beginAtomic < endAtomic"
    and beginAtomic2: "tr!beginAtomic = (s, ABeginAtomic tx ntxns)"
    and endAtomic1: "endAtomic < length tr"    
    and endAtomic2: "tr!endAtomic = (s, AEndAtomic)"
    and a1: "\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> fst (tr ! i) = s"
shows "transactionIsPacked tr tx"
 (* by (smt a1 beginAtomic1 beginAtomic2 endAtomic1 endAtomic2 fst_conv indexInOtherTransaction_def leI less_imp_le_nat less_trans steps transactionIdsUnique transactionIsPacked_def) *)
proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
  fix k i s' ntxns
  assume b0: "k < length tr"
     and b1: "i < k"
     and b2: "tr ! i = (s', ABeginAtomic tx ntxns)"
     and b3: "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
     and b4: "fst (tr ! k) \<noteq> s'"
  
  from steps b2
  have "i = beginAtomic"
    using b0 b1 beginAtomic1 beginAtomic2 endAtomic1 transactionIdsUnique by auto
  hence "s' = s"
    using b2 beginAtomic2 by auto
    
  from b3
  have "k \<le> endAtomic"
    using \<open>i = beginAtomic\<close> \<open>s' = s\<close> beginAtomic1 endAtomic2 leI by blast
  
  with b4 show False
    using \<open>i = beginAtomic\<close> \<open>k \<le> endAtomic\<close> a1 b1 b2 by auto
qed    


lemma transactionIsPacked_from_sublist:
assumes steps: "initialState p ~~ tr \<leadsto>* S"
    and packed: "transactionIsPacked xs tx"
    and split: "tr = start@xs@end"
shows "transactionIsPacked tr tx" 
using packed split
apply (auto simp add: transactionIsPacked_def)
oops (* TODO needs more restrictive definition of transactionIsPacked *)


(* the set of transactions occurring in the trace *)    
definition traceTransactions :: "trace \<Rightarrow> txid set" where
"traceTransactions tr \<equiv> {tx | s tx txns. (s, ABeginAtomic tx txns) \<in> set tr}"
    
text {* between begin and end of a transaction there are no actions from other sessions  *}
definition transactionsArePacked :: "trace \<Rightarrow> bool" where
"transactionsArePacked tr \<equiv>
  \<forall>i k s t txns. 
      i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t txns)  
    \<and> fst (tr!k) \<noteq> s
    \<longrightarrow>  (\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

text {*
For termination proofs, we want to measure how far a trace is from being packed.
For this we take the sum over all actions in the trace and count in how many transactions
it appears.
*}


(* checks if sessions s is in a transaction at position i in trace tr *)
definition inTransaction :: "trace \<Rightarrow> nat \<Rightarrow> invocation \<Rightarrow> bool"  where 
"inTransaction tr i s \<equiv>
  \<exists>j. j\<le>i \<and> i<length tr \<and> (\<exists>t txns. tr!j = (s, ABeginAtomic t txns))
     \<and> (\<forall>k. j<k \<and> k < length tr \<and> k\<le>i \<longrightarrow> tr!k \<noteq> (s, AEndAtomic))
"

(* returns the set of all transactions, which are in a transaction at point i in the trace*)
definition sessionsInTransaction :: "trace \<Rightarrow> nat \<Rightarrow> invocation set"  where 
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


lemma " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1 txns), (s\<^sub>1, AEndAtomic)] 3 = {}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done


lemma " sessionsInTransaction [(s1, ABeginAtomic t\<^sub>1 txns)] 0= {s1}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done

lemma " sessionsInTransaction [(s\<^sub>1, ABeginAtomic t\<^sub>1 txns), (s\<^sub>1, AEndAtomic)] 1 = {}" 
apply (auto simp add: sessionsInTransaction_def )
apply (auto simp add: inTransaction_def nth_Cons' split: if_splits)
done

(*
fun sessionsInTransactionRevAlt :: "trace \<Rightarrow> nat \<Rightarrow> invocation set"  where
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

lemma if_cases:
"\<lbrakk>c \<Longrightarrow> P t; \<not>c \<Longrightarrow> P f\<rbrakk> \<Longrightarrow>  P (if c then t else f)"
  by auto

lemma if_cases2:
"\<lbrakk>c \<Longrightarrow> X = t; \<not>c \<Longrightarrow> X = f\<rbrakk> \<Longrightarrow>  X = (if c then t else f)"
  by auto  
  
lemma sessionsInTransactionEmptySnoc: 
"sessionsInTransaction (tr@[a]) i = (
if i=length tr then
  if \<exists>t ts. snd a = ABeginAtomic t ts then
       sessionsInTransaction tr (length tr - 1) \<union> {fst a}
  else if snd a = AEndAtomic then
       sessionsInTransaction tr (length tr - 1) - {fst a}
  else 
       sessionsInTransaction tr (length tr - 1)
else if i > length tr then
  {}
else
  sessionsInTransaction tr i)"
proof (intro if_cases2; clarsimp)
  fix t ts
  assume a0: "i = length tr"
     and a1: "snd a = ABeginAtomic t ts"
  
  thus "sessionsInTransaction (tr @ [a]) (length tr) = insert (fst a) (sessionsInTransaction tr (length tr - Suc 0))"
    apply (case_tac a, auto)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    apply (metis Suc_leI Suc_le_mono Suc_pred length_pos_if_in_set less_imp_le_nat nat_neq_iff nth_mem)
    apply (auto simp add: nth_append sessionsInTransaction_def  split: if_splits)[1]
    apply (metis (no_types, lifting) inTransaction_def leD le_eq_less_or_eq length_append_singleton less_Suc_eq nth_append_length)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    by (metis Suc_pred le0 le_less_trans less_not_refl3 less_trans_Suc not_le)
    
next
  assume a0: "i = length tr"
   and a1: "snd a = AEndAtomic"

  thus "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0) - {fst a}"
    apply (case_tac a, auto)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    apply (smt Suc_pred inc_induct less_Suc_eq less_imp_le_nat linorder_neqE_nat not_less_zero)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def sndI split: if_splits)[1]
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    by (smt Nitpick.size_list_simp(2) One_nat_def le_SucI length_tl less_Suc_eq_le not_less_eq_eq not_less_zero)
next
  assume a0: "i = length tr"
   and a1: "\<forall>t ts. snd a \<noteq> ABeginAtomic t ts"
   and a2: "snd a \<noteq> AEndAtomic"

  thus "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0)"
    apply (case_tac a, auto)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)
    apply (smt Suc_diff_diff Suc_pred cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_is_0_eq' diff_zero le_trans n_not_Suc_n nat_le_linear not_gr_zero zero_less_diff)
    by (metis Suc_pred le0 le_less_trans less_not_refl3 less_trans_Suc not_le)
    
next 
  show "length tr < i \<Longrightarrow> sessionsInTransaction (tr @ [a]) i = {}"
    by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)
qed

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
shows "\<exists>i k s t ts a s'. 
      tr ! k = (s', a) 
    \<and> i<k 
    \<and> k<length tr 
    \<and> tr!i = (s, ABeginAtomic t ts)  
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
shows "\<exists>trStart s tx txns txa rest.
       tr = trStart @ (s, ABeginAtomic tx txns) # txa @ tr!min_i # rest 
     \<and> length (trStart @ (s, ABeginAtomic tx txns) # txa) = min_i
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
  obtain j s tx txns
    where j1: "min_i < length tr"
      and j2: "j \<le> min_i"
      and noEndAtomic: "\<forall>k. j < k \<and> k < length tr \<and> k \<le> min_i \<longrightarrow> tr ! k \<noteq> (s, AEndAtomic)"
      and tr_j: "tr ! j = (s, ABeginAtomic tx txns)"
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
     using j2 min_i1 by auto
    
   have arith_simp[simp]: "i < min_i - Suc j \<Longrightarrow> Suc j + i \<le> length tr" for i
     using min_simp1 by linarith
    
   have arith_simp2[simp]: "i < min_i - Suc j \<Longrightarrow> Suc (j + i) \<le> length tr" for i
     using arith_simp by auto
   
   have j_len[simp]: "j < length tr"
     using j2 min_i1 by auto
  
    
    
     
   have "tr = trStart @ (s, ABeginAtomic tx txns) # txa @ (tr!min_i) # rest"
     (* this proof should be easier ... *)
     apply (auto simp add: trStart_def txa_def rest_def append_eq_conv_conj2 cons_eq_conv_conj)
     using j_len apply auto[1]
     apply (simp add: hd_drop_conv_nth j1 less_imp_le_nat min.absorb2 tr_j)
     apply (auto simp add: append_eq_conv_conj)
     apply (simp add: drop_Suc j_len less_or_eq_imp_le min_absorb2 min_diff min_i1 tl_drop)
     apply (rule sym)
     apply (auto simp add: cons_eq_conv_conj)
     apply (metis Suc_leI j_len j2 le_diff_iff min_i1 not_less order.not_eq_order_implies_strict otherS prod.collapse prod.inject tr_j)
     apply (smt Suc_diff_Suc add_diff_cancel_left' drop_Suc fst_conv hd_drop_conv_nth j_len j2 leD le_Suc_ex le_diff_iff length_drop less_imp_le_nat min_i1 nth_drop order.not_eq_order_implies_strict otherS tr_j)
     apply (subst tl_drop)
     apply (case_tac j)
     apply auto
     apply (metis Suc_diff_Suc diff_zero drop_Suc fst_conv j2 le_less otherS tr_j)
     apply (case_tac nat)
     apply auto
     apply (metis (mono_tags, lifting) One_nat_def Suc_diff_Suc diff_zero drop_0 drop_Suc dual_order.order_iff_strict fst_conv j2 less_le_trans less_numeral_extra(1) otherS tr_j)
     by (smt Suc_diff_Suc add.commute add_diff_cancel_left' drop_Suc drop_drop dual_order.order_iff_strict fst_conv j2 le_Suc_ex otherS tl_drop tr_j)
     
     
   hence "tr = trStart @ (s, ABeginAtomic tx txns) # txa @ (tr!min_i) # rest
       \<and> length (trStart @ (s, ABeginAtomic tx txns) # txa) = min_i"
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
      
      { (* Next, we consider the case where txa contains an action from a different invocation*)
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
          apply (simp add: other_least_1)
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
shows "\<exists>trStart s txns txa rest.
       tr = trStart @ (s, ABeginAtomic tx txns) # txa @ tr!min_i # rest 
     \<and> length (trStart @ (s, ABeginAtomic tx txns) # txa) = min_i
     \<and> (\<forall>a \<in> set txa. fst a = s \<and> snd a \<noteq> AEndAtomic)
     \<and> (s \<noteq> fst (tr!min_i))"
proof -
  
  from i2
  obtain j s txns
    where j1: "j < length tr"
      and j2: "j \<le> min_i"
      and noEndAtomic: "\<forall>k. j < k \<and> k < length tr \<and> k \<le> min_i \<longrightarrow> tr ! k \<noteq> (s, AEndAtomic)"
      and tr_j: "tr ! j = (s, ABeginAtomic tx txns)"
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
    
     
   have "tr = trStart @ (s, ABeginAtomic tx txns) # txa @ (tr!min_i) # rest"
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
     
     
   hence "tr = trStart @ (s, ABeginAtomic tx txns) # txa @ (tr!min_i) # rest
       \<and> length (trStart @ (s, ABeginAtomic tx txns) # txa) = min_i"
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
      
      { (* Next, we consider the case where txa contains an action from a different invocation*)
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
shows "traceCorrect tr' = traceCorrect tr"
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


definition allowed_context_switch where 
"allowed_context_switch action \<equiv> 
            (\<exists>txId txns. action = ABeginAtomic txId txns) 
          \<or> (\<exists>p a. action = AInvoc p a)"

definition packed_trace :: "trace \<Rightarrow> bool" where
"packed_trace tr \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> fst (tr!(i-1)) \<noteq> fst (tr!i)
    \<longrightarrow> (allowed_context_switch (snd (tr!i)))" 

    
lemmas use_packed_trace = iffD1[OF packed_trace_def[THEN meta_eq_to_obj_eq], rule_format]

lemma isPrefix_len:
"isPrefix tr tr' \<Longrightarrow> length tr \<le> length tr'"
  by (metis isPrefix_def nat_le_linear take_all)


lemma isPrefix_same: 
assumes "isPrefix tr tr'"
    and "i<length tr"
shows "tr!i = tr'!i"
using assms apply (auto simp add: isPrefix_def )
  by (metis nth_take)


lemma prefixes_are_packed:
assumes "packed_trace tr'" 
    and "isPrefix tr tr'"
shows "packed_trace tr"
using `packed_trace tr'` apply (auto simp add: packed_trace_def  )
  by (metis (no_types, lifting) Suc_leI assms(2) diff_less_Suc isPrefix_len isPrefix_same less_le_trans)



lemma context_switches_in_packed: 
assumes packed: "packed_trace tr"
    and split_tr: "tr = tr1@[(s,a),(s',a')]@tr2"
    and differentSession: "s \<noteq> s'"
shows "allowed_context_switch a'"
  (*"(\<exists>tx txns. a' = ABeginAtomic tx txns) \<or> (\<exists>p ar. a' = AInvoc p ar)"*)
proof -
  have "a' = snd(tr!(1+length tr1))"
    using split_tr by (auto simp add: nth_append)
  
  moreover
  have "allowed_context_switch (snd(tr!(1+length tr1)))"
  using packed proof (rule use_packed_trace)
    show "0 < 1 + length tr1" by simp
    show "1 + length tr1 < length tr" using split_tr by auto
    show "fst (tr ! (1 + length tr1 - 1)) \<noteq> fst (tr ! (1 + length tr1))" using split_tr `s \<noteq> s'` by (auto simp add: nth_append)
  qed
  ultimately
  show ?thesis by simp
qed  


definition max_natset :: "nat set \<Rightarrow> nat" where
"max_natset S \<equiv> if S = {} then 0 else Suc (Max S)"

lemma max_natset_empty[simp]: "max_natset S = 0 \<longleftrightarrow> S = {}"
by (simp add: max_natset_def)

lemma max_natset_Suc: 
assumes "max_natset S = Suc i"
   and "finite S"
shows "i\<in>S"
  and "\<And>j. j\<in>S \<Longrightarrow> j\<le>i"
using assms apply (auto simp add: max_natset_def  split: if_splits)
using Max_in by blast

lemma max_natset_Collect_Suc: 
assumes "max_natset {x. P x} = Suc i"
   and "finite {x. P x}"
shows "P i"
  and "\<And>j. P j \<Longrightarrow> j\<le>i"
using assms apply (auto simp add: max_natset_def  split: if_splits)
using Max_in by blast

lemma show_max_natset_smaller:
assumes "i \<in> S"
   and "finite S"
   and "\<And>j. j\<in>S' \<Longrightarrow> j < i"
shows "max_natset S' < max_natset S"
using assms apply (auto simp add: max_natset_def)
  by (metis Max_gr_iff Max_in all_not_in_conv bounded_nat_set_is_finite)

lemma show_max_natset_smaller_Collect:
assumes "P i"
   and "finite {i. P i}"
   and "\<And>j. P' j \<Longrightarrow> j < i"
shows "max_natset {i. P' i} < max_natset {i. P i}"
apply (rule show_max_natset_smaller)
using assms by force+
         

lemma finiteH: 
"finite {x::nat. 0 < x \<and> x < A \<and> P x}"
  by simp

definition canSwap :: "action \<Rightarrow> action \<Rightarrow> bool" where
"canSwap a b \<equiv> (\<forall>C1 C2 s1 s2. s1\<noteq>s2 \<and> (C1 ~~ [(s1,a),(s2,b)] \<leadsto>* C2) \<and> state_wellFormed C1 \<longrightarrow> (C1 ~~ [(s2,b),(s1,a)] \<leadsto>* C2))"
  
lemma show_canSwap:
assumes "\<And>C1 C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
shows "canSwap a b"
proof (auto simp add: canSwap_def)
  fix C1 C3 s1 s2
  assume a0: "s1 \<noteq> s2"
     and a1: "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C3"
     and a2: "state_wellFormed C1"
     
  from a1 obtain C2
  where a1': "C1 ~~ (s1,a) \<leadsto> C2" and a1'': "C2 ~~ (s2,b) \<leadsto> C3"
    using steps_appendFront steps_single by blast
    
     
  show "C1 ~~ [(s2, b), (s1, a)] \<leadsto>* C3"
  proof (subst steps.simps, clarsimp, rule assms)
    show "s1 \<noteq> s2" using a0.
    show "C1 ~~ (s1, a) \<leadsto> C2" using a1'.
    show "C2 ~~ (s2,b) \<leadsto> C3" using a1''.
    show "state_wellFormed C1" using a2.
  qed
qed
    
lemma show_canSwap':
assumes "x = a" 
    and"\<And>C1 C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
shows "canSwap x b"
  using assms show_canSwap by auto

method prove_canSwap = (rule show_canSwap, auto simp add: step_simps, subst state_ext, auto)  
method prove_canSwap' = (rule show_canSwap', auto simp add: step_simps, subst state_ext, auto)

lemma commutativeS_canSwap:
assumes comm: "\<And>C s1 s2. s1\<noteq>s2 \<Longrightarrow> commutativeS C (s1,a) (s2,b)"
shows "canSwap a b"
proof (auto simp add: canSwap_def)
  fix C1 C2 s1 s2
  assume a0: "s1 \<noteq> s2"
     and a1: "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2"
  
  show "C1 ~~ [(s2, b), (s1, a)] \<leadsto>* C2"
  proof (subst useCommutativeS)
    show "commutativeS C1 (s2, b) (s1, a)" 
      using comm a0 by (simp add: commutativeS_switchArgs) 
    show "C1 ~~ [(s1, a), (s2, b)] \<leadsto>* C2" using a1.
  qed
qed
        

lemma canSwap_when_allowed:
assumes no_ctxt_switch: "\<not>allowed_context_switch b"
    and no_invcheck_a: "\<not>is_AInvcheck a"
    and no_invcheck_b: "\<not>is_AInvcheck b"  
    and no_fail_a: "a \<noteq> AFail"
    and no_fail_b: "b \<noteq> AFail"    
shows "canSwap a b"
proof (cases b)
  case ALocal
  then show ?thesis
    by (simp add: commutativeS_canSwap) 
next
  case (ANewId bid)
  hence [simp]: "b = ANewId bid" .
  show ?thesis 
  proof (cases a; prove_canSwap?)
    case (AInvcheck x91 x92)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by blast 
  qed
next
  case (ABeginAtomic x31 x32)
  then show ?thesis
    using allowed_context_switch_def no_ctxt_switch by auto 
next
  case AEndAtomic
  hence [simp]: "b = AEndAtomic" .
  then show ?thesis 
  proof (cases a; prove_canSwap?)
    case ALocal
    then show ?thesis
      by (simp add: commutativeS_canSwap) 
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap'
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis 
      apply (rule show_canSwap')
      apply (auto simp add: step_simps)
      apply (auto)
      apply (subst state_ext)
      apply auto
      done
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap'
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis by prove_canSwap'
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap'
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap'
  next
    case AFail
    then show ?thesis by prove_canSwap'
  next
    case (AInvcheck x91 x92)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case (ADbOp x51 x52 x53 x54)
  hence [simp]: "b = ADbOp x51 x52 x53 x54" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap'
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap'
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap'
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap'
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis
      using canSwap_def useCommutativeS by auto 
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap'
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap'
  next
    case AFail
    then show ?thesis
      using no_fail_a by blast 
  next
    case (AInvcheck x91 x92)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by blast 
  qed
next
  case (AInvoc x61 x62)
  then show ?thesis
    using allowed_context_switch_def no_ctxt_switch by auto 
  
next
  case (AReturn res)
  hence [simp]: "b = AReturn res" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap'
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap'
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap'
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap'
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis by prove_canSwap'
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap'
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap'
  next
    case AFail
    then show ?thesis by prove_canSwap'
  next
    case (AInvcheck x91 x92)
      then show ?thesis
        using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case AFail
  then show ?thesis
    using no_fail_b by blast 
next
  case (AInvcheck x91 x92)
  then show ?thesis
    using is_AInvcheck_def no_invcheck_b by auto 
qed

  
text {* We can swap one action over a list of actions with canSwap *}
lemma swapMany:
assumes steps: "C1 ~~ tr @ [(s,a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (snd x) a"
    and wf: "state_wellFormed C1"
shows "C1 ~~ [(s,a)] @ tr \<leadsto>* C2"
using steps tr_different_session tr_canSwap 
proof (induct tr arbitrary: C2 rule: rev_induct)
  case Nil
  then show ?case
    by simp 
next
  case (snoc a' tr')
  hence IH: "\<And>C2. \<lbrakk>C1 ~~ tr' @ [(s, a)] \<leadsto>* C2; \<And>x. x \<in> set tr' \<Longrightarrow> fst x \<noteq> s; \<And>x. x \<in> set tr' \<Longrightarrow> canSwap (snd x) a\<rbrakk> \<Longrightarrow> C1 ~~ [(s, a)] @ tr' \<leadsto>* C2" 
    and steps: "C1 ~~ (tr' @ [a']) @ [(s, a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> canSwap (snd x) a"
    by auto
 
  from steps
  obtain C'
    where steps1: "C1 ~~ tr' \<leadsto>* C'" 
      and steps2: "C' ~~ [a', (s, a)] \<leadsto>* C2"
    using steps_append by auto
  
  have wf': "state_wellFormed C'"
    using local.wf state_wellFormed_combine steps1 by blast
    
  from steps2
  have steps2': "C' ~~ [(s, a), a'] \<leadsto>* C2"
    using tr_canSwap by (metis canSwap_def list.set_intros(1) prod.collapse rotate1.simps(2) set_rotate1 tr_different_session wf') 
    
  from steps1 steps2'
  have "C1 ~~ tr' @  [(s, a), a'] \<leadsto>* C2"
    using steps_append2 by blast
  
  from this 
  obtain C''
  where steps1': "C1 ~~ tr' @  [(s, a)] \<leadsto>* C''" and steps2'': "C'' ~~ [a'] \<leadsto>* C2"
    by (metis (no_types, hide_lams) append.assoc append_Cons append_Nil steps_append)
  
  from steps1' IH
  have steps1'': "C1 ~~ [(s, a)] @ tr' \<leadsto>* C''"
    by (simp add: snoc.prems(2) snoc.prems(3))
  
    
  with steps2''  
  show ?case
    using steps_append2 by fastforce 
qed


lemma swapMany_middle:
assumes steps: "C1 ~~ tr_start @ tr @ [(s,a)] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (snd x) a"
    and wf: "state_wellFormed C1"
shows "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
proof -
  from steps
  obtain C1' C2'
    where "C1 ~~ tr_start \<leadsto>* C1'" and "C1' ~~ tr @ [(s,a)] \<leadsto>* C2'" and "C2' ~~ tr_end \<leadsto>* C2"
    by (meson steps_append)
   
  hence "C1' ~~ [(s,a)] @ tr  \<leadsto>* C2'"
    using local.wf state_wellFormed_combine swapMany tr_canSwap tr_different_session by blast
    
  thus "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
    using \<open>C1 ~~ tr_start \<leadsto>* C1'\<close> \<open>C2' ~~ tr_end \<leadsto>* C2\<close> steps_append2 by fastforce
qed    

lemma swapMany_middle':
assumes steps: "C1 ~~ tr_start @ tr @ [a] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> (fst a)"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (snd x) (snd a)"
    and wf: "state_wellFormed C1"
shows "C1 ~~ tr_start @ [a] @ tr @ tr_end \<leadsto>* C2"
using assms apply (cases a)
apply (rule ssubst, assumption, rule swapMany_middle)
apply auto
done

lemma localState_iff_exists_invoc:
assumes steps: "initialState program ~~ tr \<leadsto>* C"
shows "localState C s \<noteq> None \<longrightarrow> (\<exists>p args. (s, AInvoc p args) \<in> set tr)"
  using invation_info_set_iff_invocation_happened(1) invocation_ops_if_localstate_nonempty steps by auto
(*
  using steps proof (induct rule: steps_induct)
  case initial
  then show ?case
    by (auto simp add: initialState_def)
next
  case (step S' tr a S'')
  hence  IH: "(localState S' s \<noteq> None) \<longrightarrow> (\<exists>p args. (s, AInvoc p args) \<in> set tr)"
    and step': "S' ~~ a \<leadsto> S''"
    by auto
  
  show ?case 
    using step apply (auto simp add: step_simps_all split: if_splits)
    by blast
qed    
*)

lemma exists_invoc:
assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and "i < length tr"
    and "fst(tr!i) = s"
    and "\<And>p args. snd(tr!i) \<noteq> AInvoc p args"
    and "\<not>is_AInvcheck (snd(tr!i))"
shows "\<exists>j. j<i \<and> fst(tr!j) = s \<and> (\<exists>p args. snd(tr!j) = AInvoc p args)"    
using assms proof (induct arbitrary: i rule: steps_induct)
  case initial
  then show ?case by (auto simp add: initialState_def)
next
  case (step S' tr a S'')
  
  from `initialState program ~~ tr \<leadsto>* S'`
  have "\<exists>p args. (s, AInvoc p args) \<in> set tr" if "localState S' s \<noteq> None" for s
    using that
    using localState_iff_exists_invoc by blast 
  
  hence getI: "\<exists>j p args. j<length tr \<and> tr!j =(s, AInvoc p args)" if "localState S' s \<triangleq> x" for s x
    by (metis in_set_conv_nth option.distinct(1) that)
    
    
  show ?case 
  proof (cases "i = length tr")
    case True
    then show ?thesis 
      using `S' ~~ a \<leadsto> S''` 
        `fst ((tr @ [a]) ! i) = s`
      apply (auto simp add: step_simps_all nth_append_first  dest!: getI split: if_splits)
      using step.prems(3) apply fastforce
      using is_AInvcheck_def step.prems(4) by auto
  next
    case False
    hence "i < length tr"
      using step.prems(1) by auto
      
    then show ?thesis
      by (smt less_imp_le less_le_trans nth_append_first step.IH step.prems(2) step.prems(3) step.prems(4)) 
  qed
qed
  
definition packed_trace_s :: "trace \<Rightarrow> invocation \<Rightarrow> bool" where
"packed_trace_s tr s \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> fst (tr!i) = s
    \<longrightarrow> fst (tr!(i-1)) \<noteq> s
    \<longrightarrow> (allowed_context_switch (snd (tr!i)))" 

    
lemma exists_greatest:
assumes example: "P j"
    and bounded: "\<And>j. P j \<Longrightarrow> j \<le> bound"
shows "\<exists>j::nat. P j \<and> (\<forall>j'. P j' \<longrightarrow> j' \<le> j)"
using example proof (induct "bound - j" arbitrary: j)
  case 0
  with bounded
  have "j = bound"
    by force
  then show ?case
    using "0.prems" bounded by blast 
next
  case (Suc i)
  then show ?case
    by (metis GreatestI Greatest_le bounded leI less_le_trans) 
qed

    
lemma exists_greatest':
assumes example: "\<exists>j. P j"
    and bounded: "\<exists>bound. \<forall>j. P j \<longrightarrow> j \<le> bound"
shows "\<exists>j::nat. P j \<and> (\<forall>j'. P j' \<longrightarrow> j' \<le> j)"
  using bounded example exists_greatest by auto    

lemma split_take:
assumes "ys = drop i xs"
shows "xs = take i xs @ ys"
  by (simp add: assms)


  find_theorems name:induct "op\<subset>"
    
  
  
lemma pack_trace_for_one_session:
assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr \<Longrightarrow> \<not>is_AInvcheck a "
shows "\<exists>tr'. packed_trace_s tr' s
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s)
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
text {* By induction over the minimal index that is not packed.*}
(* I could not figure out how to write this down as an induction over the minimum, so I reversed it and made it an induction over the maximum. *)
using steps noFail noInvcheck        
proof (induct "max_natset {length tr - i  | i.
        0<i 
      \<and> i<length tr 
      \<and> fst (tr!(i-1)) \<noteq> s
      \<and> fst (tr!i) = s
      \<and> \<not>(allowed_context_switch (snd(tr!i)))}"
      arbitrary: tr C
      rule: less_induct)
  case less
  hence IH: "\<And>tra C. \<lbrakk>max_natset {length tra - i |i. 0 < i \<and> i < length tra \<and> fst (tra ! (i - 1)) \<noteq> s \<and> fst (tra ! i) = s \<and> \<not> allowed_context_switch (snd (tra ! i))}
                      < max_natset {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))};
                      initialState program ~~ tra \<leadsto>* C; \<And>s. (s, AFail) \<notin> set tra; \<And>s a. (s, a) \<in> set tra \<Longrightarrow> \<not> is_AInvcheck a\<rbrakk>
                     \<Longrightarrow> \<exists>tr'. packed_trace_s tr' s \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tra s \<longrightarrow> packed_trace_s tr' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"
   and noFail: "\<And>s. (s, AFail) \<notin> set tr"
   and noInvcheck: "\<And>s a. (s, a) \<in> set tr \<Longrightarrow> \<not> is_AInvcheck a"
  by auto
  
  show ?case 
  proof (cases "max_natset {length tr - i  | i. 0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))}")
    case 0
    hence "{i. 0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))} = {}"
      by simp
    hence already_packed: "packed_trace_s tr s"
      by (auto simp add: packed_trace_s_def)
    
    show ?thesis 
      by (rule exI[where x=tr], auto simp add: less already_packed)
    
  next
    case (Suc n)
    
    text {* There is one problematic position *}
    from Suc
        obtain i_example
        where i_example: "0 < i_example \<and> i_example < length tr \<and> fst (tr ! (i_example - 1)) \<noteq> s \<and> fst (tr ! i_example) = s \<and> \<not> allowed_context_switch (snd (tr ! i_example))"
          using max_natset_Collect_Suc(1) by fastforce
        
    text {* Let i be the smallest problematic position *}
    obtain i
      where i_def: "0<i \<and> i<length tr \<and> fst (tr!(i-1)) \<noteq> s \<and> fst (tr!i) = s \<and> \<not>(allowed_context_switch (snd(tr!i)))"
      and i_min: "\<And>j. 0<j \<and> j<length tr \<and> fst (tr!(j-1)) \<noteq> s \<and> fst (tr!j) = s \<and> \<not>(allowed_context_switch (snd(tr!j))) \<Longrightarrow> j\<ge>i"
        apply atomize_elim
        using i_example by (rule ex_has_least_nat)
    hence i1[simp]: "0<i"
      and i2[simp]: "i<length tr"
      and i3: "fst (tr!(i-1)) \<noteq> s"
      and i4: "fst (tr!i) = s"
      and i5: "\<not>(allowed_context_switch (snd(tr!i)))"
      by auto
    
    text {* There must be a previous action on the same invocation (at least the invocation should be there, since i is no invocation). *}
    obtain prev
      where prev1: "fst(tr!prev) = s"
        and prev2: "prev < i"
        and prev3: "\<And>j. \<lbrakk>prev < j; j < i\<rbrakk> \<Longrightarrow> fst(tr!j) \<noteq> s"
      proof (atomize_elim)
        from `initialState program ~~ tr \<leadsto>* C` `i<length tr` `fst (tr!i) = s`
        have "\<exists>j<i. fst (tr ! j) = s \<and> (\<exists>p args. snd (tr ! j) = AInvoc p args)"
        proof (rule exists_invoc)
          show "\<And>p args. snd (tr ! i) \<noteq> AInvoc p args"
            using allowed_context_switch_def i5 by auto 
          show "\<not> is_AInvcheck (snd (tr ! i))"
            by (metis i2 less.prems(3) nth_mem snd_conv surj_pair)
        qed
        hence "\<exists>j<i. fst (tr ! j) = s"
          by auto
        hence "\<exists>j. (j<i \<and> fst (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> fst (tr ! j') = s \<longrightarrow> j'\<le>j)"
        proof (rule exists_greatest')
          show "\<exists>bound. \<forall>j. j < i \<and> fst (tr ! j) = s \<longrightarrow> j \<le> bound"
            using less_or_eq_imp_le by blast
        qed
        from this obtain j where "(j<i \<and> fst (tr ! j) = s) \<and> (\<forall>j'. j'<i \<and> fst (tr ! j') = s \<longrightarrow> j'\<le>j)"
          by blast
        hence "fst (tr ! j) = s \<and> j < i \<and> (\<forall>j'>j. j' < i \<longrightarrow> fst (tr ! j') \<noteq> s)"
          by auto
          
        thus "\<exists>prev. fst (tr ! prev) = s \<and> prev < i \<and> (\<forall>j>prev. j < i \<longrightarrow> fst (tr ! j) \<noteq> s)"  ..
      qed
      
    have [simp]: "prev < length tr"
      using i2 order.strict_trans prev2 by blast
    have [simp]: "min (length tr) prev = prev"
      using i2 prev2 by linarith  
    have [simp]: "min (length tr) i = i"
      using i2  by linarith    
      
    text {* Then we can split the trace, so that we have (one action from s) -- (many other actions) -- (action i form s) *}
    have tr_split: "tr = take prev tr @ [tr!prev] @ drop (Suc prev) (take i tr) @ [tr!i] @ drop (Suc i) tr"
    proof (rule nth_equalityI)
      show "length tr = length (take prev tr @ [tr ! prev] @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr)"
        apply auto
        using i2 prev2 by linarith
      show "\<forall>ia<length tr. tr ! ia = (take prev tr @ [tr ! prev] @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr) ! ia"
        by (auto simp add: nth_append nth_Cons'  Suc_leI less_diff_conv prev2)
    qed    
        
    
    text {* Because of the swap lemma we can change this to (one action from s) -- (action i form s) -- (many other actions) *}
    define tr' where "tr' = take prev tr @ [tr!prev, tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr"
    
    have tr'sameLength: "length tr' = length tr"
      apply (auto simp add: tr'_def)
      using i2 prev2 by linarith
      
    
    have tr'_sameSet: "set tr' = set tr" 
       apply (subst tr_split)
       apply (subst  tr'_def)
       by auto
     
    
    have tr'1: "tr'!x = tr!x" if "x \<le> prev" for x
      using that by (auto simp add: tr'_def nth_append)
    moreover have tr'2: "tr'!x = tr!i" if "x=Suc prev" for x
      using that by (auto simp add: tr'_def nth_append)
    moreover have tr'3: "tr'!x = tr!(x-1)" if "x>Suc prev"  and "x<i" for x
      using that apply (auto simp add: tr'_def nth_append nth_Cons')
      by (metis Suc_diff_Suc diff_Suc_less dual_order.strict_trans less_2_cases not_less_eq numeral_2_eq_2)
    moreover have tr'4: "tr'!x = tr!(x-1)" if  "x = i" for x
      using that apply (auto simp add: tr'_def nth_append nth_Cons')
      apply (simp add: Suc_diff_Suc numeral_2_eq_2)
      using prev2 apply blast
      by (metis Suc_lessI \<open>0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))\<close> diff_Suc_1 leD prev1 prev2)
    moreover have tr'5: "tr'!x = tr!x" if "x > i" and "x < length tr" for x
      using that apply (auto simp add: tr'_def nth_append nth_Cons')
      using prev2 apply linarith
      using prev2 by auto
    ultimately have tr'i_def: "tr'!x = (if x\<le>prev then tr!x else if x=Suc prev then tr!i else if x\<le>i then tr!(x-1) else tr!x)" if "x<length tr" for x
      by (metis antisym_conv2 not_le not_less_eq_eq that)  
    
    
    have "initialState program ~~ (take prev tr @ [tr!prev]) @ [tr!i] @ drop (Suc prev) (take i tr)  @ drop (Suc i) tr \<leadsto>* C"
    proof (rule swapMany_middle')
      show "initialState program ~~ (take prev tr @ [tr ! prev]) @ drop (Suc prev) (take i tr) @ [tr ! i] @ drop (Suc i) tr \<leadsto>* C"
        using tr_split less.prems(1) by auto
        
      show "\<And>x. x \<in> set (drop (Suc prev) (take i tr)) \<Longrightarrow> fst x \<noteq> fst (tr ! i)"
        apply (auto simp add: in_set_conv_nth)
        using prev3
        by (metis add.commute add_Suc_right fst_conv i4 less_add_Suc1 less_diff_conv) 
       
      from i5
      show "canSwap (snd x) (snd (tr ! i))" if "x \<in> set (drop (Suc prev) (take i tr))" for x
      proof (rule canSwap_when_allowed)
        from that obtain k 
          where k1: "x = tr!k" 
            and k2: "k<i" 
            and k3: "k>prev"
           by (auto simp add: in_set_conv_nth)
      
        hence k4: "x\<in>set tr"
          using dual_order.strict_trans i2 nth_mem by blast
          
           
        show "\<not> is_AInvcheck (snd x)"
          by (metis k4 less.prems(3) prod.collapse)
        show "\<not> is_AInvcheck (snd (tr ! i))"
          by (metis i2 less.prems(3) nth_mem snd_conv surj_pair)
        show "snd x \<noteq> AFail"
          by (metis k4 less.prems(2) prod.collapse)
        show "snd (tr ! i) \<noteq> AFail"
          by (metis i2 less.prems(2) nth_mem old.prod.exhaust snd_conv)
      qed  
      
      show "state_wellFormed (initialState program)"
        by auto
    qed    
    
    
    hence "initialState program ~~ tr' \<leadsto>* C"
      by (simp add: tr'_def)
      
    have tr'packed: "packed_trace_s tr' s" if "packed_trace_s tr s" for s
      using that
      apply (auto simp add: packed_trace_s_def tr'i_def tr'sameLength i4 prev1 )
      apply (metis One_nat_def Suc_diff_eq_diff_pred antisym i4 nat_less_le not_less_eq_eq zero_less_Suc zero_less_diff)
      apply (metis One_nat_def Suc_eq_plus1 diff_Suc_1 i_def le_SucE le_diff_conv zero_less_Suc)
      using Suc_leI prev2 by blast
      
      
    
    text {* Now the problem at i is fixed, so we can use IH to fix the rest of the trace. *}
    have "\<exists>tr''. packed_trace_s tr'' s \<and> (initialState program ~~ tr'' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tr' s \<longrightarrow> packed_trace_s tr'' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr'') \<and> (\<forall>s a. (s, a) \<in> set tr'' \<longrightarrow> \<not> is_AInvcheck a)"
    proof (rule IH)
      show "initialState program ~~ tr' \<leadsto>* C"
        by (simp add: \<open>initialState program ~~ tr' \<leadsto>* C\<close>)
      show "\<And>s. (s, AFail) \<notin> set tr'"
        using noFail tr'_sameSet by blast 
      show "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
        using noInvcheck tr'_sameSet by blast
        
    
        
      show "max_natset {length tr' - i |i. 0 < i \<and> i < length tr' \<and> fst (tr' ! (i - 1)) \<noteq> s \<and> fst (tr' ! i) = s \<and> \<not> allowed_context_switch (snd (tr' ! i))}
          < max_natset {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))}"
      proof (rule show_max_natset_smaller_Collect, intro exI)
        show "length tr - i = length tr - i \<and> 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))"
          using One_nat_def i3 i4 i5 by auto
        show "finite {length tr - i |i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))}" by force
        show "\<exists>i. j = length tr' - i \<and> 0 < i \<and> i < length tr' \<and> fst (tr' ! (i - 1)) \<noteq> s \<and> fst (tr' ! i) = s \<and> \<not> allowed_context_switch (snd (tr' ! i)) \<Longrightarrow> j < length tr - i" for j
        proof (auto simp add: tr'sameLength intro!: diff_less_mono2)
          fix i'
          assume a0: "j = length tr - i'"
             and a1: "0 < i'"
             and a2: "i' < length tr"
             and a3: "fst (tr' ! (i' - Suc 0)) \<noteq> fst (tr' ! i')"
             and a4: "\<not> allowed_context_switch (snd (tr' ! i'))"
             and a5: "s = fst (tr' ! i')"
            
          show "i < i'"
            using a2 a3 a4 apply (auto simp add: tr'i_def split: if_splits)
            apply (metis One_nat_def a1 a5 dual_order.strict_iff_order i_min leD prev2 tr'1)
            using \<open>0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> s \<and> fst (tr ! i) = s \<and> \<not> allowed_context_switch (snd (tr ! i))\<close> prev1 apply blast
            using a3 a5 i_def tr'2 apply auto[1]
            by (metis One_nat_def a5 antisym diff_le_self i3 le_less_linear prev3 tr'i_def)
        qed
      qed
    qed

    from this obtain tr'' 
      where tr''1: "packed_trace_s tr'' s" 
        and tr''2: "initialState program ~~ tr'' \<leadsto>* C" 
        and tr''3: "\<forall>s. packed_trace_s tr' s \<longrightarrow> packed_trace_s tr'' s"
        and tr''4: "(\<forall>s. (s, AFail) \<notin> set tr'')"
        and tr''5: "(\<forall>s a. (s, a) \<in> set tr'' \<longrightarrow> \<not> is_AInvcheck a)" 
        by blast
      
    from tr''3
    have tr''packed: "\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr'' s"
      using tr'packed by blast
      
    
    show ?thesis
      using tr''1 tr''2 tr''4 tr''5 tr''packed by blast 
      
    
  qed
qed
        
lemma packed_trace_iff_all_sessions_packed:
  "packed_trace tr \<longleftrightarrow> (\<forall>s. packed_trace_s tr s)"
by (auto simp add: packed_trace_def packed_trace_s_def)

text {* Now we can just repeat fixing invocation by invocation, until all sessions are packed. *}
lemma pack_trace:
assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and noInvcheck: "\<And>s a. (s, a)\<in>set tr \<Longrightarrow> \<not>is_AInvcheck a "
shows "\<exists>tr'. packed_trace tr'
        \<and> (initialState program ~~ tr' \<leadsto>* C)
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (\<forall>s a. (s,a)\<in>set tr' \<longrightarrow> \<not>is_AInvcheck a)"
proof -
  have "{s. \<not>packed_trace_s tr s } \<subseteq> set (map fst tr)"
    by (auto simp add: packed_trace_s_def)

  hence "finite {s. \<not>packed_trace_s tr s }"
    using infinite_super by blast
    
  from this and assms
  show ?thesis
  proof (induct "{s. \<not>packed_trace_s tr s }" arbitrary: tr rule: finite_psubset_induct)
    case psubset
    
    show ?case 
    proof (cases "{s. \<not>packed_trace_s tr s } = {}")
      case True
      hence "packed_trace tr"
        by (auto simp add: packed_trace_iff_all_sessions_packed)
      thus ?thesis
        using psubset.prems by blast 
    next
      case False
      from this obtain s where "\<not> packed_trace_s tr s"
        by blast
      
      
      from `initialState program ~~ tr \<leadsto>* C` `\<And>s. (s, AFail) \<notin> set tr` `\<And>s a. (s, a) \<in> set tr \<Longrightarrow> \<not> is_AInvcheck a`
      have "\<exists>tr'. packed_trace_s tr' s \<and> (initialState program ~~ tr' \<leadsto>* C) \<and> (\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s) \<and> (\<forall>s. (s, AFail) \<notin> set tr') \<and> (\<forall>s a. (s, a) \<in> set tr' \<longrightarrow> \<not> is_AInvcheck a)"  
        by (rule pack_trace_for_one_session; force)
        
      from this
      obtain tr' 
        where tr'1: "packed_trace_s tr' s"
          and tr'2: "initialState program ~~ tr' \<leadsto>* C"
          and tr'3: "\<forall>s. packed_trace_s tr s \<longrightarrow> packed_trace_s tr' s"
          and tr'4: "\<And>s. (s, AFail) \<notin> set tr'"
          and tr'5: "\<And>s a. (s, a) \<in> set tr' \<Longrightarrow> \<not> is_AInvcheck a"
        by blast
      
      from tr'1 tr'3 `\<not> packed_trace_s tr s`
      have subset: "{s. \<not>packed_trace_s tr' s } \<subset> {s. \<not>packed_trace_s tr s }"
        by auto
        
      from subset tr'2 tr'4 tr'5
      show ?thesis 
        by (rule psubset; force)
    qed
  qed
qed
  



lemma pack_incorrect_trace:
assumes steps: "initialState program ~~ tr \<leadsto>* C"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and notCorrect: "\<not>traceCorrect tr"
shows "\<exists>tr' C'. packed_trace tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* C')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> \<not>traceCorrect tr'"
proof -
  text {* As the trace is not correct, there must be a failing invariant: *} 
  
  from notCorrect
  obtain failPos1 
    where failPos1_props: "failPos1 < length tr \<and> (\<exists>s txns. tr ! failPos1 = (s, AInvcheck txns False))"
    by (meson in_set_conv_nth traceCorrect_def)
   
  text {* Now take the minimal failing position. *}  
  hence "\<exists>failPos1. (failPos1 < length tr \<and> (\<exists>s txns. tr ! failPos1 = (s, AInvcheck txns False)))
           \<and> (\<forall>i. (i < length tr \<and> (\<exists>s txns. tr ! i = (s, AInvcheck txns False))) \<longrightarrow> i \<ge> failPos1)"
    by (rule ex_has_least_nat)
  from this
  obtain failPos failPos_s txns
    where failPos_len: "failPos < length tr" 
      and failPos_fail: "tr ! failPos = (failPos_s, AInvcheck txns False)"
      and failPos_min: "\<And> i. \<lbrakk>i < length tr; \<exists>s txns. tr ! i = (s, AInvcheck txns False)\<rbrakk> \<Longrightarrow> i\<ge>failPos"
    by auto

    
    
  text {* Only the part leading to the invariant violation is relevant ...*}  
    
  define tr' where "tr' = take failPos tr"
  
  from steps
  obtain C' where tr'_steps: "initialState program ~~ tr' \<leadsto>* C'"
    by (metis append_take_drop_id steps_append tr'_def)
    
  from steps
  have "initialState program ~~ (tr'@[tr!failPos]@drop (Suc failPos) tr) \<leadsto>* C"
    by (metis \<open>failPos < length tr\<close> append.assoc append_take_drop_id take_Suc_conv_app_nth tr'_def)
  hence "\<exists>C''. (op ~~ C' \<leadsto> (tr ! failPos)) C''"
    using steps_append2 steps_appendFront tr'_steps by auto
    
  hence C'_fails: "\<And>s. C' ~~ (s, AInvcheck txns False) \<leadsto> C'"  
    by (auto simp add: failPos_fail step_simps)
      
  
  text {* No remove all other invariant checks *}
  define tr'' where "tr'' = filter (\<lambda>(s,a). \<not>is_AInvcheck a) tr'"
    
  from tr'_steps
  have tr''_steps:  "initialState program ~~ tr'' \<leadsto>* C'"
    apply (auto simp add: tr''_def)
    apply (induct rule: steps_induct)
    by (auto simp add: is_AInvcheck_def step_simps steps_step)
  
  from tr''_steps
  have "\<exists>tr'''. packed_trace tr''' \<and> (initialState program ~~ tr''' \<leadsto>* C') \<and> (\<forall>s. (s, AFail) \<notin> set tr''') \<and> (\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a)"
  proof (rule pack_trace)
    show "\<And>s. (s, AFail) \<notin> set tr''"
      using noFail by (auto simp add: tr'_def tr''_def dest: in_set_takeD)
    show "\<And>s a. (s, a) \<in> set tr'' \<Longrightarrow> \<not> is_AInvcheck a"
      by (auto simp add: tr''_def)
  qed    
  
  from this
  obtain tr'''
    where tr'''1: "packed_trace tr'''"
      and tr'''2: "initialState program ~~ tr''' \<leadsto>* C'"
      and tr'''3: "\<forall>s. (s, AFail) \<notin> set tr'''"
      and tr'''4: "\<forall>s a. (s, a) \<in> set tr''' \<longrightarrow> \<not> is_AInvcheck a"
    by blast
  
  define tr4 where "tr4 = tr''' @ [(fst (last tr'''), AInvcheck txns False)]"
  
  from `packed_trace tr'''`
  have "packed_trace tr4"
    apply (auto simp add: packed_trace_def tr4_def nth_append)
    by (metis One_nat_def gr_implies_not_zero last_conv_nth length_0_conv less_SucE)
  
  
  moreover have "initialState program ~~ tr4 \<leadsto>* C'"
    using C'_fails steps_append2 steps_single tr'''2 tr4_def by blast
  moreover have "\<forall>s. (s, AFail) \<notin> set tr4"
    by (simp add: tr4_def tr'''3)
  moreover have "\<not> traceCorrect tr4"
    by (auto simp add: traceCorrect_def tr4_def)
    
  ultimately show ?thesis by blast
qed    
    
  
        
        

text {*
 To show that a program is correct, we only have to consider packed transactions
*}
theorem show_programCorrect_noTransactionInterleaving:
assumes packedTracesCorrect: 
  "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
shows "programCorrect program"
unfolding programCorrect_def proof -
  text "We only have to consider traces without AFail actions"
  show "\<forall>trace\<in>traces program. traceCorrect trace"
  proof (subst can_ignore_fails, clarsimp)
    text "Let tr be some trace such that program executes trace to s."
    fix tr
    assume is_trace: "tr \<in> traces program" 
       and noFail: "\<forall>s. (s, AFail) \<notin> set tr"
    
    from is_trace 
    obtain s where steps: "initialState program ~~ tr \<leadsto>* s"
      by (auto simp add: traces_def)
    
    (*
    text "Then there is a reshuffling of the trace, where transactions are not interleaved"
    then obtain tr' s'
      where steps': "initialState program ~~ tr' \<leadsto>* s'" 
        and txpacked': "transactionsArePacked tr'"
        and correct': "traceCorrect tr' \<longleftrightarrow> traceCorrect tr"
        and nofail': "\<forall>s. (s, AFail) \<notin> set tr'"
      using canPackTransactions noFail by blast
    *)
    
    show "traceCorrect tr" 
    proof (rule ccontr)
      assume "\<not> traceCorrect tr"
      with noFail steps
      obtain tr'' s''
      where "initialState program ~~ tr'' \<leadsto>* s''" 
        and "packed_trace tr''"
        and "\<not>traceCorrect tr''"
        and "\<forall>s. (s, AFail) \<notin> set tr''"
        using pack_incorrect_trace
          by blast 
      thus False
        using packedTracesCorrect by blast
    qed
  qed  
qed





end

