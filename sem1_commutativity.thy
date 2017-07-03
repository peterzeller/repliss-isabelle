theory sem1_commutativity
imports replissSem1 prefix
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
      case (pull C s ls vis newTxns newCalls)
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
          using `S' ~~ (s, AFail) \<leadsto> S''` invation_info_set_iff_invocation_happened(1) step.steps steps'' by auto 
      next 
        assume "a = (s, AReturn res)"
        hence "S' ~~ (s, AReturn res) \<leadsto> S''"
          using step.step by auto
        thus "localState S'' s = None"
          by (auto simp add: step_simp_AReturn)
          
        from `S' ~~ (s, AReturn res) \<leadsto> S''`  
        show "invocationOp S'' s \<noteq> None"
          using invocation_ops_if_localstate_nonempty step.steps step_simp_AReturn by auto
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
 There can be no action on a session before the invocation:
*}
lemma nothing_after_fail_or_return:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
 and fail_or_return: "tr!i = (s, AFail) \<or> tr!i = (s, AReturn res)"
 and i_in_range: "i < length tr"
shows "\<nexists>j. j>i \<and> j<length tr \<and> fst(tr!j) = s" 
using steps fail_or_return i_in_range proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'')
  show "\<nexists>j. j>i \<and> j < length (tr @ [a]) \<and> fst ((tr @ [a]) ! j) = s"
  proof auto
    fix j
    assume a1: "j < Suc (length tr)"
       and a2: "i < j"
       and a3: "s = fst ((tr @ [a]) ! j)"
       
    have j_def: "j = length tr"
    proof (rule ccontr)
      assume "j \<noteq> length tr"
      hence "j < length tr" using a1 by simp
      hence "s \<noteq> fst ((tr @ [a]) ! j)"
        by (metis (no_types, hide_lams) a2 dual_order.strict_trans nth_append step.IH step.prems(1))
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
      using no_ls step.steps visibleCalls_iff_localState by auto
    qed
qed

(*
text {*
After a return or a failure no more actions on the same session are possible.
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
schematic_goal [simp]: "isAFail (ABeginAtomic t) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AEndAtomic) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (ADbOp c oper args res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (APull pulled) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvoc pname args) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AReturn res) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AFail) = ?x" by (auto simp add: isAFail_def)
schematic_goal [simp]: "isAFail (AInvcheck c) = ?x" by (auto simp add: isAFail_def)                            

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
  
  from this obtain s S' where "(s, AInvcheck False) \<in> set tr" and "initialState program ~~ tr \<leadsto>* S'"
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
        case (beginAtomic s ls f ls' t)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := currentTransaction S2(s \<mapsto> t), transactionStatus := transactionStatus S1(t \<mapsto> Uncommited)\<rparr>"])
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
        case (pull s ls vis newTxns newCalls)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
          
        show ?thesis 
          apply (rule exI[where x="S2\<lparr>visibleCalls := visibleCalls S2(s \<mapsto> vis \<union> newCalls)\<rparr>"])
          using induct_step.coupling no_fail pull
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
        case (invCheck s vis res)
        from `initialState program ~~ tr \<leadsto>* S1` `visibleCalls S1 s \<triangleq> vis`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis everything_starts_with_an_invocation in_set_conv_nth option.simps(3) visibleCalls_iff_localState)
          
        show ?thesis 
          apply (rule exI[where x="S2"])
          using induct_step.coupling no_fail invCheck
          by (auto simp add: step_simps state_ext  induct_step)
      qed
    qed
      
      
    thus "[tr\<leftarrow>tr . \<not> isAFail (snd tr)] \<in> traces program"
      by (auto simp add: traces_def)
  qed
qed
  

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
"precondition (s, AFail) C = (\<exists>ls. localState C s \<triangleq> ls)" (* failures occur wherever something is running ;) *)
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
    using 3 exec generatedIds_mono2 by blast
  thus ?thesis
    by (metis "1" "2" "4" ANewId differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
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
    by (metis ABeginAtomic differentSessions exec precondition_beginAtomic) 
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
  case (APull txns) 
  with preconditionHolds obtain ls vis
      where 1: "localState B sb \<triangleq> ls"
      and 2: "currentTransaction B sb = None"
      and 3: "visibleCalls B sb \<triangleq> vis"
      and 4: "\<forall>txn\<in>txns. transactionStatus B txn \<triangleq> Commited"
    by (auto simp add: precondition_pull)
  
  then show ?thesis
    by (metis (mono_tags, lifting) APull aIsNotCommit differentSessions exec mem_Collect_eq precondition_pull snd_conv subsetI transactionStatus_mono2 unchangedInTransaction(1) unchangedInTransaction(3) unchangedInTransaction(4))
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
    by (metis differentSessions exec preconditionHolds precondition_return unchangedInTransaction(1) unchangedInTransaction(2) unchangedInTransaction(3)) 
next
  case AFail
  then show ?thesis
    by (metis differentSessions exec preconditionHolds precondition_fail unchangedInTransaction(1))
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
shows "invContextH co ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs
    = invContextH co ts hbOld cs ki io ir vcs"
apply (simp add: invContextH_def)
using assms apply (auto simp add: restrict_relation_def commitedCallsH_def)
done  

lemma invContext_unchanged_happensBefore2[simp]:
assumes "co c = None"
shows "invContextH co ts (hbOld \<union> vis \<times> {c}) cs ki io ir vcs 
    = invContextH co ts hbOld cs ki io ir vcs "
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
shows "i_visibleCalls (invContextH co ts hbOld cs ki io ir vcs )
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
shows "invContextH (co(c \<mapsto> t)) ts hb cs ki io ir vis  =
       invContextH co ts hb cs ki io ir vis "
using assms by (auto simp add: invContextH_def)

lemma invContextH_update_calls[simp]:
assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommited"
shows "invContextH co ts hb (cs(c \<mapsto> newCall)) ki io ir vis  =
       invContextH co ts hb cs ki io ir vis "
using assms by (auto simp add: invContextH_def commitedCallsH_in)

lemma commitedCallsH_update_uncommited[simp]:
assumes "ts t = None"
shows "commitedCallsH co (ts(t \<mapsto> Uncommited))
     = commitedCallsH co ts"
using assms apply (auto simp add: commitedCallsH_def)
  by force


lemma invContextH_update_txstatus[simp]:
assumes "ts t = None"
shows "invContextH co (ts(t\<mapsto>Uncommited)) hb cs ki io ir vis =
       invContextH co ts hb cs ki io ir vis"
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
assumes "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s \<rbrakk> \<Longrightarrow> traceCorrect trace"
shows "programCorrect program"
  by (auto simp add: assms programCorrect_def traces_def)

lemma currentTransaction_unchangedInternalSteps:
assumes "S ~~ tr \<leadsto>* S'"
  and "\<And>a.  a \<in> set tr \<Longrightarrow> snd a \<noteq> AEndAtomic"
  and "\<And>a tx.  a \<in> set tr \<Longrightarrow> snd a \<noteq> ABeginAtomic tx"
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
shows "currentTransaction S' s = Some t"  and "a \<in> set tr \<Longrightarrow> a \<noteq> (s, ABeginAtomic tx)" 
using assms apply (induct arbitrary: a tx rule: steps.induct)  
 using currentTransaction_unchangedInternalSteps by (auto simp add: step_simps split: if_splits, fastforce+)


lemma currentTransaction_unchangedInternalSteps3:
assumes a1: "s_init ~~ (s, ABeginAtomic tx) # as \<leadsto>* S'"
  and a2: "\<And>st at.  (st, at) \<in> set as \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
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
assumes splitTrace: "tr = (s, ABeginAtomic tx) # txa @ x # rest" 
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
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
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ trStart @ x # (s, ABeginAtomic tx) # txa @ rest \<leadsto>* C)"
apply (auto simp add: steps_append splitTrace)
using local.wf one_compaction_step state_wellFormed_combine txaInTx xOutside by blast+


lemma one_compaction_step3:
assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx) # txa @ x # rest" 
    and splitTrace': "tr' = trStart @ x # (s, ABeginAtomic tx) # txa @ rest"
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
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

lemma transactionIsPackedAlt_case_tx_exists:
assumes "(s, ABeginAtomic tx) \<in> set tr"
shows "transactionIsPackedAlt tr tx \<equiv> 
    \<exists>i s end. 
         i < length tr 
        \<and> tr!i = (s, ABeginAtomic tx)
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

lemma transactionIdsUnique2:
assumes "S ~~ tr \<leadsto>* S'" 
   and "(s, ABeginAtomic tx)\<in>set tr" 
   and "(s', ABeginAtomic tx)\<in>set tr" 
shows "s' = s"
  by (metis Pair_inject assms(1) assms(2) assms(3) in_set_conv_nth transactionIdsUnique)


lemma currentTransaction:
assumes steps: "S ~~ tr \<leadsto>* S'"
   and "i < length tr"
   and "tr!i = (s, ABeginAtomic txi)"
shows "(\<forall>j. i<j \<and> j<length tr \<longrightarrow> tr!j \<noteq> (s, AEndAtomic) \<and> tr!j \<noteq> (s, AFail)) \<longleftrightarrow> currentTransaction S' s \<triangleq> txi"
using assms apply (induct arbitrary: txi i rule: steps.induct)
apply simp
apply (auto simp add: step_simps)
apply (auto simp add: less_Suc_eq nth_append split: if_splits )
apply blast
apply blast
using less_trans apply blast
using less_trans apply blast
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem order.strict_trans)
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
using less_trans apply blast
apply (metis beginAtomicInTrace_to_transactionStatus domIff nth_mem order.strict_trans)
using less_trans by blast+

  
  
lemma noNestedTransactions:
assumes steps: "S ~~ tr \<leadsto>* S'" 
   and "tr!i = (s, ABeginAtomic txi)"
   and "i<j"
   and "j < length tr" 
   and "tr!j = (s, ABeginAtomic txj)"
shows "\<exists>k. i<k \<and> k < j \<and> (tr!k = (s, AEndAtomic) \<or> tr!k = (s, AFail))"
using assms apply (induct rule: steps.induct)
  apply simp
  apply (case_tac "j < length tr")
  apply (metis (no_types, hide_lams) less_trans nth_append)
  apply (subgoal_tac "j = length tr")
  apply auto
  apply (auto simp add: step_simps )
  by (smt currentTransaction nth_append option.simps(3)) (*times out sometimes*)

lemma noNestedTransactions':
assumes steps: "S ~~ tr \<leadsto>* S'" 
   and "tr!i = (s, ABeginAtomic txi)"
   and "i<j"
   and "j < length tr" 
   and "tr!j = (s, ABeginAtomic txj)"
   and "(s, AFail) \<notin> set tr"
shows "\<exists>k. i<k \<and> k < j \<and> tr!k = (s, AEndAtomic) "
using noNestedTransactions[OF steps assms(2) assms(3) assms(4) assms(5) ] assms(6)
  by (metis assms(4) dual_order.strict_trans nth_mem)

  
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

lemma transactionIsPackedAlt_eq2:
assumes steps: "initialState p ~~ tr \<leadsto>* S"
shows "transactionIsPackedAlt tr tx = transactionIsPacked tr tx"
  using steps transactionIdsUnique transactionIsPackedAlt_eq by auto  

find_theorems steps ABeginAtomic

find_theorems "card _ = 0"
    

lemma transactionIsPacked_show:
assumes steps: "initialState p ~~ tr \<leadsto>* S"
    and beginAtomic1: "beginAtomic < endAtomic"
    and beginAtomic2: "tr!beginAtomic = (s, ABeginAtomic tx)"
    and endAtomic1: "endAtomic < length tr"    
    and endAtomic2: "tr!endAtomic = (s, AEndAtomic)"
    and a1: "\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> fst (tr ! i) = s"
shows "transactionIsPacked tr tx"
 (* by (smt a1 beginAtomic1 beginAtomic2 endAtomic1 endAtomic2 fst_conv indexInOtherTransaction_def leI less_imp_le_nat less_trans steps transactionIdsUnique transactionIsPacked_def) *)
proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
  fix k i s'
  assume b0: "k < length tr"
     and b1: "i < k"
     and b2: "tr ! i = (s', ABeginAtomic tx)"
     and b3: "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
  
  from steps b2
  have "i = beginAtomic"
    using b0 b1 beginAtomic1 beginAtomic2 endAtomic1 transactionIdsUnique by auto
  hence "s' = s"
    using b2 beginAtomic2 by auto
    
  from b3
  have "k \<le> endAtomic"
    using \<open>i = beginAtomic\<close> \<open>s' = s\<close> beginAtomic1 endAtomic2 leI by blast
  
  show "fst (tr ! k) = s'"
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
  \<exists>j. j\<le>i \<and> i<length tr \<and> (\<exists>t. tr!j = (s, ABeginAtomic t))
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


lemma " sessionsInTransaction [(s1, ABeginAtomic t\<^sub>1)] 0= {s1}" 
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

lemma if_cases:
"\<lbrakk>c \<Longrightarrow> P t; \<not>c \<Longrightarrow> P f\<rbrakk> \<Longrightarrow>  P (if c then t else f)"
  by auto

lemma if_cases2:
"\<lbrakk>c \<Longrightarrow> X = t; \<not>c \<Longrightarrow> X = f\<rbrakk> \<Longrightarrow>  X = (if c then t else f)"
  by auto  
  
lemma sessionsInTransactionEmptySnoc: 
"sessionsInTransaction (tr@[a]) i = (
if i=length tr then
  if \<exists>t. snd a = ABeginAtomic t then
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
  fix t
  assume a0: "i = length tr"
     and a1: "snd a = ABeginAtomic t"
  
  thus "sessionsInTransaction (tr @ [a]) (length tr) = insert (fst a) (sessionsInTransaction tr (length tr - Suc 0))"
    apply (case_tac a, auto)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    apply (metis Suc_leI Suc_le_mono Suc_pred length_pos_if_in_set less_imp_le_nat nat_neq_iff nth_mem)
    apply (auto simp add: nth_append sessionsInTransaction_def  split: if_splits)[1]
    apply (metis (no_types, lifting) inTransaction_def leD le_eq_less_or_eq length_append_singleton less_Suc_eq nth_append_length)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    done
    
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
   and a1: "\<forall>t. snd a \<noteq> ABeginAtomic t"
   and a2: "snd a \<noteq> AEndAtomic"

  thus "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0)"
    apply (case_tac a, auto)
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)
    by (smt Suc_diff_diff Suc_pred cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel diff_is_0_eq' diff_zero le_trans n_not_Suc_n nat_le_linear not_gr_zero zero_less_diff)
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
    where j1: "min_i < length tr"
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
     using j2 min_i1 by auto
    
   have arith_simp[simp]: "i < min_i - Suc j \<Longrightarrow> Suc j + i \<le> length tr" for i
     using min_simp1 by linarith
    
   have arith_simp2[simp]: "i < min_i - Suc j \<Longrightarrow> Suc (j + i) \<le> length tr" for i
     using arith_simp by auto
   
   have j_len[simp]: "j < length tr"
     using j2 min_i1 by auto
  
    
    
     
   have "tr = trStart @ (s, ABeginAtomic tx) # txa @ (tr!min_i) # rest"
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
    and "\<And>s. (s, AFail) \<notin> set tr"
    and "length insideTx = endAtomic - beginAtomic - 1"
    and "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
    and "tr'' = trStart @ insideTxOther @  (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
     (* NOTE from this assumption, we can later show that everything that was already packed is still packed *)
    and "insideTxOther = filter (\<lambda>a. fst a \<noteq> s) insideTx"
    and "insideTxSame = filter (\<lambda>a. fst a = s) insideTx"
shows "transactionIsPacked tr'' tx 
        \<and> (initialState program ~~ tr'' \<leadsto>* S') 
        \<and> (traceCorrect tr'' \<longleftrightarrow> traceCorrect tr)"
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
  assume noFailInTx: "\<And>s. (s, AFail) \<notin> set tr"
  assume insideTx_len: "length insideTx = endAtomic - beginAtomic - 1"
  assume tr_splitLemma: "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
  assume tr''_split: "tr'' = trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
  assume insideTxOther_def: "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]"
  assume insideTxSame_def: "insideTxSame = [a\<leftarrow>insideTx . fst a = s]" 
  assume ih: "\<forall>m<transactionIsPackedMeasure tr tx.
       \<forall>x. m = transactionIsPackedMeasure x tx \<longrightarrow>
           (initialState program ~~ x \<leadsto>* S') \<longrightarrow>
           (\<forall>xa xb xc. xc < length x \<longrightarrow>
                       x ! xc = (s, ABeginAtomic tx) \<longrightarrow>
                       endAtomic < length x \<longrightarrow>
                       xc < endAtomic \<longrightarrow>
                       x ! endAtomic = (s, AEndAtomic) \<longrightarrow>
                       (\<forall>xa>xc. xa < endAtomic \<longrightarrow> x ! xa \<noteq> (s, AEndAtomic)) \<longrightarrow>
                       (\<forall>s. (s, AFail) \<notin> set x) \<longrightarrow>
                       (\<forall>xd. length xd = endAtomic - xc - 1 \<longrightarrow>
                             x = xb @ (s, ABeginAtomic tx) # xd @ (s, AEndAtomic) # trRest \<longrightarrow>
                             (\<forall>xc xe. xa = xb @ xc @ (s, ABeginAtomic tx) # xe @ (s, AEndAtomic) # trRest \<longrightarrow>
                                      xc = [a\<leftarrow>xd . fst a \<noteq> s] \<longrightarrow> xe = [a\<leftarrow>xd . fst a = s] \<longrightarrow> transactionIsPacked xa tx \<and> (initialState program ~~ xa \<leadsto>* S') \<and> traceCorrect xa = traceCorrect x)))"
  (* show "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect  tr'' = traceCorrect  tr" *)
    
  have inductionHypothesis2: 
          "transactionIsPacked tr'' tx 
        \<and> (initialState program ~~ tr'' \<leadsto>* S') 
        \<and> (traceCorrect tr'' \<longleftrightarrow> traceCorrect tr')"
     if a1: "initialState program ~~ tr' \<leadsto>* S'"
    and a2: "Suc beginAtomic < length tr'"
    and a3: "tr' ! Suc beginAtomic = (s, ABeginAtomic tx)"
    and a4: "endAtomic < length tr'"
    and a5: "Suc beginAtomic < endAtomic"
    and a6: "tr' ! endAtomic = (s, AEndAtomic)"
    and a7: "\<And>i. \<lbrakk>Suc beginAtomic<i; i<endAtomic\<rbrakk> \<Longrightarrow> tr' ! i \<noteq> (s, AEndAtomic)"
    and no_AFail: "\<And>s. (s, AFail) \<notin> set tr'"
    and a8: "length insideTx = endAtomic - Suc beginAtomic - 1"
    and a9: "tr' = trStart' @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
    and a10: " tr'' = trStart' @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
    and a11: "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]"
    and a12: "insideTxSame = [a\<leftarrow>insideTx . fst a = s]"
    and measureDecr: "transactionIsPackedMeasure tr' tx < transactionIsPackedMeasure tr tx"
    for tr' tr'' trStart' insideTx insideTxOther insideTxSame::"(session \<times> action) list" and beginAtomic::nat
    using that ih  by blast
    
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
  
  have insideTx_noFail: "(s, AFail) \<notin> set insideTx" 
    using noFailInTx tr_splitLemma by auto
  
  hence insideTx_noFail: "insideTx ! i \<noteq> (s, AFail)" if "i < length insideTx" for i
    by (simp add: in_set_conv_nth that)
  
  
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
  
    
  
  show "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect tr'' = traceCorrect tr"
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
    have tr_split2h': "a \<noteq> (s, AFail)" if "a \<in> set txa" for  a  
      using that noFailInTx apply (auto simp add: in_set_conv_nth)
      by (metis (no_types, lifting) Suc_less_eq insideTx_len insideTx_noFail insideTx_split less_SucI less_trans_Suc nth_append_first txa_len)
    hence tr_split2: "fst a = s \<and> snd a \<noteq> AEndAtomic \<and> snd a \<noteq> AFail" if "a \<in> set txa" for a
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
        ultimately show "fst a = s \<and> snd a \<noteq> AEndAtomic \<and> snd a \<noteq> AFail"
          using that tr_split2h tr_split2h'  by fastforce
      qed
    
    have tr_split3: "s \<noteq> fst (tr ! kmin)"
      using beginAtomicUnique indexInOtherTransaction_def kmin_inTx tr_beginAtomic by auto  
      
      
    have "min_s \<noteq> s"
      using min_s_def tr_split3 by auto
      
      
      
    obtain tr' where tr'_def:
      "tr' = trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ rest" by simp
    
    have tr'_def2:
      "tr' = trStart @ (min_s, min_a) # (s, ABeginAtomic tx) # txa @ txb @ (s, AEndAtomic) # trRest"
      by (simp add: \<open>rest \<equiv> txb @ (s, AEndAtomic) # trRest\<close> tr'_def)
      
      
    from tr_split2
    have tr_split2': "\<And>st at. (st, at) \<in> set txa \<Longrightarrow> st = s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail"
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
    have preservesCorrectness: "traceCorrect tr' = traceCorrect tr"
      proof (rule show_traceCorrect_same)
        show "set tr = set tr'"
          by (auto simp add: tr'_def tr_split )
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
      
      
      
    
    have "transactionIsPacked tr'' tx \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> traceCorrect tr'' = traceCorrect tr'"  
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
      show "\<And>s. (s, AFail) \<notin> set tr'"
        using noFailInTx tr'_sameSet by auto
         
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


definition transactionIsClosed :: "trace \<Rightarrow> txid \<Rightarrow> bool" where
"transactionIsClosed tr tx \<equiv>
  \<forall>i s. i<length tr \<and> tr!i = (s, ABeginAtomic tx) \<longrightarrow> (\<exists>j. j>i \<and> j<length tr \<and> tr!j = (s, AEndAtomic))"


definition actionInOpenTransaction where
"actionInOpenTransaction tx  tr i \<equiv> 
  \<forall>s a. tr!i = (s,a) 
    \<longrightarrow> (\<exists>k. k\<le>i \<and> tr!k = (s, ABeginAtomic tx) \<and> (\<forall>j. j>k \<and> j<length tr \<longrightarrow> tr!j \<noteq> (s, AEndAtomic)))"
  
lemma transactionIsClosed_def2:
shows "transactionIsClosed tr tx \<longleftrightarrow> (\<forall>i. i<length tr \<longrightarrow> \<not>actionInOpenTransaction  tx tr i)"
  by (auto simp add: transactionIsClosed_def actionInOpenTransaction_def)
  
  
fun transactionIsClosedFun where 
  empty: 
  "transactionIsClosedFun [] tx = True" 
| beginAtomic:
  "transactionIsClosedFun ((s, ABeginAtomic tx')#tr) tx = (
            if tx' = tx then (s, AEndAtomic) \<in> set tr \<and> transactionIsClosedFun tr tx
            else transactionIsClosedFun tr tx)"
| other:
  "transactionIsClosedFun (_#tr) tx = transactionIsClosedFun tr tx"
    
  
lemma transactionIsClosed_def3:
"transactionIsClosed tr tx \<longleftrightarrow> 
 (\<forall>i s. i<length tr \<and> tr!i = (s, ABeginAtomic tx) \<longrightarrow> (s, AEndAtomic)\<in>set (drop (Suc i) tr))"
apply (auto simp add: transactionIsClosed_def in_set_conv_nth)
  apply (smt Suc_leI add.commute add_diff_cancel_left' append_take_drop_id le_Suc_ex length_take less_SucE less_diff_conv min.absorb2 not_less_iff_gr_or_eq nth_append)
  by (smt Groups.add_ac(3) Suc_eq_plus1 add.commute less_add_same_cancel1 less_diff_conv less_imp_le_nat not_less_eq nth_drop zero_order(3))

 

lemma transactionIsClosed_fun_eq: "transactionIsClosed tr tx \<longleftrightarrow> transactionIsClosedFun tr tx"
apply (induct tr tx rule: transactionIsClosedFun.induct)
apply auto
apply (simp add: transactionIsClosed_def)
apply (auto simp add: transactionIsClosed_def3 nth_Cons'  split: if_splits)
by (metis Suc_pred diff_Suc_less dual_order.strict_trans less_SucE)+
  
declare [[show_question_marks = false]]  
  
lemma notPackedExists:
assumes "\<not> transactionIsPacked tr tx"
shows "\<exists>s. (s, ABeginAtomic tx)\<in>set tr"
using assms apply (auto simp add: transactionIsPacked_def indexInOtherTransaction_def )
  by (metis dual_order.strict_trans nth_mem)



lemma canSplitUnpackedTransaction:
assumes steps: "initialState program ~~ tr \<leadsto>* S'"
 and transactionExists: "(s, ABeginAtomic tx)\<in>set tr"
 and transactionIsClosed: "transactionIsClosed tr tx"
shows "\<exists>beginAtomic s endAtomic insideTx trStart trRest.
       beginAtomic < length tr 
       \<and> tr ! beginAtomic = (s, ABeginAtomic tx) 
       \<and> endAtomic < length tr 
       \<and> beginAtomic < endAtomic 
       \<and> tr ! endAtomic = (s, AEndAtomic)
       \<and> (\<forall>i>beginAtomic. i < endAtomic \<longrightarrow> tr ! i \<noteq> (s, AEndAtomic))
       \<and> length insideTx = endAtomic - beginAtomic - 1 
       \<and> tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
proof -
  find_theorems transactionIsPacked
  from transactionExists
  obtain beginAtomic
    where a1: "beginAtomic < length tr"
      and a2: "tr ! beginAtomic = (s, ABeginAtomic tx) "
    by (meson in_set_conv_nth)
  with transactionIsClosed
  obtain i
    where endAtomic_props: "i < length tr  \<and> beginAtomic < i \<and> tr ! i = (s, AEndAtomic)"
    by (auto simp add: transactionIsClosed_def)
  
  define endAtomic where "endAtomic = (LEAST i. i < length tr  \<and> beginAtomic < i \<and> tr ! i = (s, AEndAtomic))"
    
  from endAtomic_props endAtomic_def
  have endAtomic_props': "endAtomic < length tr  \<and> beginAtomic < endAtomic \<and> tr ! endAtomic = (s, AEndAtomic)"
    by (metis (mono_tags, lifting) LeastI_ex)
  hence ea1[simp]: "endAtomic < length tr"
    and ea2[simp]: "beginAtomic < endAtomic"
    and ea3: "tr ! endAtomic = (s, AEndAtomic)"
    by auto
    
  define insideTx where "insideTx = drop (1+beginAtomic) (take endAtomic tr)"
  
  from insideTx_def
  have insideTx_len: "length insideTx = endAtomic - beginAtomic - 1 "
    by (simp add: less_imp_le_nat min.absorb2)
    
  define trStart where "trStart = take beginAtomic tr"
  define trRest where "trRest = drop (endAtomic+1) tr"
    
  have tr_split:
     "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"  
   apply (auto simp add: trStart_def trRest_def insideTx_def)
   by (smt Cons_nth_drop_Suc Suc_leI a2 add.commute append_take_drop_id drop_drop drop_take endAtomic_props' leD length_append length_drop length_take less_trans min_absorb2 min_def)
     
  have noEndAtomic: 
    "(\<forall>i>beginAtomic. i < endAtomic \<longrightarrow> tr ! i \<noteq> (s, AEndAtomic))"  
    apply auto
    using endAtomic_def endAtomic_props' less_trans not_less_Least by blast
  
  show ?thesis
    using a1 a2 endAtomic_props' insideTx_len noEndAtomic tr_split by blast
qed
       
lemma beginAndEndOfPackedTransaction:
assumes steps: "initialState program ~~ tr \<leadsto>* S'"
    and exists: "(s, ABeginAtomic tx) \<in> set tr"
    and packed: "transactionIsPacked tr tx"
    and closed: "transactionIsClosed tr tx"
    and noFail: "(s, AFail) \<notin> set tr"
shows "\<exists>beginAtomic endAtomic. 
        beginAtomic < length tr
      \<and> beginAtomic < endAtomic  
      \<and> endAtomic < length tr
      \<and> tr ! beginAtomic = (s, ABeginAtomic tx)
      \<and> tr ! endAtomic = (s, AEndAtomic)
      \<and> (\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> fst (tr!i) = s)
      \<and> (\<forall>i. beginAtomic \<le> i \<and> i < endAtomic \<longrightarrow> snd (tr!i) \<noteq> AEndAtomic)
      \<and> (\<forall>i t. beginAtomic < i \<and> i < endAtomic \<longrightarrow> snd (tr!i) \<noteq> ABeginAtomic t)"
proof -
  from exists obtain beginAtomic
    where beginAtomic1: "beginAtomic < length tr" 
      and beginAtomic2: "tr ! beginAtomic = (s, ABeginAtomic tx)"
    by (meson in_set_conv_nth)
  
  from closed obtain e
    where e_prop: "e < length tr \<and> beginAtomic < e \<and>  tr ! e = (s, AEndAtomic)"
    using beginAtomic1 beginAtomic2 by (auto simp add: transactionIsClosed_def)
  
  define endAtomic where "endAtomic = (LEAST e. e < length tr \<and> beginAtomic < e \<and>  tr ! e = (s, AEndAtomic))"
  
  have e_prop': "endAtomic < length tr \<and> beginAtomic < endAtomic \<and>  tr ! endAtomic = (s, AEndAtomic)"
    by (metis (mono_tags, lifting) LeastI_ex e_prop endAtomic_def)
  hence e1: "endAtomic < length tr" 
    and e2: "beginAtomic < endAtomic"
    and e3: "tr ! endAtomic = (s, AEndAtomic)" 
    by auto
    
  from packed
  have packed1: "(\<forall>i. beginAtomic \<le> i \<and> i \<le> endAtomic \<longrightarrow> fst (tr!i) = s)"
    apply (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
    apply (drule_tac x=i in spec)
    apply auto
    using e1 apply linarith
    by (smt endAtomic_def antisym_conv2 beginAtomic2 e1 fst_conv less_trans not_less_Least)
  have packed2: "(\<forall>i. beginAtomic \<le> i \<and> i < endAtomic \<longrightarrow> snd (tr!i) \<noteq> AEndAtomic)"
    by (smt endAtomic_def action.distinct(35) beginAtomic2 e1 le_eq_less_or_eq less_trans not_less_Least packed1 prod.collapse prod.inject)
  
  have packed3: "snd (tr!i) \<noteq> ABeginAtomic t" if t1: "beginAtomic < i" and t2: "i < endAtomic" for i t
  proof (rule ccontr)
    assume "\<not> snd (tr ! i) \<noteq> ABeginAtomic t"
    from this have t3: "tr ! i = (s, ABeginAtomic t)"
      by (metis less_imp_le_nat packed1 prod.collapse t1 t2)
      
    thm noNestedTransactions[OF steps]  
    have "\<exists>k>beginAtomic. k < i \<and> (tr ! k = (s, AEndAtomic) \<or> tr ! k = (s, AFail))"
    proof (rule noNestedTransactions[OF steps])
      show "tr ! beginAtomic = (s, ABeginAtomic tx)" using beginAtomic2 .
      show "beginAtomic < i" using t1 .
      show "i < length tr"
        using e1 t2 by auto 
      show "tr ! i = (s, ABeginAtomic t)" using t3 .
    qed
    hence "\<exists>k>beginAtomic. k < i \<and> tr ! k = (s, AEndAtomic)"
      using noFail by (metis dual_order.strict_trans e_prop' nth_mem t2) 
    thus False
      by (metis less_imp_le_nat less_trans packed2 snd_conv t2) 
  qed    
    
    
  show ?thesis
    using beginAtomic1 beginAtomic2 e_prop' packed1 packed2 packed3 by blast
qed    
   


lemma filter_injection:
assumes "ys = filter P xs"
shows "\<exists>f. 
    strict_mono f
  \<and> (\<forall>i<length ys. f i < length xs \<and> ys ! i = xs ! f i )
  \<and> (\<forall>i<length xs. P (xs!i) \<longrightarrow> (\<exists>j<length ys. f j = i \<and> ys!j = xs!i))"
proof (auto simp add: assms)
  show "\<exists>f. strict_mono f 
      \<and> (\<forall>i<length (filter P xs). f i < length xs \<and> filter P xs ! i = xs ! f i)
      \<and> (\<forall>i<length xs. P (xs ! i) \<longrightarrow> (\<exists>j<length (filter P xs). f j = i \<and> filter P xs ! j = xs ! i))"
  proof (induct xs)
    case Nil
    then show ?case 
      apply (rule_tac x=id in exI)
      by (simp add: strict_monoI) 
  next
    case (Cons x xs)
    
    from this
    obtain f where f_mono: "strict_mono f" 
      and f2: "\<forall>i<length (filter P xs). f i < length xs \<and> filter P xs ! i = xs ! f i"
      and f3: "\<forall>i<length xs. P (xs ! i) \<longrightarrow> (\<exists>j<length (filter P xs). f j = i \<and> filter P xs ! j = xs ! i)"
      by blast
    
    show ?case 
    proof (cases "P x")
      case False
      
      define f' where "f' = (\<lambda>x. 1 + f x)"

      have f'_mono: "strict_mono f'"
        using f'_def f_mono
        by (simp add: strict_mono_def) 
      
      show ?thesis 
        apply (rule_tac x=f' in exI)
        apply (simp add: False f'_mono)
        apply (auto simp add: f'_def f2 f3)
        using False f3 less_Suc_eq_0_disj by auto
        
    next
      case True
      
      define f' where "f' = (\<lambda>x. if x = 0 then 0 else  1 + f (x-1))"
      
      have f'_mono: "strict_mono f'"
        using f'_def f_mono
        by (simp add: strict_mono_def) 
      
      show ?thesis 
        apply (rule_tac x=f' in exI)
        apply (simp add: True f'_mono)
        apply auto
        using f'_def f2 apply auto[1]
        using f'_def f2 apply auto[1]
        apply (case_tac i)
        apply auto
        apply (simp add: f'_def)
        by (metis One_nat_def comm_monoid_add_class.add_0 diff_Suc_1 f'_def f3 not_less_eq nth_Cons_pos plus_nat.simps(2) zero_less_Suc)
    qed
  qed
qed

lemma show_transactionIsClosed2:
assumes "\<And>i s. \<lbrakk>i<length tr; tr!i = (s, ABeginAtomic tx)\<rbrakk> \<Longrightarrow> (s, AEndAtomic)\<in>set (drop (Suc i) tr)"
shows "transactionIsClosed tr tx"
using assms apply (auto simp add: transactionIsClosed_def)
apply (drule_tac x=i in meta_spec)
apply (drule_tac x=s in meta_spec)
apply auto
apply (auto simp add: in_set_conv_nth )
using less_diff_conv by fastforce

lemma show_transactionIsClosed:
assumes "\<And>i s. \<lbrakk>i<length tr; tr!i = (s, ABeginAtomic tx)\<rbrakk> \<Longrightarrow> \<exists>j. i<j \<and>  j<length tr \<and> tr!j = (s, AEndAtomic)"
shows "transactionIsClosed tr tx"
using assms by (auto simp add: transactionIsClosed_def)

lemma use_transactionIsClosed:
assumes "transactionIsClosed tr tx"
  and "i < length tr"
  and "tr!i = (s, ABeginAtomic tx)"
shows "\<exists>j. i<j \<and> j<length tr \<and> tr!j = (s, AEndAtomic)"
  using assms(1) assms(2) assms(3) transactionIsClosed_def by blast

lemma transactionIsClosed_cons:
"transactionIsClosed (a#tr) tx \<longleftrightarrow>
  (case a of 
    (s, ABeginAtomic tx') \<Rightarrow> 
      if tx' = tx then (s, AEndAtomic) \<in> set tr \<and> transactionIsClosed tr tx
      else transactionIsClosed tr tx
    | _ \<Rightarrow> transactionIsClosed tr tx)"
apply (subst transactionIsClosed_fun_eq)
by (auto simp add: transactionIsClosed_fun_eq split: action.splits)

  
lemma transactionIsClosed_filter_simp:
assumes a: "\<And>s'. (s', ABeginAtomic tx)\<in>set tr \<Longrightarrow> s' = s"
shows "(transactionIsClosed [a\<leftarrow>tr . fst a = s] tx) \<longleftrightarrow> transactionIsClosed tr tx"
apply (unfold transactionIsClosed_fun_eq)
using a proof (induct rule: transactionIsClosedFun.induct)
  case (1 tx)
  then show ?case by auto
next
  case (2 s tx' tr tx)
  show ?case by (auto simp add: 2)
qed (auto)    




lemma canPackOneTransaction2:
assumes steps: "initialState program ~~ tr \<leadsto>* S'"
  and transactionIsClosed: "\<And>tx. transactionIsClosed tr tx"
  and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "\<exists>tr'. transactionIsPacked tr' tx 
        \<and> (initialState program ~~ tr' \<leadsto>* S') 
        \<and> (\<forall>t. transactionIsPacked tr t \<longrightarrow>  transactionIsPacked tr' t)
        \<and> (\<forall>tx. transactionIsClosed tr' tx)
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (traceCorrect tr' \<longleftrightarrow> traceCorrect tr)"
proof (cases "transactionIsPacked tr tx")
  case True
  with steps
  show ?thesis using transactionIsClosed noFail by blast
next
  case False
  hence notPacked: "\<not> transactionIsPacked tr tx" .
  from notPacked obtain s
    where txExists: "(s, ABeginAtomic tx) \<in> set tr"
    using notPackedExists by blast 
  
  
  from canSplitUnpackedTransaction[OF steps txExists transactionIsClosed]
  obtain beginAtomic endAtomic s trStart insideTx trRest
    where a1: "beginAtomic < length tr"
    and a2: "tr ! beginAtomic = (s, ABeginAtomic tx)"
    and a3: "endAtomic < length tr"
    and a4: "beginAtomic < endAtomic"
    and a5: "tr ! endAtomic = (s, AEndAtomic)"
    and a6: "\<And>i. \<lbrakk>beginAtomic < i; i < endAtomic\<rbrakk> \<Longrightarrow> tr ! i \<noteq> (s, AEndAtomic)"
    and a7: "length insideTx = endAtomic - beginAtomic - 1"
    and a8: "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest"
    by blast
  
  have trStart_len: "length trStart = beginAtomic"
    using a1 a2 a8 steps transactionIdsUnique by auto
    
  
    
  define insideTxOther where  "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]"
  define insideTxSame where "insideTxSame = [a\<leftarrow>insideTx . fst a = s]"
  define tr' where "tr' = trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest"
  
  (*from canPackOneTransaction[OF steps a1 a2 a3 a4 a5]*)
  have "transactionIsPacked tr' tx 
     \<and> (initialState program ~~ tr' \<leadsto>* S') 
     \<and> traceCorrect tr' = traceCorrect tr"
  proof (rule canPackOneTransaction)
    show "initialState program ~~ tr \<leadsto>* S'" using steps .
    show "beginAtomic < length tr" using a1 . 
    show "tr ! beginAtomic = (s, ABeginAtomic tx)" using a2 .
    show "endAtomic < length tr" using a3 .
    show "beginAtomic < endAtomic" using a4 .
    show "tr ! endAtomic = (s, AEndAtomic)" using a5 .
    show "\<And>i. \<lbrakk>beginAtomic < i; i < endAtomic\<rbrakk> \<Longrightarrow> tr ! i \<noteq> (s, AEndAtomic)" using a6 .
    show "length insideTx = endAtomic - beginAtomic - 1" using a7 .
    show "tr = trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest" using a8 .
    show "tr' = trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest" using tr'_def .
    show "insideTxOther = [a\<leftarrow>insideTx . fst a \<noteq> s]" using insideTxOther_def .
    show "insideTxSame = [a\<leftarrow>insideTx . fst a = s]" using insideTxSame_def .
    show "\<And>s. (s, AFail) \<notin> set tr" using noFail .
  qed
  hence tr'1: "transactionIsPacked tr' tx" 
    and tr'2: "(initialState program ~~ tr' \<leadsto>* S')"
    and tr'3: "traceCorrect tr' = traceCorrect tr"
    by auto
  
  have insideTx_set: "set insideTx = set insideTxOther \<union> set insideTxSame"
    by (auto simp add: insideTxOther_def insideTxSame_def)
  hence tr'_sameSet: "set tr' = set tr"  
    by (auto simp add: tr'_def a8)
  
  have insideTx_len: "length insideTx = length insideTxOther + length insideTxSame"
    apply (auto simp add: insideTxOther_def insideTxSame_def)
    by (metis filter_cong sum_length_filter_compl)
    
    
  have tr'_same_start: "tr'!i = tr!i" if "i<beginAtomic" for i
    using that by (auto simp add: tr'_def a8 trStart_len nth_append_first)
  
  have tr'_same_endAtomic: "tr' ! endAtomic = tr ! endAtomic"
    using a4 a7 trStart_len insideTx_len by (auto simp add: tr'_def a8  nth_append nth_Cons split: nat.splits if_splits)
    
  have tr'_same_end: "tr'!i = tr!i" if "i>endAtomic" for i
    using that proof -
      have "tr'!i = (trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ (s, AEndAtomic) # trRest) ! i"
        using tr'_def by simp
      moreover have "...
          = ((trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ [(s, AEndAtomic)]) @ trRest) ! i"
          by simp
      moreover have "... = trRest ! (i - length (trStart @ insideTxOther @ (s, ABeginAtomic tx) # insideTxSame @ [(s, AEndAtomic)]))"
        apply (rule nth_append_second)
        apply auto
        using a4 a7 insideTx_len that trStart_len by linarith
      moreover have "... = trRest ! (i - endAtomic - 1)"
        using Suc_diff_Suc a4 a7 insideTx_len trStart_len by auto  
      ultimately have tr'_i: "tr'!i = trRest ! (i - endAtomic - 1)"
        by presburger 

      have "tr!i = (trStart @ (s, ABeginAtomic tx) # insideTx @ (s, AEndAtomic) # trRest) ! i"
        by (simp add: a8)
      moreover have "... = ((trStart @ (s, ABeginAtomic tx) # insideTx @ [(s, AEndAtomic)]) @ trRest) ! i"
        by simp
      moreover have "... = trRest ! (i - length (trStart @ (s, ABeginAtomic tx) # insideTx @ [(s, AEndAtomic)]))"
        apply (rule nth_append_second)
        apply auto
        using a4 a7 insideTx_len that trStart_len by linarith
      moreover have "... =  trRest ! (i - endAtomic - 1)"
        using Suc_diff_Suc a4 a7 trStart_len by auto
      ultimately have "tr!i = trRest ! (i - endAtomic - 1)"
        by presburger

      with tr'_i show "tr'!i = tr!i"
        by simp
    qed
  
  have tr'_same_end2: "tr'!i = tr!i" if "i\<ge>endAtomic" for i
    using antisym_conv2 that tr'_same_end tr'_same_endAtomic by auto  
  
    
  have tr_filtered_same: "[a\<leftarrow>tr' . fst a = ses] = [a\<leftarrow>tr . fst a = ses]" for ses
    apply (auto simp add: a8 tr'_def insideTxOther_def insideTxSame_def)
    by metis
  
  have noFail': "(s, AFail) \<notin> set tr'" for s
    by (simp add: noFail tr'_sameSet)
    
  
  have transactionIsClosed': "transactionIsClosed tr' tx" for tx
  proof - 
    { 
      fix ses
      assume hasBegin': "(ses, ABeginAtomic tx)\<in>set tr'"
      hence hasBegin: "(ses, ABeginAtomic tx)\<in>set tr"
        by (simp add: tr'_sameSet)
        
      
      have "transactionIsClosed [a\<leftarrow>tr . fst a = ses] tx"
      proof (rule transactionIsClosed_filter_simp[THEN iffD2]) 
        show "transactionIsClosed tr tx" using transactionIsClosed .
        show "\<And>s'. (s', ABeginAtomic tx) \<in> set tr \<Longrightarrow> s' = ses"
          using hasBegin steps transactionIdsUnique2 by blast 
      qed    
      
      hence h: "transactionIsClosed [a\<leftarrow>tr' . fst a = ses] tx"
        by (simp add: tr_filtered_same)
      
      have "transactionIsClosed tr' tx"
      proof (rule transactionIsClosed_filter_simp[THEN iffD1])
        show "transactionIsClosed [a\<leftarrow>tr' . fst a = ses] tx" using h .
        show "\<And>s'. (s', ABeginAtomic tx) \<in> set tr' \<Longrightarrow> s' = ses"
          using hasBegin steps tr'_sameSet transactionIdsUnique2 by blast
      qed    
    }
    thus "transactionIsClosed tr' tx"
      using nth_mem transactionIsClosed_def3 by fastforce
  qed  
    
  
    
  have "transactionIsPacked tr' t" if packedBefore: "transactionIsPacked tr t" for t
  proof (cases "\<exists>s'. (s', ABeginAtomic t) \<in> set tr")
    case False
    hence "\<nexists>s'. (s', ABeginAtomic t) \<in> set tr'"
      by (auto simp add: tr'_sameSet)
    thus "transactionIsPacked tr' t"
      apply (auto simp add:  transactionIsPacked_def indexInOtherTransaction_def)
      by (metis dual_order.strict_trans nth_mem)
  next
    case True
    from this obtain s'
      where hasBegin: "(s', ABeginAtomic t) \<in> set tr " by force
    
    have closed: "transactionIsClosed tr t"
      by (simp add: transactionIsClosed)   
      
    from beginAndEndOfPackedTransaction[OF steps hasBegin packedBefore closed noFail]  
    obtain beginAtomic' endAtomic'
       where b1: "beginAtomic' < length tr"
       and b2: "beginAtomic' < endAtomic'"
       and b3: "endAtomic' < length tr"
       and b4: "tr ! beginAtomic' = (s', ABeginAtomic t)"
       and b5: "tr ! endAtomic' = (s', AEndAtomic)"
       and b6: "\<forall>i. beginAtomic' \<le> i \<and> i \<le> endAtomic' \<longrightarrow> fst (tr ! i) = s'"
       and b7: "\<forall>i. beginAtomic' \<le> i \<and> i < endAtomic' \<longrightarrow> snd (tr ! i) \<noteq> AEndAtomic"
       and b7: "\<forall>i t. beginAtomic' < i \<and> i < endAtomic' \<longrightarrow> snd (tr ! i) \<noteq> ABeginAtomic t"
      by blast
    
    (* look at different places where beginAtomic' is starting*)  
    {
      assume part1b: "beginAtomic' < beginAtomic"
      hence part1e: "endAtomic' < beginAtomic"
        using a2 b5 b7 less_linear by fastforce
           
      have "transactionIsPacked tr' t"
      proof (rule transactionIsPacked_show)
        show "initialState program ~~ tr' \<leadsto>* S'" using tr'2 .
        show "beginAtomic' < endAtomic'" using b2 .
        show "tr' ! beginAtomic' = (s', ABeginAtomic t)"
          using b4
          by (simp add: \<open>beginAtomic' < beginAtomic\<close> tr'_same_start) 
        show "endAtomic' < length tr'"
          using part1e tr'_def trStart_len by auto
        show "tr' ! endAtomic' = (s', AEndAtomic)"
          using b5 part1e tr'_same_start by auto
        show "\<forall>i. beginAtomic' \<le> i \<and> i \<le> endAtomic' \<longrightarrow> fst (tr' ! i) = s'"
          using b6 part1e tr'_same_start by auto
      qed    
    }
    moreover 
    {
      assume "beginAtomic' = beginAtomic"
      hence "transactionIsPacked tr' t"
        using a2 b4 tr'1 by auto
    }
    moreover
    {
      assume l1: "beginAtomic < beginAtomic'" and l2: "beginAtomic' < endAtomic "
      have "endAtomic' < endAtomic"
      proof (rule ccontr)
        assume "\<not> endAtomic' < endAtomic"
        hence "endAtomic' \<ge> endAtomic" by simp

        with b6
        have "fst (tr ! endAtomic) = s'"
          using l2 less_or_eq_imp_le by blast
        hence "s' = s"
          using a5 by auto
          
        from steps a2 l1 b1 
        have "\<exists>k>beginAtomic. k < beginAtomic' \<and> tr ! k = (s, AEndAtomic)"
        proof (rule noNestedTransactions')
          from b4
          show "tr ! beginAtomic' = (s, ABeginAtomic t)" using `s' = s` by simp
          show "(s, AFail) \<notin> set tr" using noFail .
        qed
        thus False
          using a6 l2 by auto
       qed   
      
      have [simp]: "tx \<noteq> t"
        using notPacked that by blast  
        
      have [simp]: "s \<noteq> s'"
        using \<open>endAtomic' < endAtomic\<close> a6 b2 b5 l1 less_trans by blast
        
                
      define beginAtomic'2 where "beginAtomic'2 = beginAtomic' - beginAtomic - 1"
      define endAtomic'2 where "endAtomic'2 = endAtomic' - beginAtomic - 1"
      
      have begin_before_end2: "beginAtomic'2 < endAtomic'2"
        using \<open>beginAtomic'2 \<equiv> beginAtomic' - beginAtomic - 1\<close> \<open>endAtomic'2 \<equiv> endAtomic' - beginAtomic - 1\<close> b2 l1 by auto
      
      have "beginAtomic'2 < length insideTx"
        using \<open>beginAtomic'2 \<equiv> beginAtomic' - beginAtomic - 1\<close> a7 l1 l2 by linarith
     
      have "endAtomic'2 < length insideTx"
        by (smt One_nat_def Suc_diff_Suc Suc_less_SucD \<open>endAtomic' < endAtomic\<close> \<open>endAtomic'2 \<equiv> endAtomic' - beginAtomic - 1\<close> a7 add_diff_inverse_nat b2 diff_zero dual_order.strict_trans l1 minus_nat.simps(2) nat_add_left_cancel_less order.asym)
        
      have [simp]: "insideTx ! beginAtomic'2 = (s', ABeginAtomic t)"
        using b4 beginAtomic'2_def trStart_len apply (auto simp add: a8 nth_append nth_Cons' split: if_splits)
        using l1 not_less_iff_gr_or_eq trStart_len apply blast
        using \<open>beginAtomic'2 < length insideTx\<close> by blast
      have [simp]: "insideTx ! endAtomic'2 = (s', AEndAtomic)"
        using b5 endAtomic'2_def trStart_len apply (auto simp add: a8 nth_append nth_Cons' split: if_splits)
        using b2 l1 order.strict_trans apply blast
        using \<open>endAtomic'2 < length insideTx\<close> by blast
         
      
        
      obtain f
        where f_mono: "strict_mono f"
        and  f_exists: "\<And>i. \<lbrakk>i<length insideTx; fst (insideTx ! i) \<noteq> s\<rbrakk> \<Longrightarrow> \<exists>j<length insideTxOther. f j = i \<and> insideTxOther ! j = insideTx ! i"
        and f_map: "\<And>i. \<lbrakk>i<length insideTxOther\<rbrakk> \<Longrightarrow>  insideTxOther ! i = insideTx ! f i"
        and f_map2: "\<And>i. \<lbrakk>i<length insideTxOther\<rbrakk> \<Longrightarrow>  f i < length insideTx"
        using filter_injection[OF insideTxOther_def]
        by blast 
        
      obtain beginAtomic'3 
        where beginAtomic'3a: "beginAtomic'3 < length insideTxOther"
          and beginAtomic'3b: "f beginAtomic'3 = beginAtomic'2"
          using f_exists[OF `beginAtomic'2 < length insideTx`] \<open>s \<noteq> s'\<close> by auto 

      obtain endAtomic'3 
        where endAtomic'3a: "endAtomic'3 < length insideTxOther"
          and endAtomic'3b: "f endAtomic'3 = endAtomic'2"
          using f_exists[OF `endAtomic'2 < length insideTx`] \<open>s \<noteq> s'\<close> by auto           
        
      have "transactionIsPacked tr' t"
      proof (rule transactionIsPacked_show)
        show "initialState program ~~ tr' \<leadsto>* S'" using tr'2 .
        show "beginAtomic'3 + beginAtomic < endAtomic'3 + beginAtomic"
          using add_strict_right_mono beginAtomic'3b begin_before_end2 endAtomic'3b f_mono strict_mono_less by blast
        have beginAtomic'2_inisdeTx: "insideTx ! beginAtomic'2 = (s', ABeginAtomic t)"
          using b4 
          apply (auto simp add: a8 beginAtomic'2_def nth_append nth_Cons' trStart_len split: if_splits)
          using l1 not_less_iff_gr_or_eq trStart_len apply blast
          using a7 l2 by linarith
        hence beginAtomic'3_insideTx: "insideTxOther ! beginAtomic'3 = (s', ABeginAtomic t)"
          by (simp add: \<open>beginAtomic'2 < length insideTx\<close> beginAtomic'3a beginAtomic'3b f_map)  
          
        have endAtomic'2_insideTx: "insideTx ! endAtomic'2 = (s', AEndAtomic)"
          using b5
          apply (auto simp add: a8 endAtomic'2_def nth_append nth_Cons' trStart_len split: if_splits)
          using b2 l1 less_trans apply blast
          using \<open>endAtomic' < endAtomic\<close> a7 by linarith
        hence endAtomic'3_insideTx: "insideTxOther ! endAtomic'3 = (s', AEndAtomic)"
          by (simp add: \<open>endAtomic'2 < length insideTx\<close> endAtomic'3a endAtomic'3b f_map)
          
          
        show "tr' ! (beginAtomic'3 + beginAtomic) = (s', ABeginAtomic t)"
          using beginAtomic'3_insideTx  by (auto simp add: tr'_def nth_append nth_Cons' trStart_len beginAtomic'3a)
        show "endAtomic'3 + beginAtomic < length tr'"
          apply (auto simp add: tr'_def trStart_len )
          using endAtomic'3a by presburger
        show "tr' ! (endAtomic'3 + beginAtomic) = (s', AEndAtomic)"
          using endAtomic'3_insideTx by (auto simp add: tr'_def nth_append nth_Cons' trStart_len endAtomic'3a)
         
        have h1: "fst x \<noteq> s" if "x\<in>set insideTxOther" for x
          using that by (auto simp add: insideTxOther_def)
          
        have h2: "fst (insideTxOther ! i) = s'" if " beginAtomic'3 \<le> i" and "i \<le> endAtomic'3" for i
        proof (rule ccontr)
          assume a: "fst (insideTxOther ! i) \<noteq> s'"
          
          have i_insideTxOther: "i < length insideTxOther"
            using endAtomic'3a le_less_trans that(2) by blast
          hence "insideTxOther ! i = insideTx ! f i"
            using f_map by blast

            
          with a
          have "fst (insideTx ! f i) \<noteq> s'"
            by simp
          hence c1: "fst (tr ! (f i + 1 + beginAtomic)) \<noteq> s'"
            apply (auto simp add: a8 nth_append nth_Cons' trStart_len split: if_splits)
            using \<open>i < length insideTxOther\<close> f_map2 by auto
            
          have c2: "f i + 1 + beginAtomic > beginAtomic'"
            by (smt One_nat_def Suc_diff_Suc \<open>fst (insideTx ! f i) \<noteq> s'\<close> add.commute add.left_commute add.right_neutral 
                add_Suc_right add_diff_inverse_nat add_le_cancel_left beginAtomic'2_def beginAtomic'2_inisdeTx 
                beginAtomic'3b diff_Suc_1 diff_diff_left f_mono fst_conv l1 leD leI le_add_diff_inverse le_less 
                less_Suc_eq_0_disj not_add_less2 order.asym strict_mono_less_eq that(1))

          find_theorems i
          {
            assume "i < endAtomic'3"
            
            hence c3: "f i + 1 + beginAtomic < endAtomic'"
              by (metis endAtomic'2_def endAtomic'3b f_mono less_diff_conv strict_mono_def)
              
            with c1 c2 
            have False
              using b6 less_or_eq_imp_le by blast 
          }
          moreover
          {
            assume "i = endAtomic'3"
            hence c3: "f i + 1 + beginAtomic = endAtomic'"
              using \<open>insideTxOther ! i = insideTx ! f i\<close> a endAtomic'3b by auto
            with c1 c2   
            have False
              by (simp add: b5)
          }
          ultimately show False
            using le_eq_less_or_eq that(2) by blast   
        qed  
          
          
        
        show "\<forall>i. beginAtomic'3 + beginAtomic \<le> i \<and> i \<le> endAtomic'3 + beginAtomic \<longrightarrow> fst (tr' ! i) = s'"
          apply (auto simp add: tr'_def )
          apply (subst nth_append_second)
          apply (simp add: trStart_len)
          apply (subst nth_append_first)
          apply (simp add: trStart_len)
          using endAtomic'3a apply auto[1]
          apply (simp add: trStart_len)
          by (simp add: h2)
          
      qed
    }
    moreover
    {
      assume l1: "beginAtomic' = endAtomic "
      hence False
        using a5 b4 by auto
      hence "transactionIsPacked tr' t"
        by simp
    }
    moreover
    {
      assume l1: "beginAtomic' > endAtomic "
      hence l2: "endAtomic' > endAtomic"
        using b2 dual_order.strict_trans by blast
      
      
      have "transactionIsPacked tr' t"
      proof (rule transactionIsPacked_show)
        show "initialState program ~~ tr' \<leadsto>* S'" using tr'2 .
        show "beginAtomic' < endAtomic'" using b2 .
        show "tr' ! beginAtomic' = (s', ABeginAtomic t)"
          by (simp add: tr'_same_end l1 b4)
        show "endAtomic' < length tr'"
          using a8 b3 insideTx_len tr'_def by auto
        show "tr' ! endAtomic' = (s', AEndAtomic) "
          by (simp add: tr'_same_end l2 b5)
        show "\<forall>i. beginAtomic' \<le> i \<and> i \<le> endAtomic' \<longrightarrow> fst (tr' ! i) = s'"
          using b6 l1 tr'_same_end by auto
      qed    
    }
    ultimately show "transactionIsPacked tr' t"
      by linarith
  qed
    
  
  then show ?thesis
    using tr'1 tr'2 tr'3 transactionIsClosed' noFail' by blast
qed

find_theorems List.map_filter

lemma notPacked_finite:
  "finite {tx. \<not> transactionIsPacked tr tx}"
proof (rule finite_subset)
  show "{tx. \<not> transactionIsPacked tr tx} \<subseteq> {tx | c tx. (c, ABeginAtomic tx) \<in> set tr}"
    using notPackedExists by auto
    
  define P :: "(session\<times>action) \<Rightarrow> txid option" where "P = (\<lambda>x. case x of (c, ABeginAtomic tx) \<Rightarrow> Some tx | _ \<Rightarrow> None)"
  
  have P1: "P (c, ABeginAtomic tx) = Some tx" for c tx by (auto simp add: P_def)
  have P2: "P a = None" if "\<forall>c tx. a \<noteq> (c, ABeginAtomic tx)" for a 
    using that by (auto simp add: P_def split: prod.splits action.splits)
  
  
  have alt: 
     "{tx | c tx. (c, ABeginAtomic tx) \<in> set tr}
    = set (List.map_filter P tr)"
  proof (induct tr)
    case Nil
    then show ?case by (auto simp add: map_filter_simps)
  next
    case (Cons a tr)
    thm Cons.hyps
    
    have "set (List.map_filter P (a # tr)) 
        = set (List.map_filter P tr) \<union> (case P a of None \<Rightarrow> {} | Some tx \<Rightarrow> {tx})"
        by (auto simp add: map_filter_simps split: option.splits)
    moreover have "... = {tx | c tx. (c, ABeginAtomic tx) \<in> set tr} \<union> (case P a of None \<Rightarrow> {} | Some tx \<Rightarrow> {tx})"
      by (subst Cons.hyps, simp)
    moreover have "... = {tx | c tx. (c, ABeginAtomic tx) \<in> set (a#tr)}"
      apply auto
      apply (metis P1 P2 equals0D option.case_eq_if option.collapse option.inject singletonD)
      by (simp add: P1)
      
      
    ultimately show ?case by force
  qed
  thus "finite {tx | c tx. (c, ABeginAtomic tx) \<in> set tr}" by force
qed    


lemma canPackAllClosedTransactions:
assumes steps: "initialState program ~~ tr \<leadsto>* S'"
  and transactionIsClosed: "\<And>tx. transactionIsClosed tr tx"
  and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "\<exists>tr'. (\<forall>tx. transactionIsPacked tr' tx)
        \<and> (initialState program ~~ tr' \<leadsto>* S')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (traceCorrect tr' \<longleftrightarrow> traceCorrect tr)"
using assms proof (induct "card {tx. \<not>transactionIsPacked tr tx}" arbitrary: tr rule: nat_less_induct)

  case 1
    fix tr
  assume a0: "\<forall>m<card {tx. \<not> transactionIsPacked tr tx}.
              \<forall>x. m = card {tx. \<not> transactionIsPacked x tx} \<longrightarrow>
                  (initialState program ~~ x \<leadsto>* S') \<longrightarrow>
                  All (transactionIsClosed x) \<longrightarrow> (\<forall>xa. (xa, AFail) \<notin> set x) \<longrightarrow> (\<exists>tr'. All (transactionIsPacked tr') \<and> (initialState program ~~ tr' \<leadsto>* S') \<and> (\<forall>s. (s, AFail) \<notin> set tr') \<and> (traceCorrect tr' = traceCorrect x))"
     and a1: "initialState program ~~ tr \<leadsto>* S'"
     and a2: "\<And>x. transactionIsClosed tr x"
     and a3: "\<And>s. (s, AFail) \<notin> set tr"

  show "\<exists>tr'. All (transactionIsPacked tr') \<and> (initialState program ~~ tr' \<leadsto>* S') \<and>  (\<forall>s. (s, AFail) \<notin> set tr') \<and> traceCorrect tr' = traceCorrect tr"
  proof (cases "card {tx. \<not>transactionIsPacked tr tx}")
    case 0
    hence "\<forall>tx. transactionIsPacked tr tx"
      using notPacked_finite by auto
      
    then show ?thesis
      using a1 a3 by blast 
    
  next
    case (Suc n)
    from this obtain tx where tx_notPacked: "\<not> transactionIsPacked tr tx"
      by fastforce 
    
      
    from canPackOneTransaction2[OF a1 a2 a3]
    obtain tr'
      where tr1: "transactionIsPacked tr' tx"
        and tr2: "(initialState program ~~ tr' \<leadsto>* S')"
        and tr3: "(\<forall>t. transactionIsPacked tr t \<longrightarrow> transactionIsPacked tr' t) "
        and tr4: "traceCorrect tr' = traceCorrect tr"
        and tr5: "\<forall>tx. transactionIsClosed tr' tx"
        and tr6: "\<forall>s. (s, AFail) \<notin> set tr'"
      by blast
      
    have "{tx. \<not>transactionIsPacked tr' tx} \<subset> {tx. \<not>transactionIsPacked tr tx}"
      using tr3 tr1 tx_notPacked by auto
    hence cardReduced: "card {tx. \<not>transactionIsPacked tr' tx} < card {tx. \<not>transactionIsPacked tr tx}"
      by (simp add: notPacked_finite psubset_card_mono)
      
    thm a0[rule_format]  
    have "\<exists>tr''. All (transactionIsPacked tr'') \<and> (initialState program ~~ tr'' \<leadsto>* S') \<and> (\<forall>s. (s, AFail) \<notin> set tr'') \<and> traceCorrect tr'' = traceCorrect tr'"
    proof (rule a0[rule_format]) 
      show "card {tx. \<not>transactionIsPacked tr' tx} < card {tx. \<not>transactionIsPacked tr tx}" using cardReduced .
      show "card {tx. \<not> transactionIsPacked tr' tx} = card {tx. \<not> transactionIsPacked tr' tx}" ..
      show "initialState program ~~ tr' \<leadsto>* S'" using tr2 .
      show "\<And>x. transactionIsClosed tr' x" using tr5 by simp
      show "\<And>s. (s, AFail) \<notin> set tr'" using tr6 by simp
  qed
  thus ?thesis
    using tr4 by blast
  qed
qed

lemma card_zero:
assumes "finite S"
and "0 = card S"
shows "S = {}"
using assms(1) assms(2) by auto

lemma card_suc_nonempty: "Suc x = card S \<Longrightarrow> \<exists>x. x\<in>S"
  by (metis card_eq_SucD insertI1)

  
lemma card_remove_one:
fixes X::"'a set"
fixes Y::"'b set"
assumes fin: "finite X"
    and "f ` (Y - {missing}) = X"
    and "(g ` X) \<union> {missing} = Y"
    and "\<And>a. a\<in>Y - {missing} \<Longrightarrow> g (f a) = a"
    and "\<And>a. a\<in>X \<Longrightarrow> f (g a) = a"
shows "card Y = Suc (card X)"
using assms proof (induct X arbitrary: Y  rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert x F)
  hence fin: "finite F"
   and xNotInF: "x \<notin> F"
   and IH: "\<And>Y. \<lbrakk>f ` (Y - {missing}) = F; g ` F \<union> {missing} = Y; \<And>a. a \<in> Y - {missing} \<Longrightarrow> g (f a) = a; \<And>a. a \<in> F \<Longrightarrow> f (g a) = a\<rbrakk> \<Longrightarrow> card Y = Suc (card F)"
   and YtoX: "f ` (Y - {missing}) = insert x F"
   and XtoY: "g ` insert x F \<union> {missing} = Y"
   and invY: "\<And>a. a \<in> Y - {missing} \<Longrightarrow> g (f a) = a"
   and invX: "\<And>a. a \<in> insert x F \<Longrightarrow> f (g a) = a"
   by auto
  
  have "g x \<noteq> missing"
    by (smt Diff_insert_absorb Un_insert_right XtoY YtoX image_iff insertI1 invY mk_disjoint_insert)
  
  have "missing \<in> Y"
    using XtoY by blast
    
    
  define Y' where "Y' \<equiv> Y - {g x}"
    
  from YtoX `g x \<noteq> missing`
  have "f ` (Y' - {missing}) = F"
    apply (auto simp add: Y'_def)
    using image_iff insert.prems(2) invX apply auto[1]
    by (metis (no_types, lifting) Diff_insert Diff_insert2 Diff_insert_absorb image_diff_subset image_empty image_insert insertI1 invX subsetCE xNotInF)
    
    
  moreover have "g ` F \<union> {missing} = Y'" 
    using XtoY  apply (auto simp add: Y'_def `g x \<noteq> missing`[symmetric] `missing \<in> Y`)
    by (metis insert_iff invX xNotInF)
  
  moreover have  "\<And>a. a \<in> Y' - {missing} \<Longrightarrow> g (f a) = a"
    using invY Y'_def by blast

  moreover have "\<And>a. a \<in> F \<Longrightarrow> f (g a) = a"
    by (simp add: invX)
  
  ultimately have "card Y' = Suc (card F)" by (rule IH)
    
  then have "card Y = Suc (card Y')"
    apply (auto simp add: Y'_def)
    using fin insert.prems(2) by force
  moreover have "... = Suc (Suc (card F))"
    using \<open>card Y' = Suc (card F)\<close> by blast
  moreover have "... =  Suc (card (insert x F))"
    by (simp add: fin xNotInF)
  ultimately show ?case
    by linarith 
qed

definition "skip x i \<equiv> if i < x then i else i - 1"    
definition "skip_rev x i \<equiv> if i < x then i else i + 1"
  
definition removeAt :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"removeAt i l = take i l @ drop (Suc i) l"



lemma removeAt_nth: 
assumes "j < length l - 1"
shows "(removeAt i l) ! j = (if j<i then l!j else l!Suc j)"
using assms by (auto simp add: removeAt_def nth_append min_def)


(* examples *)
lemma "removeAt 0 [1,2,3] = [2,3::int]" by eval
lemma "removeAt 1 [1,2,3] = [1,3::int]" by eval

lemma show_card_smaller:
assumes "A \<subseteq> B"
    and "finite B"
    and "x\<in>B"
    and "x\<notin>A"
shows "card A < card B"
using assms 
  by (metis le_imp_less_or_eq psubset_card_mono) 

lemma show_sets_unequal:
assumes "x\<in>B" and "x\<notin>A"
shows "A \<noteq> B"
using assms
  by blast 
  
lemma Greatest_stuff:
fixes a::nat
assumes greatestIsY: "(GREATEST x. P x) = y"  
  and someP: "P a" 
  and bound: "\<And>x. P x \<Longrightarrow> x < bound"
shows "P y \<and> (\<forall>y'. P y' \<longrightarrow> y' \<le> y)"
using assms
  by (metis GreatestI Greatest_le) 
    
lemma Greatest_smaller:
fixes a::nat
assumes allSmaller: "\<And>i. P i \<Longrightarrow> i < n"
  and someP: "P a" 
shows "(GREATEST i. P i) < n"
  using GreatestI assms by auto
  
  
(*
IDEA prove general greatest induct on list

if I can always remove the last offender of a property P in a list while maintaining property Q,
then there is a list with property Q \<and> P if there is a list with Q
*)
lemma removeLastOffender_induct:
assumes listWithP: "P l"
   and canAlwaysRemoveLastQ: "\<And>l i. \<lbrakk>Q l i;  i<length l; \<And>j. \<lbrakk>j>i; j<length l\<rbrakk> \<Longrightarrow> \<not>Q l j; P l \<rbrakk> \<Longrightarrow> P (removeAt i l) \<and> (\<forall>j. j\<ge>i \<and> j < length l - 1 \<longrightarrow> \<not>Q (removeAt i l) j)"
   (*and P_prefix: "\<And>l n. P l \<Longrightarrow> P (take n l)"  this makes no sense, could just choose l = []*)
shows "\<exists>l. P l \<and> (\<forall>i<length l. \<not>Q l i)"
using listWithP proof (induct "GREATEST i. i\<le>length l \<and> (i=0 \<or> Q l (i-1))" arbitrary: l rule: less_induct)
  case less
  hence IH: "\<And>l'. \<lbrakk>(GREATEST i. i \<le> length l' \<and> (i = 0 \<or> Q l' (i-1))) < (GREATEST i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1))); P l'\<rbrakk> \<Longrightarrow> \<exists>l. P l \<and> (\<forall>i<length l. \<not> Q l i)" by simp
  
  {
    assume a1: "(GREATEST i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1))) = 0"
    have f1: "(0 \<le> length l \<and> (0 = 0 \<or> Q l (0 - 1))) \<and> (\<forall>y'. y' \<le> length l \<and> (y' = 0 \<or> Q l (y' - 1)) \<longrightarrow> y' \<le> 0)"
      using Greatest_stuff[where P="\<lambda>i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1))" and y=0 and a=0 and bound="Suc (length l)"]
      using a1 le_imp_less_Suc by blast
      
    hence "\<not>Q l i" if "i < length l" for i
      using that
      by (metis Suc_leI Suc_le_lessD diff_Suc_1 not_less0) 
    hence "P l \<and> (\<forall>i<length l. \<not>Q l i)"
      using less.prems by blast
    hence "\<exists>l. P l \<and> (\<forall>i<length l. \<not>Q l i)" ..
  }
  moreover
  {
    assume "(GREATEST i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1))) \<noteq> 0"
    hence "\<exists>i. i < length l \<and> Q l i"
      by (smt Greatest_stuff diff_diff_cancel diff_is_0_eq' diff_zero le_trans less_one linorder_neqE_nat nat_le_linear zero_less_diff)
    from this obtain i
      where i1: "i < length l"
        and i2: "Q l i"
        and i_greatest: "\<forall>j. j<length l \<and> Q l j \<longrightarrow> j \<le> i"
      apply (atomize_elim)
      apply (rule_tac x="GREATEST i. i<length l \<and> Q l i" in exI)
      apply (auto)
      apply (metis (no_types, lifting) GreatestI)
      apply (metis (no_types, lifting) GreatestI)
      by (metis (no_types, lifting) Greatest_le)
    
    have greatest_i: "(GREATEST i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1))) = Suc i"
    proof (rule Greatest_equality)
      show g1: "Suc i \<le> length l \<and> (Suc i = 0 \<or> Q l (Suc i - 1))"
        using i1 i2  by auto
      show "\<And>ia. ia \<le> length l \<and> (ia = 0 \<or> Q l (ia - 1)) \<Longrightarrow> ia \<le> Suc i"
        using i_greatest apply auto
        by (metis One_nat_def g1 diff_Suc_1 inc_induct le_SucE not_less_eq_eq) 
    qed
      
    have l_removed: "P (removeAt i l) \<and> (\<forall>j. j\<ge>i \<and> j < length l - 1 \<longrightarrow> \<not>Q (removeAt i l) j)"
    using i2 i1 proof (rule canAlwaysRemoveLastQ)
      show "\<And>j. \<lbrakk>i < j; j < length l\<rbrakk> \<Longrightarrow> \<not> Q l j"
        using i_greatest leD by blast
      show "P l"
        by (simp add: less.prems)
    qed    
    
    have "\<exists>l. P l \<and> (\<forall>i<length l. \<not>Q l i)"
    proof (rule IH)
      show "P (removeAt i l)" using l_removed by simp
      
      from i1 l_removed
      have "i' < i" if "i' < length (removeAt i l)" and "Q (removeAt i l) i'" for i'
        using that
        by (metis (no_types, lifting) Suc_eq_plus1 Suc_mono add_Suc_right id_take_nth_drop leI length_Cons length_append less_diff_conv removeAt_def) 
      
      hence h1: "i' < Suc i" if "i' \<le> length (removeAt i l)" and "(i' = 0 \<or> Q (removeAt i l) (i' - 1))" for i'
        using that
        by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred dual_order.strict_iff_order le0 le_imp_less_Suc) 
      
      hence "(GREATEST i'. i' \<le> length (removeAt i l) \<and> (i' = 0 \<or> Q (removeAt i l) (i' - 1))) < Suc i"
        by (rule Greatest_smaller; blast)
  
        
      thus "(GREATEST i'. i' \<le> length (removeAt i l) \<and> (i' = 0 \<or> Q (removeAt i l) (i' - 1))) < (GREATEST i. i \<le> length l \<and> (i = 0 \<or> Q l (i-1)))"
        unfolding greatest_i .
    qed
  }
  ultimately show ?case by blast
qed  
  
lemma removeLastQ_induct:
assumes listWithP: "P l"
   and canAlwaysRemoveLastQ: "\<And>l i. \<lbrakk>\<not>Q l i; i<length l; \<And>j. \<lbrakk>j>i; j<length l\<rbrakk> \<Longrightarrow> Q l j  \<rbrakk> \<Longrightarrow> P (removeAt i l) \<and> (\<forall>j. j\<ge>i \<and> j < length l - 1 \<longrightarrow> Q (removeAt i l) j)"
   (*and P_prefix: "\<And>l n. P l \<Longrightarrow> P (take n l)"  this makes no sense, could just choose l = []*)
shows "\<exists>l. P l \<and> (\<forall>i<length l. Q l i)"
proof -
  have "\<exists>l. P l \<and> (\<forall>i<length l. \<not>\<not>Q l i)"
    using listWithP apply (rule removeLastOffender_induct)
    using canAlwaysRemoveLastQ by blast
  thus ?thesis by simp
qed  
  


lemma existsGreates_pair:
fixes i :: nat
fixes j:: nat
assumes example: "P i j"
    and bound: "\<And>i j. P i j \<Longrightarrow> j < upper_bound"
shows "\<exists>i j. P i j \<and> (\<forall>i' j'. P i' j' \<longrightarrow> j' \<le> j)"
proof -
  define maxJ where "maxJ \<equiv> GREATEST j. \<exists>i. P i j"
  
  have "\<exists>i. P i maxJ"
  unfolding maxJ_def proof (rule GreatestI)
    show "\<exists>i. P i j" using example by blast
    show "\<forall>j. (\<exists>i. P i j) \<longrightarrow> j < upper_bound" using bound by blast
  qed
  
  from this
  obtain maxI where p1: "P maxI maxJ"
    by blast
    
  have p2: "j' \<le> maxJ" if "P i' j'" for i' j'
  unfolding maxJ_def proof (rule Greatest_le)
    show "\<exists>i. P i j'" using that by blast
    show "\<forall>y. (\<exists>i. P i y) \<longrightarrow> y < upper_bound" using bound by blast
  qed
  from p1 p2 show ?thesis by blast
qed  
    

lemma removeAt_nth2: "\<lbrakk>i \<le> j; j < length tr - Suc 0\<rbrakk> \<Longrightarrow> removeAt i tr ! j = tr ! Suc j"
  by (simp add: removeAt_nth)

  
lemma in_set_removeAtD:
"x \<in> set (removeAt i xs) \<Longrightarrow> x \<in> set xs"
apply (auto simp add: removeAt_def )
apply (meson in_set_takeD)
apply (meson in_set_dropD)
done  

lemma in_set_removeAt:
"\<lbrakk>x \<in> set xs; xs!i \<noteq> x \<rbrakk> \<Longrightarrow> x \<in> set (removeAt i xs)"
apply (induct xs rule: rev_induct)
by (auto simp add: removeAt_def nth_append nth_Cons' take_Cons' split: if_splits)
  

lemma inTransaction_currentTx:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
   and intx: "inTransaction tr (length tr - 1) s"
   and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "currentTransaction S s \<noteq> None"
using assms proof (induct rule: steps_induct)
  case initial
  then show ?case
    by auto 
next
  case (step S' tr a S'')
  
  have noFail': "\<And>s. (s, AFail) \<notin> set tr"
    using step.prems(2) by auto 
  have noFail''[simp]: "a \<noteq> (s, AFail)" for s
    using step.prems(2) by auto
    
    
  { 
    assume "inTransaction tr (length tr - 1) s"
    hence "currentTransaction S' s \<noteq> None"
      using step.IH noFail' by blast
    from this obtain tx where ctx: "currentTransaction S' s = Some tx"
      by blast
      
    from `S' ~~ a \<leadsto> S''`
    have ?case 
      apply (rule step.cases)
      apply (auto simp add: ctx)
      using `inTransaction (tr @ [a]) (length (tr @ [a]) - 1) s`  inTransaction_def le_eq_less_or_eq by auto[1]
  }
  moreover 
  {
    assume "\<not>inTransaction tr (length tr - 1) s"
       and "\<And>tx. a \<noteq> (s, ABeginAtomic tx)"
    hence "\<not>inTransaction (tr @ [a]) (length (tr @ [a]) - 1) s"
      apply (auto simp add: inTransaction_def nth_append)
      by (metis Nitpick.size_list_simp(2) One_nat_def leD length_tl not_less_eq_eq not_less_zero)
    with `inTransaction (tr @ [a]) (length (tr @ [a]) - 1) s`
    have False by simp
    hence ?case ..
  }
  moreover 
  {
    fix tx
    assume "\<not>inTransaction tr (length tr - 1) s"
       and "a = (s, ABeginAtomic tx)"
    with `S' ~~ a \<leadsto> S''`
    have ?case
      by (auto simp add: step_simps)
  }
  ultimately
  show "?case" by blast
qed


lemma no_invcheck_in_tx:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
   and tri: "tr!i = (s, a)"
   and intx: "inTransaction tr i s"
   and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "a \<noteq> AInvcheck t"
using assms proof (induct rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a' S'')
  show ?case 
  proof (cases "i < length tr")
    case True
    then show ?thesis 
      using step apply (auto simp add: step_simps)
      by (metis mem_Collect_eq nth_append sessionsInTransaction_append sessionsInTransaction_def)
  next
    case False
    with `inTransaction (tr @ [a']) i s`
    have i_def[simp]: "i = length tr"
      by (auto simp add: inTransaction_def)
    hence a'_def[simp]: "a' = (s, a)"
      using `(tr @ [a']) ! i = (s, a)` by auto
      
    show "a \<noteq> AInvcheck t"
    proof (rule ccontr)
      assume "\<not> a \<noteq> AInvcheck t"
      hence a_def[simp]: "a =  AInvcheck t"
        by simp
      
      from `inTransaction (tr @ [a']) i s`
      have "inTransaction tr (length tr - 1) s"
        apply (auto simp add: inTransaction_def nth_append split: if_splits)
        by (smt Nitpick.size_list_simp(2) One_nat_def inc_induct length_tl less_Suc_eq less_le not_less_zero)
        
        
        
      (*from `inTransaction (tr @ [a]) i s`*)
      from step.steps `inTransaction tr (length tr - 1) s` 
      have "currentTransaction S' s \<noteq> None"
      proof (rule inTransaction_currentTx)  
        show "\<And>s. (s, AFail) \<notin> set tr"
          using step.prems(3) by auto 
      qed  
      
      with `S' ~~ a' \<leadsto> S''`
      show False
        by (auto simp add: step_simps)
    qed
  qed
qed  

lemma no_invcheck_in_tx2:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
   and intx: "inTransaction tr i s"
   and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "tr!i \<noteq> (s, AInvcheck t)"
  using intx noFail no_invcheck_in_tx steps by blast
  

lemma actionInOpenTransaction_to_inTransaction:
assumes "actionInOpenTransaction tx tr i" 
    and "i < length tr"
    and "s = fst (tr!i)"
shows "inTransaction tr i s"
using assms apply (auto simp add: actionInOpenTransaction_def inTransaction_def)
apply (case_tac "tr ! i")
apply (drule_tac x=a in spec)
apply auto
done

  
thm removeLastOffender_induct[where 
         P="\<lambda>t. traceCorrect t \<longleftrightarrow> traceCorrect tr"
     and Q="\<lambda>t i. (\<forall>tx. actionInOpenTransaction tx t i)"]

lemma exists_outside_imp:     
"\<exists>x. A \<longrightarrow> B x \<Longrightarrow> A \<longrightarrow> (\<exists>x. B x)"
  by simp             

     
lemma canCloseTransactions_h:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "\<exists>tr'. 
        ((traceCorrect tr' \<longleftrightarrow> traceCorrect tr) 
        \<and> (\<exists>S'. initialState program ~~ tr' \<leadsto>* S')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr'))
        \<and> (\<forall>i<length tr'. \<not> (\<exists>tx. actionInOpenTransaction tx tr' i))"
proof (rule removeLastOffender_induct; (intro conjI)?; (elim conjE)?)
  show "traceCorrect tr = traceCorrect tr" ..
  show "\<exists>S'. initialState program ~~ tr \<leadsto>* S'" using steps ..
  show "\<forall>s. (s, AFail) \<notin> set tr" using noFail by simp
  
  fix tr'::trace 
  fix i::nat
  
  assume a1: "\<exists>tx. actionInOpenTransaction tx tr' i"
     and a2: "i < length tr'"
     and a3: "\<And>j. \<lbrakk>i < j; j < length tr'\<rbrakk> \<Longrightarrow> \<not> (\<exists>tx. actionInOpenTransaction tx tr' j)"
     and a4: "traceCorrect tr' = traceCorrect tr"
     and a5: "(\<exists>S'. initialState program ~~ tr' \<leadsto>* S')"
     and a6: "(\<forall>s. (s, AFail) \<notin> set tr')"
     
  from a1 obtain tx where a1': "actionInOpenTransaction tx tr' i" ..
  
  from a5 obtain S' where a5': "initialState program ~~ tr' \<leadsto>* S'" ..
  
  show g1: "\<exists>S'. initialState program ~~ removeAt i tr' \<leadsto>* S'"
    text {*
      Since i is the last action in an open transaction, it cannot affect the execution of others
    *}
    sorry

  have no_invcheck_i: "tr'!i \<noteq> (s, AInvcheck False)" if "s = fst (tr' ! i)"  for s
  proof (rule no_invcheck_in_tx2)
    from a1
    obtain tx' where "actionInOpenTransaction tx' tr' i" by auto
    thus "inTransaction tr' i s"
    proof (rule actionInOpenTransaction_to_inTransaction)
      show "i < length tr'" using a2.
      show "s = fst (tr' ! i)" using `s = fst (tr' ! i)`.
    qed
    show "\<And>s. (s, AFail) \<notin> set tr'"
      using a6 by blast
    
    show "initialState program ~~ tr' \<leadsto>* S'"
      using a5'.
  qed      
    
  show "\<forall>s. (s, AFail) \<notin> set (removeAt i tr')"
    using a6 by (auto simp add: removeAt_def dest: in_set_takeD in_set_dropD)
    
    
  show "traceCorrect (removeAt i tr') \<longleftrightarrow> traceCorrect tr" 
    text {*
     1. Since i is in a transaction it cannot be an invariant check.
    *}
    apply (auto simp add: traceCorrect_def)
    apply (metis a4 fst_conv in_set_removeAt no_invcheck_i traceCorrect_def)
    by (meson a4 in_set_removeAtD traceCorrect_def) 
    
    
    
    
    
  from a3 have a3': "\<And>j tx s a k. \<lbrakk>i < j; j < length tr'; tr' ! j = (s, a); tr' ! k = (s, ABeginAtomic tx); k \<le> j\<rbrakk> \<Longrightarrow> (\<exists>j>k. j < length tr' \<and> tr' ! j = (s, AEndAtomic))"
    apply (auto simp add: actionInOpenTransaction_def)
    by fastforce
  
    
  show "(\<forall>j. i \<le> j \<and> j < length tr' - 1 \<longrightarrow> \<not> (\<exists>tx. actionInOpenTransaction tx (removeAt i tr') j))"
    text {*
      have to consider a lot of different cases, most are by solved by a3'
    *}
    sorry

qed  
(*
  if there are unclosed transactions, we can just ignore them without affecting the correctness of the code
*)
lemma canCloseTransactions:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "\<exists>tr' S'. (\<forall>tx. transactionIsClosed tr' tx)
        \<and> (initialState program ~~ tr' \<leadsto>* S') 
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (traceCorrect tr' \<longleftrightarrow> traceCorrect tr)"
unfolding transactionIsClosed_def2
using canCloseTransactions_h[OF steps noFail] 
  by auto 

lemma transactionsArePacked_def2:
shows "transactionsArePacked tr \<longleftrightarrow> (\<forall>tx. transactionIsPacked tr tx)"
apply (auto simp add: transactionsArePacked_def transactionIsPacked_def indexInOtherTransaction_def)
  by blast

  
  
find_theorems transactionIsClosed steps        
lemma canPackTransactions:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
shows "\<exists>tr' S'. transactionsArePacked tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* S')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (traceCorrect tr' \<longleftrightarrow> traceCorrect tr)"
  using canCloseTransactions canPackAllClosedTransactions steps transactionsArePacked_def2 noFail by blast
    

definition packed_trace :: "trace \<Rightarrow> bool" where
"packed_trace tr \<equiv>
  \<forall>i.
      0<i
    \<longrightarrow> i<length tr
    \<longrightarrow> fst (tr!(i-1)) \<noteq> fst (tr!i)
    \<longrightarrow> ((\<exists>txId. snd(tr!i) = ABeginAtomic txId) 
          \<or> (\<exists>p a. snd(tr!i) = AInvoc p a))" 

    
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
shows "(\<exists>tx. a' = ABeginAtomic tx) \<or> (\<exists>p ar. a' = AInvoc p ar)"
proof -
  have "a' = snd(tr!(1+length tr1))"
    using split_tr by (auto simp add: nth_append)
  
  moreover
  have "(\<exists>tx. snd(tr!(1+length tr1)) = ABeginAtomic tx) \<or> (\<exists>p ar. snd(tr!(1+length tr1)) = AInvoc p ar)"
  using packed proof (rule use_packed_trace)
    show "0 < 1 + length tr1" by simp
    show "1 + length tr1 < length tr" using split_tr by auto
    show "fst (tr ! (1 + length tr1 - 1)) \<noteq> fst (tr ! (1 + length tr1))" using split_tr `s \<noteq> s'` by (auto simp add: nth_append)
  qed
  ultimately
  show ?thesis by simp
qed  
    
lemma packedTrace_from_packedTransactions:
assumes steps: "initialState program ~~ tr \<leadsto>* S"
    and noFail: "\<And>s. (s, AFail) \<notin> set tr"
    and packedTransactions: "transactionsArePacked tr"
shows "\<exists>tr' S'. packed_trace tr' 
        \<and> (initialState program ~~ tr' \<leadsto>* S')
        \<and> (\<forall>s. (s, AFail) \<notin> set tr')
        \<and> (traceCorrect tr' \<longleftrightarrow> traceCorrect tr)"
using assms proof (induct "card {i.
        0<i 
      \<and> i<length tr 
      \<and> fst (tr!(i-1)) \<noteq> fst (tr!i)
      \<and> \<not>((\<exists>txId. snd(tr!i) = ABeginAtomic txId) 
          \<or> (\<exists>p a. snd(tr!i) = AInvoc p a))}"
      arbitrary: tr
      rule: less_induct)
  case less
  then show ?case
  proof (cases "card {i.
        0<i 
      \<and> i<length tr 
      \<and> fst (tr!(i-1)) \<noteq> fst (tr!i)
      \<and> \<not>((\<exists>txId. snd(tr!i) = ABeginAtomic txId) 
          \<or> (\<exists>p a. snd(tr!i) = AInvoc p a))}")
    case 0
      hence "{i. 0 < i \<and> i < length tr \<and> fst (tr ! (i - 1)) \<noteq> fst (tr ! i) \<and> \<not>((\<exists>txId. snd (tr ! i) = ABeginAtomic txId) \<or> (\<exists>p a. snd (tr ! i) = AInvoc p a))} = {}"
        by force
      hence "packed_trace tr"
        by (auto simp add: packed_trace_def)
      then show ?thesis
        using noFail steps
        using less.prems(1) less.prems(2) by blast  
  next
    case (Suc nat)
    
    text {*idea: get the last offender (or better the last?)
     
    then move that action to the front:
    if there is a beginAtomic or beginInvoc before, move it there, otherwise to beginning of list
    
    why can we do that?
    
    Case beginAtomic
    between the two actions, there can only be actions from the same session.
    there can be an endAtomic, but our action is no beginAtomic, so this does not really matter.
    Pulls can be problematic, because they kind of belong to the beginAtomic.
    I should change the thing with pulls, maybe just add them to beginAtomic?
    
    Ok, let's say we move things to the end.
    Then the problem might be that there is no end of the invocation...
    
    *}
    
    
    
    then show ?thesis sorry
  qed
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
    obtain s where "initialState program ~~ tr \<leadsto>* s"
      by (auto simp add: traces_def)
    
    
    text "Then there is a reshuffling of the trace, where transactions are not interleaved"
    then obtain tr' s'
      where "initialState program ~~ tr' \<leadsto>* s'" 
        and "transactionsArePacked tr'"
        and "traceCorrect tr' \<longleftrightarrow> traceCorrect tr"
        and "\<forall>s. (s, AFail) \<notin> set tr'"
      using canPackTransactions noFail by blast
    
    then obtain tr'' s''
      where "initialState program ~~ tr'' \<leadsto>* s''" 
        and "packed_trace tr''"
        and "traceCorrect tr'' \<longleftrightarrow> traceCorrect tr'"
        and "\<forall>s. (s, AFail) \<notin> set tr''"
      using  packedTrace_from_packedTransactions by blast
      
    text "According to the assumption those traces are correct"
    with packedTracesCorrect noFail
    have "traceCorrect tr'"  
      by auto
    
    with `traceCorrect tr' \<longleftrightarrow> traceCorrect tr`
    show "traceCorrect tr" ..
  qed  
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
