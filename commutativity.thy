theory commutativity
  imports repliss_sem prefix
    "~~/src/HOL/Eisbach/Eisbach"
    execution_invariants
begin

text {* Commutativity in executions *}

text {* This theory proves commutativity between certain actions in executions. *}

lemma iffI2: "\<lbrakk>A \<Longrightarrow> B; \<not>A \<Longrightarrow> \<not>B\<rbrakk> \<Longrightarrow> A \<longleftrightarrow> B"
  by auto

text {*
 The invocId info is set iff there was an invocId in the trace
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
      case (invocId C s procName args initialState impl)
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
      case (invCheck C res s')
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
 There can be no action on a invocId after a fail or return:
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
After a return or a failure no more actions on the same invocId are possible.
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
schematic_goal [simp]: "isAFail (AInvcheck c) = ?x" by (auto simp add: isAFail_def)                            

lemma exI_eq: 
  assumes "P y True"
  shows "\<exists>x. P x (x = y)"
  using assms by (metis (full_types))


lemma chooseSnapshot_unchanged:
  assumes
  a0: "chooseSnapshot snapshot vis S1"
  and a2: "happensBefore S2 = happensBefore S1 "
  and a4: "transactionStatus S2 = transactionStatus S1 "
  and a5: "callOrigin S2 = callOrigin S1 "
shows "chooseSnapshot snapshot vis S2"
  using a0 a2 a4 a5 by (auto simp add: chooseSnapshot_def)

lemma chooseSnapshot_unchanged_precise:
  assumes
  a0: "chooseSnapshot snapshot vis S1"
  and a2: "committedTransactions S1 \<subseteq> committedTransactions S2"
  and a3: "\<And>tx. transactionStatus S1 tx \<triangleq> Committed \<Longrightarrow> (\<forall>c. callOrigin S1 c \<triangleq> tx \<longleftrightarrow> callOrigin S2 c \<triangleq> tx)"
  and a4: "\<And>tx c. \<lbrakk>transactionStatus S1 tx \<triangleq> Committed; callOrigin S1 c \<triangleq> tx\<rbrakk> \<Longrightarrow> (\<forall>c'. (c',c)\<in>happensBefore S1 \<longleftrightarrow> (c',c)\<in>happensBefore S2)"
shows "chooseSnapshot snapshot vis S2"
proof -
  from a0 obtain newTxns newCalls
    where "newTxns \<subseteq> committedTransactions S1"
      and "newCalls = callsInTransaction S1 newTxns \<down> happensBefore S1"
      and "snapshot = vis \<union> newCalls"
    by (metis chooseSnapshot_def)

  show "chooseSnapshot snapshot vis S2"
    unfolding chooseSnapshot_def
  proof (intro exI conjI)
    show "snapshot = vis \<union> newCalls" using `snapshot = vis \<union> newCalls`.
    show "newTxns \<subseteq> committedTransactions S2"
      using \<open>newTxns \<subseteq> committedTransactions S1\<close> a2 by blast
    show "newCalls = callsInTransaction S2 newTxns \<down> happensBefore S2"
      using `newCalls = callsInTransaction S1 newTxns \<down> happensBefore S1`
      using \<open>newTxns \<subseteq> committedTransactions S1\<close> a3 a4  by (auto simp add: callsInTransactionH_def downwardsClosure_def, blast)
  qed
qed


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
        case (newId s ls f ls' uid ls'')
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls''), generatedIds := (generatedIds S2)(uid \<mapsto> s )\<rparr>"])
          using induct_step.coupling no_fail newId
          by (auto simp add: step_simps state_ext  induct_step)

      next
        case (beginAtomic s ls f ls' t vis snapshot)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))


        show ?thesis 
          apply (rule exI[where x="S2\<lparr>
                localState := localState S2(s \<mapsto> ls'), 
                currentTransaction := currentTransaction S2(s \<mapsto> t), 
                transactionStatus := transactionStatus S1(t \<mapsto> Uncommitted),
                transactionOrigin := transactionOrigin S2(t \<mapsto> s),
                visibleCalls := visibleCalls S2(s \<mapsto> snapshot)\<rparr>"])
          using induct_step.coupling no_fail beginAtomic
          apply (auto simp add: step_simps state_ext  induct_step)
          using `chooseSnapshot snapshot vis S1` chooseSnapshot_unchanged induct_step.coupling by blast 

      next
        case (endAtomic s ls f ls' t)
        from `initialState program ~~ tr \<leadsto>* S1` `localState S1 s \<triangleq> ls`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S1(t \<mapsto> Committed)\<rparr>"])
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
        case (invocId s procName args initialLocalState impl)
        from `initialState program ~~ tr \<leadsto>* S1` `invocationOp S1 s = None`
        have no_fail: "(s, AFail) \<notin> set tr"
          by (meson everything_starts_with_an_invocation in_set_conv_nth)

        show ?thesis 
          apply (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> initialLocalState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> (procName, args))\<rparr>"])
          using induct_step.coupling no_fail invocId
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
        case (invCheck res s)

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


definition commutativeS :: "('localState, 'any::valueType) state \<Rightarrow> invocId \<times> 'any action \<Rightarrow> invocId \<times> 'any action \<Rightarrow> bool" where
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

definition differentIds :: "(invocId \<times> 'any action) \<Rightarrow> (invocId \<times> 'any action) \<Rightarrow> bool" where
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
  "precondition (s, ANewId uid) C = (\<exists>ls f ls' ls''. localState C s \<triangleq> ls \<and> currentProc C s \<triangleq> f \<and> f ls = NewId ls' \<and> generatedIds C uid = None \<and> uniqueIds uid = {uid} \<and> ls' uid \<triangleq> ls'')"
  apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
  done

lemma precondition_beginAtomic:
  "precondition (s, ABeginAtomic tx snapshot) C = 
    (\<exists>ls f ls' vis. 
        localState C s \<triangleq> ls 
      \<and> currentProc C s \<triangleq> f 
      \<and> f ls = BeginAtomic ls' 
      \<and> currentTransaction C s = None 
      \<and> transactionStatus C tx = None
      \<and> visibleCalls C s \<triangleq> vis
      \<and> chooseSnapshot snapshot vis C)"
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
  "precondition (s, AFail) C = (\<exists>ls. localState C s \<triangleq> ls)" \<comment> \<open>  failures occur wherever something is running ;)  \<close>
  apply (auto simp add: precondition_def intro: step.intros elim!: step_elims)
  done

lemma precondition_invcheck:
  "precondition (s, AInvcheck res) C \<longleftrightarrow> (res = invariant (prog C) (invContext C))"
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

\<comment> \<open>getContext is not changed by actions in other transactions\<close>
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




\<comment> \<open>invcontext is not changed by actions in other transactions\<close>
lemma unchangedInTransaction_getInvContext:
  assumes differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and aIsInInvoc: "localState A sa \<triangleq> lsa"
    and txUncommitted[simp]: "transactionStatus A tx \<triangleq> Uncommitted" 
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and exec: "A ~~ (sa, a) \<leadsto> B"
    and visibleCalls_inv: "\<And>s vis. visibleCalls A s \<triangleq> vis \<Longrightarrow> vis \<subseteq> dom (calls A)"
    and origin_inv: "dom (callOrigin A) = dom (calls A)"
  shows
    "invContext A = invContext B"
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
  have committedSame: "committedCalls B = committedCalls A"        
    apply (auto simp add: committedCallsH_def isCommittedH_def  B_def)
    using "8" origin_inv by auto

  have committedCallsSame: "\<And>x. x \<in> committedCalls A \<Longrightarrow> calls A x = calls B x"
    apply (auto simp add: B_def)
    using "8" committedCallsH_def isCommittedH_def origin_inv
    by (smt domI domIff mem_Collect_eq) 

  have [simp]: "callId \<notin> committedCalls A"
    by (smt "8" domIff committedCallsH_def isCommittedH_def domI mem_Collect_eq origin_inv) 


  show ?thesis 
  proof (rule invariantContext_eqI)
    show "calls (invContext A) = calls (invContext B)"
      apply (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def)
      done
    show "happensBefore (invContext A) = happensBefore (invContext B)"
      apply (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def)
       apply (auto simp add: restrict_relation_def B_def)
      done

    show "callOrigin (invContext A) = callOrigin (invContext B)"
      apply (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def)
      apply (auto simp add: B_def)
      done
    show "knownIds (invContext A ) = knownIds (invContext B )"
      by (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def B_def)
    show "invocationOp (invContext A ) = invocationOp (invContext B )"
      by (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def B_def)
    show "invocationRes (invContext A ) = invocationRes (invContext B )"
      by (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def B_def)
    show "transactionOrigin (invContext A ) = transactionOrigin (invContext B )"
      by (auto simp add: invContextH_def committedSame committedCallsSame restrict_map_def B_def)
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
  "\<lbrakk>A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> generatedIds A \<subseteq>\<^sub>m generatedIds B"
  apply (erule step.cases, auto simp add: map_le_def)
  done

lemma generatedIds_mono2:
  assumes "generatedIds A x \<triangleq> i"
and "A ~~ a \<leadsto> B" 
shows"generatedIds B x \<triangleq> i"
  using generatedIds_mono[OF `A ~~ a \<leadsto> B`] assms by (auto simp add: map_le_def, force)


lemma generatedIds_mono2_rev:
  assumes  "generatedIds B x = None"
    and "A ~~ a \<leadsto> B"
  shows "generatedIds A x = None"
  using generatedIds_mono[OF `A ~~ a \<leadsto> B`] assms by (auto simp add: map_le_def, force)

lemma transactionStatus_mono:
  "\<lbrakk>transactionStatus B tx = None; A ~~ a \<leadsto> B\<rbrakk> \<Longrightarrow> transactionStatus A tx = None"
  apply (erule step.cases)
          apply (auto split: if_splits)
  done

lemma transactionStatus_mono2:
  "\<lbrakk>transactionStatus B tx \<triangleq> Committed; A ~~ a \<leadsto> B; snd a\<noteq>AEndAtomic\<rbrakk> \<Longrightarrow> transactionStatus A tx \<triangleq> Committed"
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
  shows "transactionStatus A t \<triangleq> Committed \<longleftrightarrow> transactionStatus B t \<triangleq> Committed" 
  using exec apply (rule step.cases)
  by (auto simp add: aIsNotCommit)    

lemma happensBefore_same_committed2: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and committed: "transactionStatus A tx \<triangleq> Committed " 
    and orig_y: "callOrigin A y \<triangleq> tx"
  shows "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
  using exec apply (rule step.cases)
  using wellFormed committed orig_y by auto      

lemma invContextSame_h: 
  assumes exec: "A ~~ (sa, a) \<leadsto> B"
    and wellFormed: "state_wellFormed A"
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Committed"
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
    and 1: "\<And>t. t\<in>txns \<Longrightarrow> transactionStatus B t \<triangleq> Committed"
    and aIsNotCommit: "a \<noteq> AEndAtomic"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommitted: "transactionStatus A tx \<triangleq> Uncommitted"
  shows "(invContext A) = (invContext B)"
proof (auto simp add: invContextH_def invContextSame_h[OF exec wellFormed 1 aIsNotCommit])
  have committed_same: "committedCalls B = committedCalls A"
    using exec apply (rule step.cases)
            apply (auto simp add: committedCallsH_def  isCommittedH_def aIsNotCommit wellFormed)
    apply force
    done

  have committed_subset: "committedCalls A \<subseteq> dom (calls A)"
    apply (auto simp add: committedCallsH_def isCommittedH_def aIsNotCommit wellFormed)
    using wellFormed wellFormed_callOrigin_dom by fastforce



  show "calls A |` committedCalls A = calls B |` committedCalls B"
    using exec apply (rule step.cases)
            apply (auto simp add: committedCallsH_def isCommittedH_def aIsInTransaction aIsNotCommit )
     apply (metis option.inject transactionStatus.distinct(1) txIsUncommitted)
    by (metis (no_types, lifting) option.distinct(1) wellFormed wellFormed_callOrigin_dom2)

  show "\<And>a b. (a, b) \<in> happensBefore A |r committedCalls A \<Longrightarrow> (a, b) \<in> happensBefore B |r committedCalls B"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
    by (auto simp add: restrict_relation_def )


  show "\<And>a b. (a, b) \<in> happensBefore B |r committedCalls B \<Longrightarrow> (a, b) \<in> happensBefore A |r committedCalls A"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
    by (auto simp add: restrict_relation_def committedCallsH_def isCommittedH_def wellFormed)

  show "callOrigin A |` committedCalls A = callOrigin B |` committedCalls B"
    apply (simp add: committed_same)
    using exec apply (rule step.cases)
            apply (auto simp add:  committedCallsH_def isCommittedH_def)
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


  show "transactionOrigin A |` committedTransactions A = transactionOrigin B |` committedTransactions B"
    using exec apply (rule step.cases)
            apply (auto simp add: restrict_map_def aIsInTransaction)
    using aIsNotCommit exec committed_same by auto[1]



qed    

lemma commutativePreservesPrecondition:
  assumes preconditionHolds: "precondition (sb,b) B"
    and differentSessions[simp]: "sa \<noteq> sb"
    and aIsInTransaction: "currentTransaction A sa \<triangleq> tx"
    and txIsUncommitted: "transactionStatus A tx \<triangleq> Uncommitted"
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
  have committed_same: "transactionStatus A t \<triangleq> Committed \<longleftrightarrow> transactionStatus B t \<triangleq> Committed" for t
    using aIsNotCommit committed_same by blast

  from exec
  have callOrigin_same_committed: "callOrigin A c \<triangleq> tx \<longleftrightarrow> callOrigin B c \<triangleq> tx" if "transactionStatus A tx \<triangleq> Committed " for c tx
    using callOrigin_same_committed that wellFormed by blast    

  from exec
  have happensBefore_same_committed2: "(x,y) \<in> happensBefore A  \<longleftrightarrow> (x,y) \<in> happensBefore B" 
    if "transactionStatus A tx \<triangleq> Committed " 
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
    obtain ls f ls' ls''
      where 1: "localState B sb \<triangleq> ls" 
        and 2: "currentProc B sb \<triangleq> f" 
        and 3: "generatedIds B x2 = None" 
        and 4: "f ls = NewId ls'"
        and 6: "uniqueIds x2 = {x2}"
        and 7: "ls' x2 \<triangleq> ls''"
      by (auto simp add: precondition_newid)
    have 5: "generatedIds A x2 = None"
      using generatedIds_mono2_rev[OF 3 exec] by blast
    thus ?thesis
      by (metis "1" "2" 4 6 7 ANewId differentSessions exec precondition_newid unchangedInTransaction(1) unchangedInTransaction(2)) 
  next
    case (ABeginAtomic tx snapshot)
    with preconditionHolds obtain ls f ls' vis
      where 1: "localState B sb \<triangleq> ls"
        and 2: "currentProc B sb \<triangleq> f"
        and 3: "f ls = BeginAtomic ls'"
        and 4: "currentTransaction B sb = None"
        and 5: "transactionStatus B tx = None"
        and 6: "chooseSnapshot snapshot vis B"
        and 7: "visibleCalls B sb \<triangleq> vis"
      by (auto simp add: precondition_beginAtomic)
    have tx_none: "transactionStatus A tx = None" using transactionStatus_mono 5 exec by blast 
    show ?thesis 
      using exec differentSessions differentSessions[symmetric] 1 2 3 4 5 6 7 tx_none txIsUncommitted wellFormed 
      by (auto simp add: aIsInTransaction aIsNotCommit step.simps `b = ABeginAtomic tx snapshot` precondition_beginAtomic elim!: chooseSnapshot_unchanged_precise split: if_splits)
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
    case (AInvcheck res)
    with preconditionHolds 
    have 2: "res = invariant (prog B) (invContext B)"
      by (auto simp add: precondition_invcheck)

    have invContextSame: "(invContext A) = (invContext B)"
      using aIsInTransaction aIsNotCommit exec invContextSnapshot_same txIsUncommitted wellFormed by blast

    have "precondition (sb, AInvcheck res) A"  
      using prog_inv[OF exec] by (auto simp add: precondition_invcheck  committed_same 2 invContextSame)

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
  assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommitted"
  shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir 
    = invContextH co to ts hbOld cs ki io ir "
  apply (simp add: invContextH_def)
  using assms apply (auto simp add: restrict_relation_def committedCallsH_def isCommittedH_def)
  done  

lemma invContext_unchanged_happensBefore2[simp]:
  assumes "co c = None"
  shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir  
    = invContextH co to ts hbOld cs ki io ir  "
  apply (simp add: invContextH_def)
  using assms apply (auto simp add: restrict_relation_def committedCallsH_def isCommittedH_def)
  done  

lemma committedCalls_uncommittedNotIn:
  assumes "callOrigin S c \<triangleq> t"
    and "transactionStatus S t \<triangleq> Uncommitted"
  shows  "c \<notin> committedCalls S"
  using assms by (auto simp add: committedCallsH_def isCommittedH_def)


find_consts "'a \<Rightarrow> 'a option \<Rightarrow> 'a"



lemma wellFormed_committedCallsExist:
  assumes a1: "calls S c = None"
    and a2: "state_wellFormed S"
  shows "c \<notin> committedCalls S"
  using a1 a2
  by (smt committedCallsH_def isCommittedH_def domIff mem_Collect_eq option.simps(3) wellFormed_callOrigin_dom) 

lemma noOrigin_notCommitted:
  "callOrigin S c = None \<Longrightarrow> c \<notin> committedCalls S"  
  by (auto simp add: committedCallsH_def isCommittedH_def)




lemma commutative_ALocal_other[simp]:
  assumes a1: "sa \<noteq> sb"
  shows "commutativeS S (sa, ALocal) (sb, a)"
  apply (case_tac a)
  by (auto simp add: commutativeS_def steps_appendFront a1 a1[symmetric]  step_simps fun_upd_twist elim!: chooseSnapshot_unchanged_precise)


lemma commutative_other_ALocal[simp]:
  assumes a1: "sa \<noteq> sb"
  shows "commutativeS S (sa, a) (sb, ALocal)"
  using assms commutativeS_switchArgs by force

lemma committedCallsH_notin[simp]:
  assumes "co c = None"
  shows "c \<notin> committedCallsH co ts"
  by (simp add: assms committedCallsH_def isCommittedH_def)

lemma committedCallsH_in:
  shows "(c \<in> committedCallsH co ts) \<longleftrightarrow> (case co c of None \<Rightarrow> False | Some t \<Rightarrow> ts t \<triangleq> Committed) "
  by (auto simp add: committedCallsH_def isCommittedH_def split: option.splits)

lemma invContextH_update_callOrigin:
  assumes "co c = None" and "ts t \<triangleq> Uncommitted"
  shows "invContextH (co(c \<mapsto> t)) to ts hb cs ki io ir   =
       invContextH co to ts hb cs ki io ir  "
  using assms by (auto simp add: invContextH_def)

lemma invContextH_update_calls:
  assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommitted"
  shows "invContextH co to ts hb (cs(c \<mapsto> newCall)) ki io ir   =
       invContextH co to ts hb cs ki io ir  "
  using assms by (auto simp add: invContextH_def committedCallsH_in)



lemma committedCallsH_update_uncommitted[simp]:
  assumes "ts t = None"
  shows "committedCallsH co (ts(t \<mapsto> Uncommitted))
     = committedCallsH co ts"
  using assms apply (auto simp add: committedCallsH_def isCommittedH_def)
  by force


lemma invContextH_update_txstatus:
  assumes "ts t = None" 
  shows "invContextH co to (ts(t\<mapsto>Uncommitted)) hb cs ki io ir  =
       invContextH co to ts hb cs ki io ir "
  using assms by (auto simp add: invContextH_def restrict_map_def)

lemmas invContextH_simps = invContextH_update_calls invContextH_update_callOrigin invContextH_update_txstatus

lemma test:
  fixes S:: "('localState, 'any::valueType) state"
  assumes a7: "currentTransaction S sa \<triangleq> t"
  assumes a10: "state_wellFormed S"
  assumes a11: "sb\<noteq>sa"
  assumes a12: "calls S c = None"
  shows "invContext
           (S\<lparr>localState := localState S(sa \<mapsto> ls' res), calls := calls S(c \<mapsto> Call operation args res),
                callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(sa \<mapsto> {c} \<union> vis),
                happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>)
           
  = invContext S "
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
      state_wellFormed S;
      visibleCalls S sb \<triangleq> visa; 
      calls S c = None
    \<rbrakk> \<Longrightarrow> c\<notin>visa"
  by (meson domIff set_mp wellFormed_visibleCallsSubsetCalls_h(2))

lemma callsInTransactionH_originUpdate_unchanged[simp]:
  assumes a1: "currentTransaction S sa \<triangleq> t"
    and a2: "state_wellFormed S"
    and a3: "calls S c = None"
    and a4: "txns \<subseteq> committedTransactions S"
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
  case (AInvcheck res)
  with a2 show ?thesis 
    apply simp
    apply (rule show_commutativeS_pres)
    by (auto simp add: precondition_def commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist subset_eq invContextH_simps)
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
      \<comment> \<open>   case (APull txns)  \<close>
  show ?thesis
  proof (induct rule: show_commutativeS_pres2)
    case (preBfront s1)
    then show "precondition (sb, a) S" 
      using a2 by (auto simp add: precondition_dbop precondition_beginAtomic step_simps split: if_splits elim!: chooseSnapshot_unchanged_precise)

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
      using a2 by (auto simp add: precondition_dbop precondition_beginAtomic step_simps split: if_splits elim!: chooseSnapshot_unchanged_precise)
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
      by (auto simp add: a1[symmetric] step_simps wellFormed_visibleCallsSubsetCalls2  split: if_splits) \<comment> \<open>  takes long \<close>
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
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute elim!: chooseSnapshot_unchanged_precise)
next
  case AEndAtomic
  then show ?thesis by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute)
next
  case (ADbOp x51 x52 x53 x54)
  then show ?thesis
    using a1 a2 commutativeS_switchArgs commutative_Dbop_other by metis
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
  by (auto simp add: commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute elim!: chooseSnapshot_unchanged_precise)


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
      \<comment> \<open> apply (auto simp add: commutativeS_def steps_appendFront step_simps a_is_in_transaction wellFormed_invoc_notStarted) \<close>
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
    case (AInvcheck res)
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
    by (auto simp add: steps_appendFront)
  moreover have "... \<longleftrightarrow> (\<exists>S'. (S ~~ [b,a] \<leadsto>* S') \<and> (S' ~~ xs \<leadsto>* T))"
    by (metis a_is_in_transaction b_is_a_different_session local.wf move_transaction not_endAtomic prod.collapse not_invCheck)
  moreover have "... \<longleftrightarrow> (S ~~ b#a#xs \<leadsto>* T)" 
    by (auto simp add: steps_appendFront)
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
      using ABeginAtomic apply (auto simp add: step_simps contra_subsetD split: if_splits elim!: chooseSnapshot_unchanged_precise)[1]
      using ABeginAtomic   apply (auto simp add: step_simps contra_subsetD split: if_splits elim!: chooseSnapshot_unchanged_precise)[1]
      apply (subst state_ext)
      using ABeginAtomic by (auto simp add: step_simps split: if_splits elim!: chooseSnapshot_unchanged_precise)

  next
    case AEndAtomic \<comment> \<open>  this is not commutative, since the transaction committed could be included in ht next snapshot \<close>
    thus ?thesis
      using no_end_atomic by auto 
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis
      using a1 a2 commutativeS_switchArgs commutative_Dbop_other by metis 
        (**next
  case (APull x6)
  then show ?thesis 
  by (auto simp add: a2 commutativeS_def steps_appendFront a1[symmetric]  step_simps fun_upd_twist insert_commute,
    auto, smt mem_Collect_eq option.inject subsetCE transactionStatus.distinct(1))*)
  next
    case (AInvoc x71 x72)
    then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits elim!: chooseSnapshot_unchanged_precise)
  next
    case (AReturn x8)
    then show ?thesis by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute split: if_splits elim!: chooseSnapshot_unchanged_precise)
  next
    case AFail
    then show ?thesis
      using a1 a2 commutativeS_switchArgs commutative_fail_other by metis 
  next
    case (AInvcheck x10)
    then show ?thesis 
      by (auto simp add: a2 commutativeS_def steps_appendFront step_simps fun_upd_twist insert_commute invContextH_simps split: if_splits, auto simp add: invContextH_def )
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




\<comment> \<open>  todo and now move everything out of transactions ...  \<close>

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

lemma currentTransaction_unchangedInternalSteps4:
  assumes "S ~~ tr \<leadsto>* S'"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> a \<noteq> (s, AEndAtomic)"
    and "\<And>a.  a \<in> set tr \<Longrightarrow> a \<noteq> (s, AFail)"
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
      using state_wellFormed_combine  
      by (metis action.distinct(39) empty_iff insert_iff list.set(1) list.simps(15) snd_conv steps_single)
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
        using wf that apply (rule state_wellFormed_combine)
        using snoc.prems(2) by fastforce
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
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C)"
proof 
  assume "s_init ~~ tr \<leadsto>* C"
  with steps_append 
  obtain S_mid where "s_init ~~ trStart \<leadsto>* S_mid" and "S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C"
    using splitTrace by blast

  have "state_wellFormed S_mid"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> local.wf noFail splitTrace state_wellFormed_combine by fastforce


  from `S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C`
  have "S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    using \<open>state_wellFormed S_mid\<close> no_endatomic one_compaction_step txaInTx xOutside by blast

  thus "s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> steps_append2 by blast
next \<comment> \<open>Other direction is very similar:\<close>
  assume "s_init ~~ trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
  with steps_append 
  obtain S_mid where "s_init ~~ trStart \<leadsto>* S_mid" and "S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C"
    by blast

  have "state_wellFormed S_mid"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> local.wf noFail splitTrace state_wellFormed_combine by fastforce

  from `S_mid ~~ x # (s, ABeginAtomic tx ntxns) # txa @ rest \<leadsto>* C`
  have "S_mid ~~ (s, ABeginAtomic tx ntxns) # txa @ x # rest \<leadsto>* C"
    using \<open>state_wellFormed S_mid\<close> no_endatomic one_compaction_step txaInTx xOutside by blast

  thus "s_init ~~ tr \<leadsto>* C"
    using \<open>s_init ~~ trStart \<leadsto>* S_mid\<close> splitTrace steps_append2 by blast
qed


lemma one_compaction_step3:
  assumes splitTrace: "tr = trStart @ (s, ABeginAtomic tx ntxns) # txa @ x # rest" 
    and splitTrace': "tr' = trStart @ x # (s, ABeginAtomic tx ntxns) # txa @ rest"
    and txaInTx: "\<And>st at. (st,at)\<in>set txa \<Longrightarrow> st=s \<and> at \<noteq> AEndAtomic \<and> at \<noteq> AFail \<and> \<not> is_AInvcheck at"
    and xOutside: "fst x \<noteq> s"
    and wf: "state_wellFormed s_init"
    and no_endatomic: "snd x \<noteq> AEndAtomic"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "(s_init ~~ tr \<leadsto>* C)  \<longleftrightarrow> (s_init ~~ tr' \<leadsto>* C)"
  using local.wf one_compaction_step2 splitTrace splitTrace' txaInTx xOutside no_endatomic noFail by blast 

definition indexInOtherTransaction :: "'any trace \<Rightarrow> txid \<Rightarrow> nat \<Rightarrow> bool" where
  "indexInOtherTransaction tr tx k \<equiv> 
  \<exists>i s ntxns. 
      k<length tr 
    \<and> i<k 
    \<and> tr!i = (s, ABeginAtomic tx ntxns)  
    \<and> fst (tr!k) \<noteq> s
    \<and> \<not>(\<exists>j. i < j \<and> j < k \<and> tr!j = (s, AEndAtomic))"

definition transactionIsPacked :: "'any trace \<Rightarrow> txid \<Rightarrow> bool" where
  "transactionIsPacked tr tx \<equiv> 
  \<forall>k. \<not>indexInOtherTransaction tr tx k"  

definition transactionIsPackedMeasure :: "'any trace \<Rightarrow> txid \<Rightarrow> nat" where
  "transactionIsPackedMeasure tr tx \<equiv>
  card {k . indexInOtherTransaction tr tx k}"  

lemma indexInOtherTransaction_finite[simp]: "finite {k. indexInOtherTransaction tr tx k}"
  by (auto simp add: indexInOtherTransaction_def)

lemma transactionIsPackedMeasure_zero_iff: 
  "transactionIsPackedMeasure tr tx = 0 \<longleftrightarrow>  transactionIsPacked tr tx" 
  by (auto simp add: transactionIsPackedMeasure_def transactionIsPacked_def)

\<comment> \<open>  this is an alternative definition, which might be easier to work with in some cases  \<close>
definition transactionIsPackedAlt :: "'any trace \<Rightarrow> txid \<Rightarrow> bool" where
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

lemma currentTransaction2:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "i < length tr"
    and "tr!i = (s, ABeginAtomic txi ntxns)"
    and "\<And>j. \<lbrakk>i<j; j<length tr\<rbrakk> \<Longrightarrow> tr!j \<noteq> (s, AFail)"
    and "\<And>j. \<lbrakk>i<j; j<length tr\<rbrakk> \<Longrightarrow> tr!j \<noteq> (s, AEndAtomic)"
  shows "currentTransaction S' s \<triangleq> txi"
  using assms currentTransaction by blast


lemma noNestedTransactions:
  assumes steps: "S ~~ tr \<leadsto>* S'" 
    and "tr!i = (s, ABeginAtomic txi ntxnsi)"
    and "i<j"
    and "j < length tr" 
    and "tr!j = (s, ABeginAtomic txj ntxnsj)"
  shows "\<exists>k. i<k \<and> k < j \<and> (tr!k = (s, AEndAtomic) \<or> tr!k = (s, AFail))"  
  using assms proof (induct rule: steps.induct)
  case (steps_refl S)
  then show ?case by simp
next
  case (steps_step S tr S' a S'')
  then show ?case 
  proof (cases "j < length tr")
    case True
    then show ?thesis
      using steps_step by (auto simp add: nth_append dest: less_trans)
  next
    case False
    hence [simp]: "j = length tr"
      using steps_step by auto


    have "S ~~ tr@[a] \<leadsto>* S''"
      using steps.steps_step steps_step.hyps(1) steps_step.hyps(3) by blast
    have "(tr @ [a]) ! i = (s, ABeginAtomic txi ntxnsi)"
      by (simp add: steps_step.prems(1))  
    have "i < j"
      using steps_step.prems(2) by blast
    have "j < length (tr @ [a])"
      by simp
    have "(tr @ [a]) ! j = (s, ABeginAtomic txj ntxnsj)"
      using steps_step.prems(4) by blast  
    hence "a =  (s, ABeginAtomic txj ntxnsj)"
      by simp

    have "i < length tr"
      using \<open>j = length tr\<close> steps_step.prems(2) by blast  

    have "tr ! i = (s, ABeginAtomic txi ntxnsi)"
      by (metis \<open>i < length tr\<close> nth_append steps_step.prems(1))  

    from `S' ~~ a \<leadsto> S''`  
    have "precondition (s, ABeginAtomic txj ntxnsj) S'"
      by (simp add: \<open>a = (s, ABeginAtomic txj ntxnsj)\<close>)



    show "\<exists>k>i. k < j \<and> ((tr @ [a]) ! k = (s, AEndAtomic) \<or> (tr @ [a]) ! k = (s, AFail))"
      using currentTransaction[OF `S ~~ tr \<leadsto>* S'` `i < length tr` `tr ! i = (s, ABeginAtomic txi ntxnsi)`] 
      apply (auto simp add: nth_append  dest: less_trans)
      thm \<open>j = length tr\<close> nth_append_length option.simps(3) preconditionI precondition_beginAtomic steps_step.hyps(3) steps_step.prems(4)
      by (metis \<open>j = length tr\<close> nth_append_length option.simps(3) preconditionI precondition_beginAtomic steps_step.hyps(3) steps_step.prems(4))
  qed      
qed  



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
  by (auto simp add: transactionIdsUnique[OF steps] transactionIsPackedAlt_eq)

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
    \<comment> \<open>  by (smt a1 beginAtomic1 beginAtomic2 endAtomic1 endAtomic2 fst_conv indexInOtherTransaction_def leI less_imp_le_nat less_trans steps transactionIdsUnique transactionIsPacked_def)  \<close>
proof (auto simp add: transactionIsPacked_def indexInOtherTransaction_def)
  fix k i s' ntxns
  assume b0: "k < length tr"
    and b1: "i < k"
    and b2: "tr ! i = (s', ABeginAtomic tx ntxns)"
    and b3: "\<forall>j>i. j < k \<longrightarrow> tr ! j \<noteq> (s', AEndAtomic)"
    and b4: "fst (tr ! k) \<noteq> s'"

  from b2
  have "i = beginAtomic"
    using b0 b1 beginAtomic1 beginAtomic2 endAtomic1 transactionIdsUnique[OF steps] by auto
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
  oops \<comment> \<open>  TODO needs more restrictive definition of transactionIsPacked  \<close>


\<comment> \<open>  the set of transactions occurring in the trace  \<close>    
definition traceTransactions :: "'any trace \<Rightarrow> txid set" where
  "traceTransactions tr \<equiv> {tx | s tx txns. (s, ABeginAtomic tx txns) \<in> set tr}"

text {* between begin and end of a transaction there are no actions from other sessions  *}
definition transactionsArePacked :: "'any trace \<Rightarrow> bool" where
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


\<comment> \<open>  checks if sessions s is in a transaction at position i in trace tr  \<close>
definition inTransaction :: "'any trace \<Rightarrow> nat \<Rightarrow> invocId \<Rightarrow> bool"  where 
  "inTransaction tr i s \<equiv>
  \<exists>j. j\<le>i \<and> i<length tr \<and> (\<exists>t txns. tr!j = (s, ABeginAtomic t txns))
     \<and> (\<forall>k. j<k \<and> k < length tr \<and> k\<le>i \<longrightarrow> tr!k \<noteq> (s, AEndAtomic))
"

\<comment> \<open>  returns the set of all transactions, which are in a transaction at point i in the trace \<close>
definition sessionsInTransaction :: "'any trace \<Rightarrow> nat \<Rightarrow> invocId set"  where 
  "sessionsInTransaction tr i \<equiv> {s. inTransaction tr i s}"

\<comment> \<open>  counts how many concurrent transactions are active  \<close>
definition transactionsArePackedMeasure :: "'any trace \<Rightarrow> nat" where
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
fun sessionsInTransactionRevAlt :: "trace \<Rightarrow> nat \<Rightarrow> invocId set"  where
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
  proof (case_tac a, auto)
    show "\<And>aa x. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr; x \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr); x \<notin> sessionsInTransaction tr (length tr - Suc 0)\<rbrakk> \<Longrightarrow> x = aa"
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
      by (metis (full_types) Suc_leI Suc_le_mono Suc_pred gr_implies_not_zero less_imp_le_nat nat_neq_iff)
    show "\<And>aa. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr\<rbrakk> \<Longrightarrow> aa \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr)"
      by (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
    show "\<And>aa x. \<lbrakk>a = (aa, ABeginAtomic t ts); i = length tr; x \<in> sessionsInTransaction tr (length tr - Suc 0)\<rbrakk> \<Longrightarrow> x \<in> sessionsInTransaction (tr @ [(aa, ABeginAtomic t ts)]) (length tr)"
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def  split: if_splits)[1]
      by (metis Suc_diff_Suc le0 le_less_trans less_Suc_eq_le minus_nat.diff_0)
  qed
next
  assume a0: "i = length tr"
    and a1: "snd a = AEndAtomic"

  thus "sessionsInTransaction (tr @ [a]) (length tr) = sessionsInTransaction tr (length tr - Suc 0) - {fst a}"
    apply (case_tac a, auto)
      apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
      apply (smt Suc_pred inc_induct less_Suc_eq less_imp_le_nat linorder_neqE_nat not_less_zero)
     apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def sndI split: if_splits)[1]
    apply (auto simp add: nth_append sessionsInTransaction_def inTransaction_def split: if_splits)[1]
    by (metis Suc_pred leD le_SucI length_greater_0_conv less_Suc_eq_le list.size(3) not_less_zero)
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
    \<comment> \<open>  TODO nicer proof \<close>

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
    \<comment> \<open>  this proof should be easier ...  \<close>
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



    { \<comment> \<open>  First consider the case where we have an earlier AEndAtomic for s  \<close>
      assume "(txa ! otherI) = (s, AEndAtomic)"
      with noEndAtomic
      have "False"
        apply (auto simp add: txa_def )
        using \<open>otherI < min_i - Suc j\<close> less_imp_le_nat min_i1 by auto
    }
    note case_endAtomic = this

    { \<comment> \<open>  Next, we consider the case where txa contains an action from a different invocId \<close>
      assume differentSession: "fst (txa ! otherI) \<noteq> s"

      define s' where s'_def: "s' = fst (txa ! otherI)"
      hence differentSession2: "s' \<noteq> s"
        by (simp add: differentSession) 

      define min_i' where min_i'_def: "min_i' = otherI + length trStart + 1"

      have [simp]: "fst (tr ! min_i') = s'"
        using min_i'_def s'_def trStart_def txa_def
        by (auto simp add: Suc_leI add.commute)

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
    \<comment> \<open>  this proof should be easier ...  \<close>
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



    { \<comment> \<open>  First consider the case where we have an earlier AEndAtomic for s  \<close>
      assume "(txa ! otherI) = (s, AEndAtomic)"
      with noEndAtomic
      have "False"
        apply (auto simp add: txa_def )
        using \<open>otherI < min_i - Suc j\<close> less_imp_le_nat i1 by auto
    }
    note case_endAtomic = this

    { \<comment> \<open>  Next, we consider the case where txa contains an action from a different invocId \<close>
      assume differentSession: "fst (txa ! otherI) \<noteq> s"

      define s' where s'_def: "s' = fst (txa ! otherI)"
      hence differentSession2: "s' \<noteq> s"
        by (simp add: differentSession) 

      define min_i' where min_i'_def: "min_i' = otherI + length trStart + 1"

      have [simp]: "fst (tr ! min_i') = s'"
        using min_i'_def s'_def trStart_def txa_def
        by (auto simp add: Suc_leI add.commute  j1)

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

(*
  ALocal
  | ANewId 'any
  | ABeginAtomic txid "txid set"
  | AEndAtomic
  | ADbOp callId operation "'any list" 'any
  | AInvoc procedureName "'any list"
  | AReturn 'any
  | AFail  
  | AInvcheck "txid set" bool
*)

lemma allowed_context_switch_simps[simp]:
  shows "\<not>allowed_context_switch ALocal" 
    and "\<not>allowed_context_switch (ANewId uid)"
    and "allowed_context_switch (ABeginAtomic t ats)"
    and "\<not>allowed_context_switch AEndAtomic" 
    and "\<not>allowed_context_switch (ADbOp c x a ar)" 
    and "allowed_context_switch (AInvoc p ia)"
    and "\<not>allowed_context_switch (AReturn ir)" 
    and "\<not>allowed_context_switch AFail" 
    and "\<not>allowed_context_switch (AInvcheck invr)" by (auto simp add: allowed_context_switch_def)


definition packed_trace :: "'any trace \<Rightarrow> bool" where
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
    \<comment> \<open> "(\<exists>tx txns. a' = ABeginAtomic tx txns) \<or> (\<exists>p ar. a' = AInvoc p ar)" \<close>
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

definition canSwap :: "'ls itself \<Rightarrow> 'any::valueType action \<Rightarrow> 'any action \<Rightarrow> bool" where
  "canSwap t a b \<equiv> (\<forall>(C1::('ls,'any) state) C2 s1 s2. s1\<noteq>s2 \<and> (C1 ~~ [(s1,a),(s2,b)] \<leadsto>* C2) \<and> state_wellFormed C1 \<longrightarrow> (C1 ~~ [(s2,b),(s1,a)] \<leadsto>* C2))"

lemma show_canSwap:
  assumes "\<And>(C1::('ls,'any::valueType) state) C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
  shows "canSwap (t::'ls itself) a b"
proof (auto simp add: canSwap_def)
  fix C1 C3 :: "('ls,'any) state"
  fix s1 s2
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
    and"\<And>(C1::('ls,'any::valueType) state) C2 C3 s1 s2. \<lbrakk>s1 \<noteq> s2; C1 ~~ (s1,a) \<leadsto> C2; C2 ~~ (s2,b) \<leadsto> C3; state_wellFormed C1\<rbrakk> \<Longrightarrow> \<exists>C. (C1 ~~ (s2,b) \<leadsto> C) \<and> (C ~~ (s1,a) \<leadsto> C3)"
  shows "canSwap (t::'ls itself) x b"
  by (simp add: assms show_canSwap)

method prove_canSwap = (rule show_canSwap, auto simp add: step_simps elim!: chooseSnapshot_unchanged_precise, subst state_ext, auto)  
method prove_canSwap' = (rule show_canSwap', auto simp add: step_simps elim!: chooseSnapshot_unchanged_precise, subst state_ext, auto)
method prove_canSwap'' = (rule show_canSwap', auto del: ext  simp add: step_simps intro!: stateEqI ext split: if_splits elim!: chooseSnapshot_unchanged_precise)

lemma commutativeS_canSwap:
  assumes comm: "\<And>(C::('ls,'any::valueType) state) s1 s2. s1\<noteq>s2 \<Longrightarrow> commutativeS C (s1,a) (s2,b)"
  shows "canSwap (t::'ls itself) a b"
proof (auto simp add: canSwap_def)
  fix C1 C2 :: "('ls,'any) state"
  fix s1 s2
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
  shows "canSwap t a b"
proof (cases b)
  case ALocal
  then show ?thesis
    by (simp add: commutativeS_canSwap) 
next
  case (ANewId bid)
  hence [simp]: "b = ANewId bid" .
  show ?thesis 
  proof (cases a; prove_canSwap?)
    case (AInvcheck r)
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
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis by prove_canSwap''
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis by prove_canSwap''
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case (ADbOp x51 x52 x53 x54)
  hence [simp]: "b = ADbOp x51 x52 x53 x54" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis
      by (meson canSwap_def commutative_Dbop_other useCommutativeS)  
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis
      using no_fail_a by blast 
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by blast 
  qed
next
  case (AInvoc x61 x62)
  then show ?thesis
    using allowed_context_switch_def[where action = b] no_ctxt_switch by auto 

next
  case (AReturn res)
  hence [simp]: "b = AReturn res" .
  then show ?thesis 
  proof (cases a)
    case ALocal
    then show ?thesis by prove_canSwap''
  next
    case (ANewId x2)
    then show ?thesis by prove_canSwap''
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis by prove_canSwap''
  next
    case AEndAtomic
    then show ?thesis by prove_canSwap''
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis by prove_canSwap''
  next
    case (AInvoc x61 x62)
    then show ?thesis by prove_canSwap''
  next
    case (AReturn x7)
    then show ?thesis by prove_canSwap''
  next
    case AFail
    then show ?thesis by prove_canSwap''
  next
    case (AInvcheck r)
    then show ?thesis
      using is_AInvcheck_def no_invcheck_a by auto 
  qed
next
  case AFail
  then show ?thesis
    using no_fail_b by blast 
next
  case (AInvcheck r)
  then show ?thesis
    using is_AInvcheck_def no_invcheck_b by auto 
qed


text {* We can swap one action over a list of actions with canSwap *}
lemma swapMany:
  assumes steps: "(C1::('ls,'any::valueType) state) ~~ tr @ [(s,a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) a"
    and wf: "state_wellFormed C1"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
  shows "C1 ~~ [(s,a)] @ tr \<leadsto>* C2"
  using steps tr_different_session tr_canSwap noFail
proof (induct tr arbitrary: C2 rule: rev_induct)
  case Nil
  then show ?case
    by simp 
next
  case (snoc a' tr')
  hence IH: "\<And>C2. \<lbrakk>C1 ~~ tr' @ [(s, a)] \<leadsto>* C2; \<And>x. x \<in> set tr' \<Longrightarrow> fst x \<noteq> s; \<And>x. x \<in> set tr' \<Longrightarrow> canSwap t (snd x) a\<rbrakk> \<Longrightarrow> C1 ~~ [(s, a)] @ tr' \<leadsto>* C2" 
    and steps: "C1 ~~ (tr' @ [a']) @ [(s, a)] \<leadsto>* C2"
    and tr_different_session: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x \<in> set (tr' @ [a']) \<Longrightarrow> canSwap t (snd x) a"
    and noFail2a: "\<And>i. (i, AFail) \<notin> set (tr' @ [a'])"
    by auto

  from steps
  obtain C'
    where steps1: "C1 ~~ tr' \<leadsto>* C'" 
      and steps2: "C' ~~ [a', (s, a)] \<leadsto>* C2"
    by (auto simp add: steps_append)

  have wf': "state_wellFormed C'"
    using local.wf state_wellFormed_combine steps1 noFail2a by auto 

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
  fixes C1 :: "('ls,'any::valueType) state"
  assumes steps: "C1 ~~ tr_start @ tr @ [(s,a)] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> s"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) a"
    and wf: "state_wellFormed C1"
    and nofail1: "\<And>i. (i,AFail)\<notin> set tr_start"
    and nofail2: "\<And>i. (i,AFail)\<notin> set tr"
  shows "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
proof -
  from steps
  obtain C1' C2'
    where "C1 ~~ tr_start \<leadsto>* C1'" and "C1' ~~ tr @ [(s,a)] \<leadsto>* C2'" and "C2' ~~ tr_end \<leadsto>* C2"
    by (meson steps_append)

  hence "C1' ~~ [(s,a)] @ tr  \<leadsto>* C2'"
    using local.wf state_wellFormed_combine swapMany tr_canSwap tr_different_session nofail1 nofail2  by blast 

  thus "C1 ~~ tr_start @ [(s,a)] @ tr @ tr_end \<leadsto>* C2"
    using \<open>C1 ~~ tr_start \<leadsto>* C1'\<close> \<open>C2' ~~ tr_end \<leadsto>* C2\<close>
    using steps_append by blast  
qed    

lemma swapMany_middle':
  fixes C1 :: "('ls,'any::valueType) state"
  assumes steps: "C1 ~~ tr_start @ tr @ [a] @ tr_end \<leadsto>* C2"
    and tr_different_session: "\<And>x. x\<in>set tr \<Longrightarrow> fst x \<noteq> (fst a)"
    and tr_canSwap: "\<And>x. x\<in>set tr \<Longrightarrow> canSwap (t::'ls itself) (snd x) (snd a)"
    and wf: "state_wellFormed C1"
    and nofail1: "\<And>i. (i,AFail)\<notin> set tr_start"
    and nofail2: "\<And>i. (i,AFail)\<notin> set tr"
  shows "C1 ~~ tr_start @ [a] @ tr @ tr_end \<leadsto>* C2"
  using assms apply (cases a)
  apply (rule ssubst, assumption, rule swapMany_middle)
     apply auto
  done

lemma localState_iff_exists_invoc:
  assumes steps: "initialState program ~~ tr \<leadsto>* C"
  shows "localState C s \<noteq> None \<longrightarrow> (\<exists>p args. (s, AInvoc p args) \<in> set tr)"
  using invation_info_set_iff_invocation_happened(1) invocation_ops_if_localstate_nonempty steps by blast
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
      using is_AInvcheck_def[where a="(snd ((tr @ [a]) ! i))"] step.prems(4) by auto
  next
    case False
    hence "i < length tr"
      using step.prems(1) by auto

    then show ?thesis
      by (smt less_imp_le less_le_trans nth_append_first step.IH step.prems(2) step.prems(3) step.prems(4)) 
  qed
qed

definition packed_trace_s :: "'any trace \<Rightarrow> invocId \<Rightarrow> bool" where
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
    by (metis bounded bounded_Max_nat)
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
    \<comment> \<open>  I could not figure out how to write this down as an induction over the minimum, so I reversed it and made it an induction over the maximum inversed index.  \<close>
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

    text {* There must be a previous action on the same invocId (at least the invocId should be there, since i is no invocId). *}
    obtain prev
      where prev1: "fst(tr!prev) = s"
        and prev2: "prev < i"
        and prev3: "\<And>j. \<lbrakk>prev < j; j < i\<rbrakk> \<Longrightarrow> fst(tr!j) \<noteq> s"
    proof (atomize_elim)
      from `initialState program ~~ tr \<leadsto>* C` `i<length tr` `fst (tr!i) = s`
      have "\<exists>j<i. fst (tr ! j) = s \<and> (\<exists>p args. snd (tr ! j) = AInvoc p args)"
      proof (rule exists_invoc)
        show "\<And>p args. snd (tr ! i) \<noteq> AInvoc p args"
          using allowed_context_switch_def[where action="snd (tr ! i)"] i5 by auto 
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
      show "canSwap t (snd x) (snd (tr ! i))" if "x \<in> set (drop (Suc prev) (take i tr))" for x t
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

      from noFail
      show "\<And>i. (i, AFail) \<notin> set (take prev tr @ [tr ! prev])"
        by (metis \<open>prev < length tr\<close> hd_drop_conv_nth in_set_takeD take_hd_drop)
      from noFail
      show "\<And>ia. (ia, AFail) \<notin> set (drop (Suc prev) (take i tr))"
        by (meson in_set_dropD in_set_takeD)
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

text {* Now we can just repeat fixing invocId by invocId, until all sessions are packed. *}
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
    where failPos1_props: "failPos1 < length tr \<and> (\<exists>s. tr ! failPos1 = (s, AInvcheck False))"
    by (meson in_set_conv_nth traceCorrect_def)

  text {* Now take the minimal failing position. *}  
  hence "\<exists>failPos1. (failPos1 < length tr \<and> (\<exists>s. tr ! failPos1 = (s, AInvcheck False)))
           \<and> (\<forall>i. (i < length tr \<and> (\<exists>s. tr ! i = (s, AInvcheck False))) \<longrightarrow> i \<ge> failPos1)"
    by (rule ex_has_least_nat)
  from this
  obtain failPos failPos_s 
    where failPos_len: "failPos < length tr" 
      and failPos_fail: "tr ! failPos = (failPos_s, AInvcheck False)"
      and failPos_min: "\<And> i. \<lbrakk>i < length tr; \<exists>s txns. tr ! i = (s, AInvcheck False)\<rbrakk> \<Longrightarrow> i\<ge>failPos"
    by auto



  text {* Only the part leading to the invariant violation is relevant ...*}  

  define tr' where "tr' = take failPos tr"

  from steps
  obtain C' where tr'_steps: "initialState program ~~ tr' \<leadsto>* C'"
    by (metis append_take_drop_id steps_append tr'_def)

  from steps
  have "initialState program ~~ (tr'@[tr!failPos]@drop (Suc failPos) tr) \<leadsto>* C"
    by (metis \<open>failPos < length tr\<close> append.assoc append_take_drop_id take_Suc_conv_app_nth tr'_def)
  hence "\<exists>C''. C' ~~ tr ! failPos  \<leadsto>  C''"
    using  tr'_steps by (auto simp add: steps_append2 steps_appendFront)

  hence C'_fails: "\<And>s. C' ~~ (s, AInvcheck False) \<leadsto> C'"  
    by (auto simp add: failPos_fail step_simps)


  text {* Now remove all other invariant checks *}
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

  define tr4 where "tr4 = tr''' @ [(fst (last tr'''), AInvcheck False)]"

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

lemma use_Greatest:
  assumes "\<exists>x. P x"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
  shows "P (GREATEST x::nat. P x)
\<and> (\<forall>y. P y \<longrightarrow> y \<le> (GREATEST x::nat. P x))"
  using GreatestI_nat Greatest_le_nat assms by auto

lemma Greatest_smaller:
  assumes "\<exists>x::nat. P x"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
    and "\<And>y. P y \<Longrightarrow> y < x"
  shows "Greatest P < x"
  using assms
  using GreatestI_nat by auto  

lemma Greatest_bigger:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P y"
    and "\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound"
    and "x < y"
  shows "x < Greatest P"
proof -
  from `P y` have "\<exists>x. P x" by auto

  from use_Greatest[OF `\<exists>x. P x` `\<exists>bound. \<forall>x. P x \<longrightarrow> x \<le> bound`] assms
  show "x < Greatest P"
    by auto
qed


definition openTransactions :: "'any trace \<Rightarrow> (invocId \<times> txid) set" where
"openTransactions tr \<equiv> {(i, tx) | i j tx txns. j<length tr \<and> tr!j = (i, ABeginAtomic tx txns) \<and> (\<forall>k. k>j \<and> k<length tr \<longrightarrow> tr!k \<noteq> (i, AEndAtomic))}"


lemma open_transactions_empty[simp]:
  shows "openTransactions [] = {}"
  by (auto simp add: openTransactions_def)

lemma open_transactions_append_one: 
  shows "openTransactions (tr@[a]) =
(case a of
    (i, AEndAtomic) \<Rightarrow> openTransactions tr - ({i} \<times> UNIV)
  | (i, ABeginAtomic tx txns) \<Rightarrow> openTransactions tr \<union> {(i, tx)}
  | _ \<Rightarrow> openTransactions tr
)"
proof -
  obtain invoc action where a_def[simp]: "a = (invoc, action)"
    using prod.exhaust_sel by blast
  show ?thesis
  proof (cases action)
    case ALocal
    then show ?thesis 
      by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (ANewId x2)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (ABeginAtomic x31 x32)
    then show ?thesis 
      apply (auto simp add: openTransactions_def nth_append split: prod.splits action.splits)
        apply blast
       apply blast
      by fastforce
  next
    case AEndAtomic
    then show ?thesis
      by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast+)
  next
    case (ADbOp x51 x52 x53 x54)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AInvoc x61 x62)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AReturn x7)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case AFail
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  next
    case (AInvcheck r)
    then show ?thesis by (auto simp add: openTransactions_def nth_append split: prod.splits action.splits, blast)
  qed
qed


definition allTransactionsEnd :: "'any trace \<Rightarrow> bool" where
  "allTransactionsEnd tr \<equiv> \<forall>i j tx txns. j<length tr \<and> tr!j = (i, ABeginAtomic tx txns) \<longrightarrow> (\<exists>k. k>j \<and> k<length tr \<and> tr!k = (i, AEndAtomic))"

lemma allTransactionsEnd_def_alt: 
"allTransactionsEnd tr \<longleftrightarrow> (openTransactions tr = {})"
  by (auto simp add: allTransactionsEnd_def openTransactions_def, blast)



text {*
If only the local states in invocId i differ,
we can transfer an execution to the different state,
when the execution trace contains no action in i.
*}

find_consts "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"


lemma show_state_transfer:
  assumes steps: "S_start ~~ tr \<leadsto>* S_end"
    and step_simulate: "\<And>a S S'. \<lbrakk>a\<in>set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
    and step_preserves: "\<And>a S S'. \<lbrakk>a\<in>set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> P S'"
    and prop_initial: "P S_start"
  shows "(T S_start ~~ tr \<leadsto>* T S_end) \<and> P S_end"
  using steps step_simulate step_preserves prop_initial proof (induct rule: steps_induct)
  case initial
  show "(T S_start ~~ [] \<leadsto>* T S_start) \<and> P S_start"
    using `P S_start` by auto 
next
  case (step S' tr a S'')
  show "(T S_start ~~ tr @ [a] \<leadsto>* T S'') \<and> P S''" 
  proof (intro conjI)
    show "P S''"
      by (metis append_is_Nil_conv butlast_snoc in_set_butlastD last_in_set last_snoc list.simps(3) prop_initial step.IH step.prems(1) step.prems(2) step.step)
    show " T S_start ~~ tr @ [a] \<leadsto>* T S''"
      by (metis UnI2 butlast_snoc in_set_butlastD list.set_intros(1) prop_initial set_append step.IH step.prems(1) step.prems(2) step.step steps_step)
  qed
qed

lemma show_state_transfer2_noP:
  assumes steps: "S_start ~~ tr \<leadsto>* S_end"
    and step_simulate: "\<And>i a S S'. \<lbrakk>(i,a)\<in>set tr; S ~~ (i,a) \<leadsto> S'\<rbrakk> \<Longrightarrow> T S ~~ (i,a) \<leadsto> T S'"
  shows "T S_start ~~ tr \<leadsto>* T S_end"
proof -
  from steps
  have "(T S_start ~~ tr \<leadsto>* T S_end) \<and> True"
    by (rule show_state_transfer; auto simp add: assms)
  thus ?thesis by simp
qed



lemma remove_local_step: 
  fixes S_start S_end :: "('ls,'any::valueType) state" 
  assumes step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ALocal)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and S_end'_def: "S_end' = S_end\<lparr>localState := (localState S_end)(i := localState S_start i)\<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('ls,'any) state. S\<lparr>localState := (localState S)(i := localState S_start i)\<rparr>"

  have "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  from steps_tr
  have "T S_mid ~~ tr \<leadsto>* T S_end"
  proof (rule show_state_transfer2_noP)
    show "T S ~~ (i',a) \<leadsto> T S'" if "(i',a) \<in> set tr" and  "S ~~ (i',a) \<leadsto> S'" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using `(i',a) \<in> set tr` no_i by force 
      hence [simp]: "i \<noteq> i'" by blast 

      from `S ~~ (i',a) \<leadsto> S'` 
      show "T S ~~ (i',a) \<leadsto> T S'"
        by (induct rule: step.cases, auto simp add: step_simps T_def state_ext elim: chooseSnapshot_unchanged_precise)
    qed
  qed

  thus "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by auto
qed

lemma uid_used_only_once:
  assumes steps:  "S_start ~~ tr \<leadsto>* S_end"
    and alreadyGenerated: "generatedIds S_start uid \<triangleq> i'"
  shows "(i, ANewId uid) \<notin> set tr"
proof -
  have "(i, ANewId uid) \<notin> set tr \<and> generatedIds S_end uid \<triangleq> i'"
    using steps alreadyGenerated proof (induct rule: steps_induct)
    case initial
    then show ?case by simp
  next
    case (step S' tr a S'')
    then show ?case apply (auto simp add: step_simps)
      using generatedIds_mono2 by blast
  qed
  thus ?thesis by simp
qed


lemma remove_newId_step: 
  fixes S_start S_end :: "('ls,'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ANewId uid)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and S_end'_def: "S_end' = S_end\<lparr>generatedIds := (generatedIds S_end)(uid := None), localState := (localState S_end)(i := localState S_start i)\<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('ls,'any) state. S\<lparr>generatedIds := (generatedIds S)(uid := None), localState := (localState S)(i := localState S_start i)\<rparr>"

  have "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  have uid_fresh: "generatedIds S_start uid = None"
    using step_a a_def by (auto simp add: step_simps)

  obtain uid_i where "generatedIds S_mid uid \<triangleq> uid_i"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  from `S_mid ~~ tr \<leadsto>* S_end` `generatedIds S_mid uid \<triangleq> uid_i`
  have uid_not_used: "(i, ANewId uid) \<notin> set tr" for i
    by (rule uid_used_only_once)

  from steps_tr
  have "T S_mid ~~ tr \<leadsto>* T S_end"
  proof (rule show_state_transfer2_noP)
    show "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  "S ~~ (i',a) \<leadsto> S'" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using `(i',a) \<in> set tr` no_i by force 
      hence [simp]: "i \<noteq> i'" by blast 

      from `S ~~ (i',a) \<leadsto> S'` 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace uid_not_used by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
        then show ?case by (auto simp add: step_simps T_def state_ext elim: chooseSnapshot_unchanged_precise)
      next
        case (endAtomic C s ls f ls' t)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (dbop C s ls f Op args ls' t c res vis)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invocId C s procName args initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (fail C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      qed
    qed
  qed

  thus "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed

find_theorems state_wellFormed

lemma wf_transaction_status_iff_origin:
  assumes wf: "state_wellFormed S"
  shows "(transactionStatus S t = None) \<longleftrightarrow> (transactionOrigin S t = None)"
  using wf apply (induct  rule: wellFormed_induct)
  by (auto simp add: initialState_def step.simps split: if_splits)

lemma wf_transaction_status_iff_origin_dom:
  assumes wf: "state_wellFormed S"
  shows "dom (transactionOrigin S) = dom (transactionStatus S)"
  by (smt Collect_cong dom_def local.wf wf_transaction_status_iff_origin)


lemma remove_beginAtomic_step: 
  fixes S_start S_end :: "('ls,'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ABeginAtomic t txns)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and newCalls_def: "newCalls = callsInTransaction C newTxns \<down> happensBefore C"
    and snapshot_def: "snapshot = vis \<union> newCalls"
    and S_end'_def: "S_end' = S_end\<lparr>
                localState := (localState S_end)(i := localState S_start i), 
                currentTransaction := (currentTransaction S_end)(i := None),
                transactionStatus := (transactionStatus S_end)(t := None),
                transactionOrigin := (transactionOrigin S_end)(t := None),
                visibleCalls := (visibleCalls S_end)(i := visibleCalls S_start i)
      \<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -
  define T where 
    "T \<equiv> \<lambda>S::('ls,'any) state. S\<lparr>
                localState := (localState S)(i := localState S_start i), 
                currentTransaction := (currentTransaction S)(i := None),
                transactionStatus := (transactionStatus S)(t := None),
                transactionOrigin := (transactionOrigin S)(t := None),
                visibleCalls := (visibleCalls S)(i := visibleCalls S_start i) \<rparr>"



  have noOrig: "transactionOrigin S_start t = None"
    using step_a local.wf wf_transaction_status_iff_origin by (auto simp add: a_def step_simps)


  hence "T S_mid = S_start"
    using step_a by (auto simp add: a_def step_simps T_def state_ext)

  define P where
    p_def: "P \<equiv> \<lambda>S::('ls,'any) state. t \<notin> committedTransactions S \<and> (\<forall>i'. i' \<noteq> i \<longrightarrow>  currentTransaction S i' \<noteq> Some t)"

  have "currentTransaction S_start i \<noteq> Some t" for i
    by (metis local.wf noOrig option.simps(3) wellFormed_currentTransactionUncommitted wf_transaction_status_iff_origin)

  hence "P S_mid"
    using step_a
    by (auto simp add: p_def step.simps precondition_beginAtomic a_def  split: if_splits)




  from `S_mid ~~ tr \<leadsto>* S_end` 
  have t_not_used1: "(i, ABeginAtomic t txns) \<notin> set tr" for i txns
    using a_def no_i steps transactionIdsUnique2 by fastforce


  thm show_state_transfer

  from steps_tr
  have "(T S_mid ~~ tr \<leadsto>* T S_end) \<and> P S_end"
  proof (rule show_state_transfer)

    show "P S_mid"
      using `P S_mid` .

    show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> P S'"
      using no_i by (auto simp add: step.simps p_def t_not_used1  split: if_splits)

    have "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  a_step: "S ~~ (i',a) \<leadsto> S'" and P_S: "P S" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using `(i',a) \<in> set tr` no_i by force 
      hence [simp]: "i \<noteq> i'" by blast 

      from `S ~~ (i',a) \<leadsto> S'` 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace t_not_used1 by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
        then show ?case 
          using in_trace t_not_used1 apply (auto simp add: step_simps T_def state_ext elim!: chooseSnapshot_unchanged_precise)
          using p_def `P S` by auto
      next
        case (endAtomic C s ls f ls' t)
        then show ?case 
          using t_not_used1 `P S`
          apply (auto simp add: step_simps T_def state_ext p_def)
          by fastforce
      next
        case (dbop C s ls f Op args ls' t c res vis)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invocId C s procName args initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (fail C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        have  "invContextH (callOrigin C) ((transactionOrigin C)(t := None)) ((transactionStatus C)(t := None)) (happensBefore C) (calls C) (knownIds C) (invocationOp C)
               (invocationRes C) 
          = invContext C "
          using P_S `S = C`
          by (auto simp add: invContextH_def restrict_map_def p_def committedCallsH_def  isCommittedH_def restrict_relation_def intro!: ext split: if_splits)


        with invCheck
        show ?case 
          using t_not_used1 P_S p_def by (auto simp add: step_simps T_def )
      qed
    qed
    thus "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
      by force
  qed

  thus "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed


lemma callIds_unique:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "calls S cId \<noteq> None"
  shows "(s, ADbOp cId Op args res) \<notin> set tr" and "calls S' cId \<noteq> None"
using steps proof (induct rule: steps_induct)
  case initial
  thus "calls S cId \<noteq> None" using `calls S cId \<noteq> None` .
  show "(s, ADbOp cId Op args res) \<notin> set []" by simp
next
  case (step S' tr a S'')
  from step
  show "(s, ADbOp cId Op args res) \<notin> set (tr @ [a])" and "calls S'' cId \<noteq> None"
    by (auto simp add: step.simps)
qed

lemma callIds_unique2:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "tr ! i = (s, ADbOp cId Op args res)"
    and "i<j"
    and "j < length tr"
  shows  "tr ! j  \<noteq> (s', ADbOp cId Op' args' res')"
  using assms 
proof -
  have "tr = take (Suc i) tr @ drop (Suc i) tr"
    by simp
  from this
  obtain Si 
    where "S ~~ take (Suc i) tr \<leadsto>* Si"
      and "Si ~~ drop (Suc i) tr \<leadsto>* S'"
    using steps steps_append by fastforce
  from `S ~~ take (Suc i) tr \<leadsto>* Si`
  obtain Si_pre where "Si_pre ~~ (s, ADbOp cId Op args res) \<leadsto> Si"
    by (smt Suc_less_eq append1_eq_conv append_is_Nil_conv assms(2) assms(3) assms(4) length_Cons less_SucI less_trans_Suc n_not_Suc_n steps.cases take_Suc_conv_app_nth)

  hence "calls Si cId \<noteq> None"
    by (auto simp add: step_simps)
  with callIds_unique[OF `Si ~~ drop (Suc i) tr \<leadsto>* S'`]
  have "(s', ADbOp cId Op' args' res') \<notin> set (drop (Suc i) tr)"
    by blast
  thus "tr ! j  \<noteq> (s', ADbOp cId Op' args' res')"
    by (smt Suc_leI \<open>tr = take (Suc i) tr @ drop (Suc i) tr\<close> assms(3) assms(4) in_set_conv_nth le_add_diff_inverse2 length_drop length_take less_diff_conv min_def min_less_iff_conj not_less_eq nth_append)
    
qed

lemma chooseSnapshot_committed:
  assumes a1: "chooseSnapshot snapshot vis S"
    and a2: "c \<in> snapshot"
    and a3: "callOrigin S c \<triangleq> tx"
    and a5: "\<forall>x. (c, x) \<notin> happensBefore S"
    and a2': "c \<notin> vis"
  shows "transactionStatus S tx \<triangleq> Committed"
  using a1 a2 a2' a3 apply (auto simp add: chooseSnapshot_def)
  apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
  using a5 by blast



\<comment> \<open>  TODO  \<close>
lemma remove_DBOp_step: 
  fixes S_start S_end :: "('ls,'any::valueType) state" 
  assumes steps: "S_start ~~ (a#tr) \<leadsto>* S_end"
    and step_a: "S_start ~~ a \<leadsto> S_mid"
    and steps_tr: "S_mid ~~ tr \<leadsto>* S_end"
    and a_def: "a = (i, ADbOp cId operation args res)"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and wf: "state_wellFormed S_start"
    and S_end'_def: "S_end' = S_end\<lparr>
                localState := (localState S_end)(i := localState S_start i), 
                calls := (calls S_end)(cId := None),
                callOrigin := (callOrigin S_end)(cId := None),
                visibleCalls := (visibleCalls S_end)(i := visibleCalls S_start i),
                happensBefore := happensBefore S_end - {cId} \<times> UNIV - UNIV \<times> {cId}
(*
                localState := (localState S_end)(i := localState S_start i), 
                currentTransaction := (currentTransaction S_end)(i := None),
                transactionStatus := (transactionStatus S_end)(t := None),
                transactionOrigin := (transactionOrigin S_end)(t := None),
                visibleCalls := (visibleCalls S_end)(i := visibleCalls S_start i)
*)
      \<rparr>"
  shows "S_start ~~ tr \<leadsto>* S_end'"
proof -

  obtain start_txn where "currentTransaction S_start i \<triangleq> start_txn"
    using step_a a_def by (auto simp add: step_simps)

  have calls_S_start_cId: "calls S_start cId = None"
    using a_def preconditionI precondition_dbop step_a by fastforce

  find_theorems calls happensBefore state_wellFormed

  with wellFormed_visibleCallsSubsetCalls_h(1)[OF wf]
  have hb1: "(c, cId) \<notin> happensBefore S_start" for c
    by blast

  from calls_S_start_cId wellFormed_visibleCallsSubsetCalls_h(1)[OF wf]
  have hb2: "(cId, c) \<notin> happensBefore S_start" for c
    by blast

  from calls_S_start_cId
  have callOrigin_S_start_cId: "callOrigin S_start cId = None"
    by (simp add: local.wf)



  define T where 
    "T \<equiv> \<lambda>S::('ls,'any) state. S\<lparr>
                localState := (localState S)(i := localState S_start i), 
                calls := (calls S)(cId := None),
                callOrigin := (callOrigin S)(cId := None),
                visibleCalls := (visibleCalls S)(i := visibleCalls S_start i),
                happensBefore := happensBefore S - {cId} \<times> UNIV - UNIV \<times> {cId}
    \<rparr>"




  hence "T S_mid = S_start"
    using step_a apply (auto simp add: a_def step_simps T_def )
    apply (subst state_ext)
    apply (intro conjI)
    using hb1 hb2 callOrigin_S_start_cId by auto



  define P where
    p_def: "P \<equiv> \<lambda>S::('ls,'any) state. 
                     callOrigin S cId \<triangleq> start_txn 
                   \<and> transactionStatus S start_txn \<triangleq> Uncommitted
                   \<and> (\<forall>i'. i\<noteq>i' \<longrightarrow> currentTransaction S i' \<noteq> Some start_txn)
                   \<and> (\<forall>x. (cId, x) \<notin> happensBefore S)
                   \<and> (\<forall>i' vis. i\<noteq>i' \<and> visibleCalls S i' \<triangleq> vis \<longrightarrow> cId \<notin> vis)"


  have cId_not_used_again: "(s, ADbOp cId Op args res) \<notin> set tr" for s Op args res
    using callIds_unique2[OF steps, where i=0] apply (simp add: a_def)
    by (metis One_nat_def Suc_mono diff_Suc_1 in_set_conv_nth zero_less_Suc)



  from steps_tr
  have "(T S_mid ~~ tr \<leadsto>* T S_end) \<and> P S_end"
  proof (rule show_state_transfer)

    from step_a
    show "P S_mid"
      using \<open>currentTransaction S_start i \<triangleq> start_txn\<close> local.wf wellFormed_currentTransactionUncommitted apply (auto simp add: p_def step_simps a_def )
      using wellFormed_currentTransaction_unique apply blast
      using hb2 apply blast
      using wellFormed_visibleCallsSubsetCalls2 apply blast
      using wellFormed_visibleCallsSubsetCalls2 by blast



      

    have cId_not_in_calls: "cId \<notin> callsInTransaction S newTxns \<down> happensBefore S" if "newTxns \<subseteq> committedTransactions S" and "P S" for S newTxns
      using that  by (auto simp add: p_def callsInTransactionH_contains downwardsClosure_in)


    show "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> P S'"
      using no_i cId_not_used_again 
      by (auto simp add: step.simps p_def cId_not_in_calls chooseSnapshot_committed  split: if_splits, fastforce+)

    have "T S ~~ (i',a) \<leadsto> T S'" if in_trace: "(i',a) \<in> set tr" and  a_step: "S ~~ (i',a) \<leadsto> S'" and P_S: "P S" for i' a S S'
    proof -

      have [simp]: "i' \<noteq> i" using `(i',a) \<in> set tr` no_i by force 
      hence [simp]: "i \<noteq> i'" by blast 

      from `S ~~ (i',a) \<leadsto> S'` 
      show "T S ~~ (i',a) \<leadsto> T S'"
      proof (induct rule: step.cases)
        case (local C s ls f ls')
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (newId C s ls f ls' uid)
        then show ?case 
          using in_trace  by (auto simp add: step_simps T_def state_ext)
      next
        case (beginAtomic C s ls f ls' t vis snapshot)
(*
        have callsInTransactions_same: 
             "x \<in> callsInTransactionH ((callOrigin C)(cId := None)) newTxns \<down> (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId})
         \<longleftrightarrow>  x \<in> callsInTransaction C newTxns \<down> happensBefore C" (is "?left \<longleftrightarrow> ?right")  for x
        proof (rule iffI)
          show "?right" if ?left
            using  that by (auto simp add: callsInTransactionH_def downwardsClosure_def split: if_splits)

          show ?left if inOld: ?right
          proof -
            {
              fix txn
              assume a1: "txn \<in> newTxns" 
                and a2: "callOrigin C x \<triangleq> txn"

              hence ?left
                apply  (auto simp add: callsInTransactionH_def downwardsClosure_def split: if_splits)
                using P_S ` newTxns \<subseteq> committedTransactions C` `S = C` p_def by auto 
            }
            moreover
            {
              fix y txn
              assume a1: "(x, y) \<in> happensBefore C"
                and a2: "txn \<in> newTxns"
                and a3: "callOrigin C y \<triangleq> txn"

              have "y \<noteq> cId"
              proof 
                assume "y = cId"
                with `callOrigin C y \<triangleq> txn` 
                have "txn = start_txn"
                  using P_S `S = C` p_def by auto

                moreover have "transactionStatus C txn \<triangleq> Uncommitted"
                  using P_S `S = C` calculation p_def by blast

                with `txn \<in> newTxns` `newTxns \<subseteq> committedTransactions C`
                show False
                  by auto
              qed

              have "x \<noteq> cId"
                using `x \<in> callsInTransaction C newTxns \<down> happensBefore C`
                apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
                using P_S beginAtomic.hyps(1) beginAtomic.hyps(10) p_def wellFormed_currentTransaction_unique_h(2) apply auto[1]
                using P_S beginAtomic.hyps(1) p_def by blast

              have ?left
                apply (auto simp add: callsInTransactionH_def downwardsClosure_def `x \<noteq> cId`)
                using \<open>y \<noteq> cId\<close> a1 a2 a3 by blast
            }
            ultimately show ?left
              using inOld apply (auto simp add: callsInTransactionH_def downwardsClosure_def)
              by fastforce+
          qed
        qed
*)
        define C' where "C' \<equiv> C\<lparr>
            calls := (calls C)(cId := None), 
            happensBefore := happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId},
            localState := (localState C)(i := localState S_start i),
            visibleCalls := (visibleCalls C)(i := visibleCalls S_start i),
            callOrigin := (callOrigin C)(cId := None)\<rparr>"

        from beginAtomic show ?case 
          apply (auto simp add: step.simps T_def  state_ext intro!: ext)

          apply (rule_tac x=C' in exI)
          apply (auto simp add: C'_def)
          apply (rule chooseSnapshot_unchanged_precise)
          apply assumption
            using P_S p_def by (auto )





      next
        case (endAtomic C s ls f ls' t)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (dbop C s ls f Op args ls' t c res vis)

        have [simp]: "cId \<notin> vis "
          using P_S \<open>i' \<noteq> i\<close> dbop.hyps(1) dbop.hyps(10) dbop.hyps(2) p_def by fastforce


        have sameContext:
             "(getContextH (calls C) (happensBefore C) (Some vis)) 
            = (getContextH ((calls C)(cId := None)) (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId}) (Some vis))"
          by (auto simp add: getContextH_def restrict_map_def restrict_relation_def)
        
        from dbop
        show ?case using cId_not_used_again in_trace by (auto simp add: step_simps T_def state_ext sameContext)

      next
        case (invocId C s procName args initialState impl)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (return C s ls f res)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (fail C s ls)
        then show ?case by (auto simp add: step_simps T_def state_ext)
      next
        case (invCheck C res s)
        have [simp]: "\<not>isCommitted C cId"
          using P_S committedCalls_uncommittedNotIn invCheck.hyps(1) p_def
          by (simp add: isCommittedH_def) 
        have [simp]: "cId \<notin> committedCalls C"
          using P_S committedCalls_uncommittedNotIn invCheck.hyps(1) p_def by blast

        have [simp]: "isCommittedH ((callOrigin C)(cId := None)) (transactionStatus C) x
                  \<longleftrightarrow> isCommittedH (callOrigin C) (transactionStatus C) x"  for x
          apply (auto simp add: isCommittedH_def )
          by (meson \<open>\<not> isCommitted C cId\<close> isCommittedH_def)


        have  "(invContextH ((callOrigin C)(cId := None)) (transactionOrigin C) (transactionStatus C) (happensBefore C - {cId} \<times> UNIV - UNIV \<times> {cId}) ((calls C)(cId := None))
           (knownIds C) (invocationOp C) (invocationRes C)
           )
          = invContext C"
          using P_S `S = C`
          by (auto simp add: p_def invContextH_def restrict_map_def committedCallsH_def restrict_relation_def downwardsClosure_def callsInTransactionH_def intro!: ext)


        with invCheck
        show ?case 
          using P_S p_def by (auto simp add: step_simps T_def )
      qed
    qed
    thus "\<And>a S S'. \<lbrakk>a \<in> set tr; S ~~ a \<leadsto> S'; P S\<rbrakk> \<Longrightarrow> T S ~~ a \<leadsto> T S'"
      by force
  qed

  thus "S_start ~~ tr \<leadsto>* S_end'"
    using S_end'_def T_def \<open>T S_mid = S_start\<close> by (auto simp add: )

qed



lemma transfer_execution_local_difference:
  assumes steps: "S1 ~~ tr \<leadsto>* S1'"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and S2_def: "S2 = S1\<lparr>localState := (localState S1)(i := ls),
      currentTransaction := (currentTransaction S1)(i := tx)\<rparr>"
    and S2'_def: "S2' = S1'\<lparr>localState := (localState S1')(i := ls),
      currentTransaction := (currentTransaction S1')(i := tx)\<rparr>"
  shows "S2 ~~ tr \<leadsto>* S2'"
  using steps no_i S2'_def proof (induct arbitrary: S2' rule: steps_induct)
  case initial
  then show ?case
    using steps_refl S2_def by blast 
next
  case (step S' tr a S'')

  define S_mid where "S_mid \<equiv> S'\<lparr>localState := (localState S')(i := ls), currentTransaction := (currentTransaction S')(i := tx)\<rparr>"

  have "S2 ~~ tr \<leadsto>* S_mid"
  proof (rule step.IH)
    show "\<And>a. a \<in> set tr \<Longrightarrow> fst a \<noteq> i"
      using step.prems(1) by auto
    show " S_mid = S'\<lparr>localState := (localState S')(i := ls), currentTransaction := (currentTransaction S')(i := tx)\<rparr>"
      by (simp add: S_mid_def)
  qed

  have [simp]: "fst a \<noteq> i" 
    by (auto simp add: step.prems(1))
  hence [simp]: "i\<noteq>fst a"
    by blast


  from `S' ~~ a \<leadsto> S''`
  have "S_mid ~~ a \<leadsto> S2'"
  proof (induct rule: step.cases)
    case (local C s ls f ls')
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (newId C s ls f ls' uid)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (beginAtomic C s ls f ls' t vis snapshot)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits elim: chooseSnapshot_unchanged)
      done
  next
    case (endAtomic C s ls f ls' t)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (dbop C s ls f Op args ls' t c res vis)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (invocId C s procName args initialState impl)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (return C s ls f res)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (fail C s ls)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  next
    case (invCheck C res s)
    then show ?case 
      using `fst a \<noteq> i` apply (auto simp add: step_simps S_mid_def)
       apply (subst state_ext)
       apply (auto simp add: step  split: if_splits)
      apply (subst state_ext)
      apply (auto simp add: step  split: if_splits)
      done
  qed
  thus "S2 ~~ tr @ [a] \<leadsto>* S2'"
    using \<open>S2 ~~ tr \<leadsto>* S_mid\<close> steps_step by blast

qed


lemma transfer_execution_local_difference':
  assumes steps: "S1 ~~ tr \<leadsto>* S1'"
    and no_i: "\<And>a. a\<in>set tr \<Longrightarrow> fst a \<noteq> i"
    and S2_def: "\<exists>ls tx. S2 = S1\<lparr>localState := (localState S1)(i := ls),
      currentTransaction := (currentTransaction S1)(i := tx)\<rparr>"
  shows "\<exists>S2'. S2 ~~ tr \<leadsto>* S2'"
  using transfer_execution_local_difference[OF steps no_i]
  using S2_def by blast


definition no_invariant_checks_in_transaction where
"no_invariant_checks_in_transaction tr \<equiv> \<forall>ib i s c tx txns. 
    tr!ib = (s, ABeginAtomic tx txns)
  \<and> ib < i
  \<and> i < length tr 
  \<and> (\<forall>j. ib<j \<and> j<i \<longrightarrow> tr!j \<noteq> (s, AEndAtomic))
  \<longrightarrow> tr!i \<noteq> (s, AInvcheck c) "

lemma show_no_invariant_checks_in_transaction[case_names hasEndatomic[invcheck beginatomic beginBefore lessLength]]:
  assumes "\<And>i s tx txns c ib. \<lbrakk>tr!i = (s, AInvcheck c); tr!ib = (s, ABeginAtomic tx txns); ib < i; i<length tr\<rbrakk>
            \<Longrightarrow> \<exists>j. ib<j \<and> j<i \<and> tr!j = (s, AEndAtomic)"
  shows "no_invariant_checks_in_transaction tr"
  using assms by (auto simp add: no_invariant_checks_in_transaction_def, blast)

lemma use_no_invariant_checks_in_transaction:
  assumes "no_invariant_checks_in_transaction tr"
    and "tr!i = (s, AInvcheck c)"
    and "tr!ib = (s, ABeginAtomic tx txns)"
    and "ib < i"
    and "i < length tr"
  shows "\<exists>j. ib<j \<and> j<i \<and> tr!j = (s, AEndAtomic)"
  using assms by (auto simp add: no_invariant_checks_in_transaction_def, blast)

lemma set_nth_transfer:
  assumes "xs!i = x"
and "i< length xs"
and "set xs \<subseteq> set xs'"
shows "\<exists>i'. i' < length xs' \<and> xs'!i' = x"
  using assms apply auto
  by (meson in_set_conv_nth subset_h1)

lemma nth_drop_if: 
"drop n xs ! i = (if n \<le> length xs then xs ! (n + i) else [] ! i)"
  by auto

lemma maintain_no_invariant_checks_in_transaction:
  assumes "no_invariant_checks_in_transaction tr"
    and "snd (tr!pos) \<noteq> AEndAtomic"
    and "pos < length tr"
  shows "no_invariant_checks_in_transaction (take pos tr @ drop (Suc pos) tr)"
proof (rule show_no_invariant_checks_in_transaction)
  fix i s tx txns c ib
  assume a1: "(take pos tr @ drop (Suc pos) tr) ! i = (s, AInvcheck c)"
    and  a2: "(take pos tr @ drop (Suc pos) tr) ! ib = (s, ABeginAtomic tx txns)"
    and a3: "ib < i"
    and a4: "i < length (take pos tr @ drop (Suc pos) tr)"

  define i' where "i' \<equiv> if i < pos then i else Suc i"
  define ib' where "ib' \<equiv> if ib < pos then ib else Suc ib"

  have a1': "tr!i' = (s, AInvcheck c)" 
    using a1 i'_def `pos < length tr` a4 by (auto simp add: nth_append min_def split: if_splits)

  have a2': "tr!ib' = (s, ABeginAtomic tx txns)" 
    using a2 ib'_def `pos < length tr` a3 a4 by (auto simp add: nth_append min_def split: if_splits)
  have a3':"ib'<i'"
    using a3 i'_def ib'_def by auto
  have a4':"i'<length tr"
    using a4 i'_def by auto

  with use_no_invariant_checks_in_transaction[OF `no_invariant_checks_in_transaction tr` a1' a2' a3' a4']
  obtain j where "j>ib'" and "j < i'" and  "tr ! j = (s, AEndAtomic)"
    by auto

  thus  "\<exists>j>ib. j < i \<and> (take pos tr @ drop (Suc pos) tr) ! j = (s, AEndAtomic)"
  proof (cases "j < pos")
    case True
    show ?thesis 
      apply (rule exI[where x=j])
      apply auto
      apply (metis Suc_lessD \<open>ib' < j\<close> ib'_def)
      apply (metis True \<open>j < i'\<close> i'_def less_SucE)
      by (simp add: True \<open>tr ! j = (s, AEndAtomic)\<close> assms(3) less_imp_le min.absorb2 nth_append_first)
  next
    case False
    show ?thesis 
      apply (rule exI[where x="j - 1"])
      using `j>ib'` `j < i'` False apply (auto simp add: ib'_def i'_def split: if_splits)
        apply (auto simp add: nth_append)
           apply (metis Suc_pred \<open>ib' < j\<close> \<open>tr ! j = (s, AEndAtomic)\<close> assms(2) ib'_def less_Suc_eq_0_disj linorder_neqE_nat not_less_eq snd_conv)
          apply (metis Suc_pred \<open>tr ! j = (s, AEndAtomic)\<close> assms(2) linorder_neqE_nat not_less_eq snd_conv zero_less_Suc)
      using \<open>j < i'\<close> a4' less_imp_diff_less less_trans apply blast
      using Suc_leI assms(3)  by (auto simp add: \<open>tr ! j = (s, AEndAtomic)\<close> min.absorb2)
  qed
qed


definition
"isNoInvCheck a \<equiv> case a of (s, AInvcheck txns) \<Rightarrow> False | _ \<Rightarrow> True"

definition 
"removeInvChecks \<equiv> filter isNoInvCheck"


lemma removeInvChecks_same:
  assumes "S ~~ trace \<leadsto>* S'"
shows "S ~~ removeInvChecks trace \<leadsto>* S'"
using assms proof (induct rule: steps_induct)
  case initial
  then show ?case  by (auto simp add: removeInvChecks_def )
next
  case (step S' tr a S'')
  then show ?case 
    by (auto simp add: removeInvChecks_def isNoInvCheck_def steps_append step_simps split: action.splits)
qed

(*
lemma packed_trace_removeInvChecks:
  assumes "packed_trace trace"
   shows "packed_trace (removeInvChecks trace)"
proof (auto simp add: packed_trace_def)
  fix i
  assume a1: "0 < i"
    and "i < length (removeInvChecks trace)"
    and "fst (removeInvChecks trace ! (i - Suc 0)) \<noteq> fst (removeInvChecks trace ! i)"

(* get corresponding indexes in trace 
then get allowed from there
*)

  show "allowed_context_switch (snd (removeInvChecks trace ! i))"
qed
*)

lemma removeInvChecks_no_invcheck:
  assumes "ia < length (removeInvChecks trace)"
  shows "removeInvChecks trace ! ia \<noteq> (s, AInvcheck c)"
proof 
  assume "removeInvChecks trace ! ia = (s, AInvcheck c)"
  hence " (s, AInvcheck c) \<in> set (removeInvChecks trace)"
    using assms
    using nth_mem by force 
  thus False
    by (auto simp add: removeInvChecks_def  isNoInvCheck_def)
qed


text {*
 To show that a program is correct, we only have to consider packed transactions 
 with no invariant checks 
*}
theorem show_programCorrect_noTransactionInterleaving_no_passing_invchecks:
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; \<And>s. (s, AInvcheck True) \<notin> set trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving)
  fix trace :: "(invocId \<times> 'a action) list"
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"

  show "traceCorrect trace"
  proof (rule ccontr)
    assume a: "\<not> traceCorrect trace"

    define isNotTrueInvcheck :: "(invocId \<times> 'a action) \<Rightarrow> bool"
      where "isNotTrueInvcheck \<equiv> (\<lambda>a. case a of (s, AInvcheck True) \<Rightarrow> False | _\<Rightarrow> True)"
    define trace' where "trace' \<equiv> filter isNotTrueInvcheck trace"

    have isNotTrueInvcheck_simps: "isNotTrueInvcheck a \<longleftrightarrow> \<not>(\<exists>s. a = (s, AInvcheck True))" for a
      by (auto simp add: isNotTrueInvcheck_def split: prod.splits action.splits)

    have "traceCorrect trace'"
    proof (rule packedTracesCorrect)
      from steps
      show "initialState program ~~ trace' \<leadsto>* S"
        apply (auto simp add: trace'_def)
      proof (induct rule: steps_induct)
        case initial
        then show ?case  by (auto simp add:  )
      next
        case (step S' tr a S'')
        show ?case 
        proof auto
          assume  "isNotTrueInvcheck a"
          thus "initialState program ~~ filter isNotTrueInvcheck tr @ [a] \<leadsto>* S''"
            using step.IH step.step steps_step by blast
        next 
          assume "\<not> isNotTrueInvcheck a"
          hence "S' = S''"
            using `S' ~~ a \<leadsto> S''`
            by (auto simp add: isNotTrueInvcheck_def step.simps split: bool.splits)
          thus "initialState program ~~ filter isNotTrueInvcheck tr  \<leadsto>* S''"
            using step.IH by blast
        qed
      qed

      from packed 
      have "packed_trace (filter isNotTrueInvcheck trace) 
       \<and> (filter isNotTrueInvcheck trace \<noteq> [] \<longrightarrow> fst (last (filter isNotTrueInvcheck trace)) = fst (last trace))"
      proof (induct trace arbitrary: trace' rule: rev_induct)
        case Nil
        then show ?case by simp
      next
        case (snoc x xs)
        hence IH1: "packed_trace (filter isNotTrueInvcheck xs)"
          and IH2: "(filter isNotTrueInvcheck xs \<noteq> [] \<Longrightarrow> fst (last (filter isNotTrueInvcheck xs)) = fst (last xs))"
          using isPrefix_appendI prefixes_are_packed by blast+


        show ?case 
        proof (cases "filter isNotTrueInvcheck xs = []")
          case True
          then show ?thesis 
            by (auto simp add:  packed_trace_def nth_append)
        next
          case False
          hence "fst (last (filter isNotTrueInvcheck xs)) = fst (last xs)"
            using IH2 by blast
          then show ?thesis 
            apply (auto simp add:  packed_trace_def nth_append )
            apply (simp add: IH1 use_packed_trace)
            apply (metis (no_types, lifting) False One_nat_def butlast_snoc diff_Suc_less filter.simps(1) last_conv_nth length_append_singleton length_greater_0_conv lessI less_SucE nth_append_length nth_butlast snoc.prems use_packed_trace)
             apply (simp add: IH1 use_packed_trace)
            apply (auto simp add: isNotTrueInvcheck_simps)
            by (metis (no_types, lifting) One_nat_def allowed_context_switch_simps(9) butlast_snoc diff_Suc_less filter.simps(1) fst_conv last_conv_nth length_append_singleton length_greater_0_conv lessI nth_append_length nth_butlast snd_conv snoc.prems use_packed_trace)
        qed
      qed

      thus "packed_trace trace'"
        unfolding trace'_def by simp
        
      show " \<And>s. (s, AFail) \<notin> set trace'"
        by (auto simp add: trace'_def nofail)

      show "\<And>s. (s, AInvcheck True) \<notin> set trace'"
        by  (auto simp add: trace'_def isNotTrueInvcheck_def)
    qed
    hence "traceCorrect trace"
      by (auto simp add: trace'_def traceCorrect_def isNotTrueInvcheck_def)

    thus "False"
      using a by blast
  qed
qed

lemma move_invariant_checks_out_of_transactions:
  assumes "initialState program ~~ trace \<leadsto>* S"
    and "packed_trace trace"
    and "\<And>s. (s, AFail) \<notin> set trace"
    and "\<And>s. (s, AInvcheck True) \<notin> set trace"
    and "last trace = (s, AInvcheck False)"
    and "length trace > 0"
    and "\<And>i s'. i<length trace - 1 \<Longrightarrow> trace!i \<noteq> (s', AInvcheck False)"
  shows "\<exists>trace' s'. 
          (\<exists>S'. initialState program ~~ trace' \<leadsto>* S')
        \<and> packed_trace trace'
        \<and> (\<forall>s. (s, AFail) \<notin> set trace')
        \<and> (\<forall>s. (s, AInvcheck True) \<notin> set trace')
        \<and> (last trace' = (s', AInvcheck False))
        \<and> length trace' > 0
        \<and> (no_invariant_checks_in_transaction trace')"
  using assms proof (induct "length trace" arbitrary: trace s S rule: less_induct)
  case (less trace s S)
  show ?case 
  proof (cases "no_invariant_checks_in_transaction trace")
    case True
    then show ?thesis 
      using less.prems by auto
  next
    case False

    from this obtain ib i s' tx ib_txns c 
      where ib1: "trace ! ib = (s', ABeginAtomic tx ib_txns)"
        and ib2: "ib < i"
        and "i < length trace"
        and noEndAtomic1: "\<forall>j. ib < j \<and> j < i \<longrightarrow> trace ! j \<noteq> (s', AEndAtomic)"
        and "trace ! i = (s', AInvcheck c)"
      by (auto simp add: no_invariant_checks_in_transaction_def)
    hence i_def: "i = length trace - 1" 
      by (smt One_nat_def Suc_pred less.prems(4) less.prems(6) less.prems(7) less_Suc_eq nth_mem)

    have [simp]: "s' = s" 
      using \<open>trace ! i = (s', AInvcheck c)\<close> i_def last_conv_nth less.prems by (auto simp add: last_conv_nth)



    have ib2: "ib < length trace - 1"
      using i_def ib2 by blast
    from noEndAtomic1
    have noEndAtomic: "trace ! j \<noteq> (s, AEndAtomic)" if "ib\<le>j" and "j<length trace" for j
      using that
      by (metis One_nat_def Pair_inject Suc_pred \<open>s' = s\<close> \<open>trace ! i = (s', AInvcheck c)\<close> action.distinct(31) action.distinct(51) i_def ib1 le_eq_less_or_eq less.prems(6) less_antisym)


    (* Let action a be the action before the invariant check.
     Get the state before and show that we can execute the invariant before that as well
     Then use IH.  *)

    have "xs = ys" if "\<And>i. i<length xs \<Longrightarrow> xs!i = ys!i" and "length xs = length ys" for xs ys
      using nth_equalityI that(1) that(2) by blast


    have "length trace \<ge> 2"
      using ib2 by linarith



    have trace_split: "trace = take (length trace - 2) trace @ [trace!(length trace -2), last trace]"
      apply (rule nth_equalityI)
      using `length trace \<ge> 2` apply (auto simp add: min_def nth_append nth_Cons')
      apply (smt Suc_le_lessD Suc_less_eq Suc_pred \<open>2 \<le> length trace\<close> diff_Suc_Suc less.prems(6) not_less_less_Suc_eq numeral_2_eq_2)
      by (metis Suc_leI Suc_lessI diff_Suc_1 last_conv_nth less.prems(6) list.size(3))

    from `initialState program ~~ trace \<leadsto>* S` 
    obtain S1 S2
      where steps_S1: "initialState program ~~ take (length trace - 2) trace \<leadsto>* S1"
        and step_S2: "S1 ~~ trace!(length trace -2) \<leadsto> S2"
        and step_inv: "S2 ~~ last trace \<leadsto> S"
      by (metis (no_types, lifting) butlast.simps(2) butlast_append butlast_snoc last_snoc less.prems(6) less_numeral_extra(3) list.simps(3) list.size(3) steps.cases steps_appendBack trace_split)

    thm less

    from step_inv 
    have step_inv': "S2 ~~ (s, AInvcheck False) \<leadsto> S"
      by (auto simp add: `last trace = (s, AInvcheck False)`)

    have invariant_fail_S2[simp]: "\<not> invariant (prog S2) (invContext S2)"
      using step_elim_AInvcheck step_inv' by blast

    have "fst (trace!(length trace -1)) = s"
      using \<open>trace ! i = (s', AInvcheck  c)\<close> i_def by auto

    with `packed_trace trace`
    have "fst (trace!(length trace -2)) = s" 
      apply (auto simp add: packed_trace_def allowed_context_switch_def)
      by (metis One_nat_def Suc_le_lessD \<open>2 \<le> length trace\<close> \<open>i < length trace\<close> \<open>trace ! i = (s', AInvcheck c)\<close> allowed_context_switch_simps(9) diff_Suc_eq_diff_pred i_def less.prems(2) numeral_2_eq_2 snd_conv use_packed_trace zero_less_diff)

    from this obtain action 
      where action_def: "trace!(length trace -2) = (s, action)"
      by (meson eq_fst_iff)
    with `S1 ~~ trace!(length trace -2) \<leadsto> S2`
    have "S1 ~~ (s, action) \<leadsto> S2"
      by simp


    have wf: "state_wellFormed S1"
      using state_wellFormed_combine state_wellFormed_init steps_S1
      by (metis contra_subsetD less.prems(3) set_take_subset) 



    show ?thesis
    proof (cases "ib < length trace - 2")
      case True
      hence [simp]: "ib < length trace - 2"
        by simp

      have currentTx: "currentTransaction S1 s \<triangleq> tx" 
      proof (rule currentTransaction2[OF steps_S1])

        show "take (length trace - 2) trace ! ib = (s, ABeginAtomic tx ib_txns)"
          using ib1 ib2  by auto

        show "ib < length (take (length trace - 2) trace)"
          using ib2 by auto
        show "\<And>j. \<lbrakk>ib < j; j < length (take (length trace - 2) trace)\<rbrakk> \<Longrightarrow> take (length trace - 2) trace ! j \<noteq> (s, AFail)"
          using less.prems(3) nth_mem by fastforce 
        show "\<And>j. \<lbrakk>ib < j; j < length (take (length trace - 2) trace)\<rbrakk> \<Longrightarrow> take (length trace - 2) trace ! j \<noteq> (s, AEndAtomic)"
          using noEndAtomic by auto
      qed

      with wf
      have ls_none: "localState S1 s \<noteq> None"
        using inTransaction_localState by blast 

      have "S1 ~~ (s, AInvcheck False) \<leadsto> S1"
      proof (cases action)
        case ALocal
        then show ?thesis
          using invariant_fail_S2 `S1 ~~ (s, action) \<leadsto> S2`  apply (auto simp add: step_simps)
          using step_elim_AInvcheck step_inv' by fastforce
      next
        case (ANewId x2)
        then show ?thesis
          using invariant_fail_S2 `S1 ~~ (s, action) \<leadsto> S2`  apply (auto simp add: step_simps)
          using invariant_fail_S2 by auto
      next
        case (ABeginAtomic x31 x32)
        then show ?thesis
          by (metis \<open>S1 ~~ (s, action) \<leadsto> S2\<close> \<open>currentTransaction S1 s \<triangleq> tx\<close> option.simps(3) preconditionI precondition_beginAtomic) 
      next
        case AEndAtomic
        then show ?thesis
          using action_def ib2 noEndAtomic by auto 
      next
        case (ADbOp cId proc args res)

        obtain tx where currentTransaction: "currentTransaction S1 s \<triangleq> tx"
          using `S1 ~~ (s, action) \<leadsto> S2` ADbOp
          apply (auto simp add:  step_simps)
          done
        hence uncommitted: "transactionStatus S1 tx \<triangleq> Uncommitted"
          using local.wf by auto

        have "calls S1 cId = None"
          using `S1 ~~ (s, action) \<leadsto> S2` ADbOp
          by (auto simp add:  step_simps)
        hence "callOrigin S1 cId = None"
          by (simp add: local.wf)


        have "committedCalls S2 = committedCalls S1" 
          using `S1 ~~ (s, action) \<leadsto> S2` ADbOp
          by (auto simp add:  step_simps ls_none committedCallsH_def isCommittedH_def currentTransaction uncommitted `callOrigin S1 cId = None` split: if_splits)

        have "invContext S2 = invContext S1 "
          apply (auto simp add: invContextH_def `committedCalls S2 = committedCalls S1`)
          using `S1 ~~ (s, action) \<leadsto> S2` ADbOp
                  apply (auto simp add: invContextH_def step_simps ls_none )
           using \<open>callOrigin S1 cId = None\<close> noOrigin_notCommitted  by (auto simp add: restrict_map_def restrict_relation_def )


         with invariant_fail_S2
         have "\<not> invariant (prog S1) (invContext S1)"
           using \<open>S1 ~~ (s, action) \<leadsto> S2\<close> prog_inv by force

         thus ?thesis 
          using invariant_fail_S2 ADbOp `S1 ~~ (s, action) \<leadsto> S2` by (auto simp add: step_simps ls_none)
      next
        case (AInvoc x61 x62)
        then show ?thesis 
          using invariant_fail_S2 `S1 ~~ (s, action) \<leadsto> S2`  by (auto simp add: step_simps ls_none)
      next
        case (AReturn x7)
        then show ?thesis 
          using invariant_fail_S2 `S1 ~~ (s, action) \<leadsto> S2`  by (auto simp add: step_simps ls_none currentTx)
      next
        case AFail
        then show ?thesis
          by (metis action_def diff_less less.prems(3) less.prems(6) nth_mem zero_less_numeral)
      next
        case (AInvcheck r)
        then show ?thesis 
          by (metis (full_types) Suc_1 Suc_diff_Suc Suc_le_lessD \<open>2 \<le> length trace\<close> action_def diff_less less.prems(4) less.prems(6) less.prems(7) lessI nth_mem zero_less_numeral)
      qed
      show ?thesis
      proof (rule less.hyps) \<comment> \<open>  USE induction hypothesis \<close>
        from `S1 ~~ (s, AInvcheck False) \<leadsto> S1`
        show " initialState program ~~ take (length trace - 2) trace @ [(s, AInvcheck False)] \<leadsto>* S1"
          using steps_S1 steps_step by blast

        have no_ctxt_switch: "\<not>allowed_context_switch (snd (trace!(length trace -2)))"
          using `S1 ~~ trace ! (length trace - 2) \<leadsto> S2`
          using action_def currentTx ls_none by (auto simp add: step.simps)

        show "packed_trace (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          apply (auto simp add: packed_trace_def nth_append min_def not_less)
           apply (simp add: less.prems(2) use_packed_trace)
          find_theorems "\<not> _ < _"
          apply (case_tac "i = length trace - 2")
           apply auto
          using `fst (trace!(length trace -2)) = s` 
          using use_packed_trace[OF `packed_trace trace`, where i="length trace - 2"]
          apply auto
          using no_ctxt_switch by linarith
        show "0 < length (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          by simp



        show "\<And>s'. (s', AInvcheck True) \<notin> set (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          apply auto
          by (meson in_set_takeD less.prems(4))

        show "\<And>s'. (s', AFail) \<notin> set (take (length trace - 2) trace @ [(s, AInvcheck False)])"
          apply auto
          by (meson in_set_takeD less.prems(3))

        show "last (take (length trace - 2) trace @ [(s, AInvcheck False)]) = (s, AInvcheck False)"
          by simp

        show "length (take (length trace - 2) trace @ [(s, AInvcheck False)]) < length trace"
          by (metis add_Suc_right length_Cons length_append lessI trace_split)
        show "\<And>i s'.
       i < length (take (length trace - 2) trace @ [(s, AInvcheck False)]) - 1 \<Longrightarrow>
       (take (length trace - 2) trace @ [(s, AInvcheck False)]) ! i \<noteq> (s', AInvcheck False)"
          by (auto simp add: nth_append less.prems)
      qed


    next
      case False
      hence "ib = length trace - 2"
        using ib2 by linarith
      hence "action = ABeginAtomic tx ib_txns"
        using action_def ib1 by auto
      with  `S1 ~~ (s, action) \<leadsto> S2`
      have "invContext S1 = invContext S2"
        using invariant_fail_S2 by (auto simp add: step_simps invContextH_def restrict_map_def)
      with `S1 ~~ (s, action) \<leadsto> S2` and `action = ABeginAtomic tx ib_txns`
      have "S1 ~~ (s', AInvcheck False) \<leadsto> S1" for s'
        apply (auto simp add: step_simps )
        using invariant_fail_S2 apply auto
        done

      define new_s where "new_s = fst(trace ! (length trace - 3))" 

      show ?thesis
      proof (rule less.hyps) \<comment> \<open>  USE induction hypothesis \<close>
        from `S1 ~~ (new_s, AInvcheck False) \<leadsto> S1`
        show " initialState program ~~ take (length trace - 2) trace @ [(new_s, AInvcheck False)] \<leadsto>* S1"
          using steps_S1 steps_step by blast


        show "packed_trace (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          apply (auto simp add: packed_trace_def nth_append min_def not_less new_s_def)
           apply (simp add: less.prems(2) use_packed_trace)
          by (metis One_nat_def diff_Suc_eq_diff_pred le_less_Suc_eq numeral_2_eq_2 numeral_3_eq_3)

        show "0 < length (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          by simp

        show "\<And>s'. (s', AInvcheck True) \<notin> set (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          apply auto
          by (meson in_set_takeD less.prems(4))

        show "\<And>s'. (s', AFail) \<notin> set (take (length trace - 2) trace @ [(new_s, AInvcheck False)])"
          apply auto
          by (meson in_set_takeD less.prems(3))

        show "last (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) = (new_s, AInvcheck False)"
          by simp

        show "length (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) < length trace"
          by (metis add_Suc_right length_Cons length_append lessI trace_split)
        show "\<And>i s'.
       i < length (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) - 1 \<Longrightarrow>
       (take (length trace - 2) trace @ [(new_s, AInvcheck False)]) ! i \<noteq> (s', AInvcheck False)"
          by (auto simp add: nth_append less.prems)
      qed
    qed
  qed
qed


text {*
 To show that a program is correct, we only have to consider packed transactions 
 with no invariant checks 
*}
theorem show_programCorrect_noTransactionInterleaving':
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving_no_passing_invchecks)
  fix trace :: "(invocId \<times> 'a action) list"
  fix S
  assume steps: "initialState program ~~ trace \<leadsto>* S"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"
    and noTrueInvs: "\<And>s. (s, AInvcheck True) \<notin> set trace"



  show "traceCorrect trace"
  proof (rule ccontr)
    assume a: "\<not> traceCorrect trace"

    \<comment> \<open>  get the first failing invariant check  \<close>
    obtain i 
      where i1: "\<exists>s. trace ! i = (s, AInvcheck False)"
        and i2: "i < length trace"
        and i_min: "\<forall>i'. (\<exists> s'. trace ! i' = (s', AInvcheck False)) \<and> i' < length trace \<longrightarrow> i\<le>i'"
      apply atomize_elim
      apply (rule_tac x="LEAST i'. (\<exists>s'. trace ! i' = (s', AInvcheck False)) \<and> i' < length trace" in exI)
      apply (rule LeastI2_wellorder_ex)
      using a by (auto simp add: traceCorrect_def in_set_conv_nth)

    from i1
    obtain s where i1': "trace ! i = (s, AInvcheck False)"
      by blast


    show "False"
    proof (cases "\<exists>ib \<comment> \<open> s \<close> tx txns. trace!ib = (s, ABeginAtomic tx txns) \<and> ib < i \<and> (\<forall>j. ib<j \<and> j<i \<longrightarrow> trace!j \<noteq> (s, AEndAtomic))")
      case False
        \<comment> \<open>  if it is not in a transaction: remove all others and use packedTracesCorrect   \<close>

      have trace_split: "trace = take i trace @ trace!i # drop (Suc i) trace"
        by (simp add: \<open>i < length trace\<close> id_take_nth_drop)

      define trace' where "trace' \<equiv> take (Suc i) trace"

      from steps 
      obtain Si where steps': "initialState program ~~ trace' \<leadsto>* Si"
        apply (auto simp add: trace'_def)
        by (metis append_take_drop_id steps_append)



      have "traceCorrect trace'"
      proof (rule packedTracesCorrect[OF steps'])
        show "packed_trace trace'"
          apply (auto simp add: trace'_def)
          by (metis append_take_drop_id isPrefix_appendI packed prefixes_are_packed)
        show "\<And>s. (s, AFail) \<notin> set trace'"
          using nofail  \<open>\<exists>s. trace ! i = (s, AInvcheck False)\<close> by (auto simp add: trace'_def removeInvChecks_def isNoInvCheck_def dest: in_set_takeD in_set_dropD)
        show "no_invariant_checks_in_transaction trace'"
        proof (induct rule: show_no_invariant_checks_in_transaction)
          case (hasEndatomic i' s2 tx txns c ib)
          from `trace' ! i' = (s2, AInvcheck c)`
          have "i' = i"
            apply (auto simp add: trace'_def nth_append removeInvChecks_no_invcheck nth_Cons' split: if_splits)
            by (smt Suc_leI append_take_drop_id hasEndatomic.lessLength i2 i_min le_less_Suc_eq length_take less_trans min.absorb2 noTrueInvs not_less_less_Suc_eq nth_append_first nth_mem trace'_def)


          from `trace' ! ib = (s2, ABeginAtomic tx txns)` `ib < i'`
          obtain ib' 
            where "trace' ! ib' = (s2, ABeginAtomic tx txns)"
              and "ib' < i"
            apply (auto simp add: trace'_def)
            by (simp add: \<open>i' = i\<close>)

          have "s2 = s"
            using \<open>i' = i\<close> hasEndatomic.invcheck i1' trace'_def by auto



          with `\<nexists>ib tx txns. trace ! ib = (s, ABeginAtomic tx txns) \<and> ib < i \<and> (\<forall>j. ib < j \<and> j < i \<longrightarrow> trace ! j \<noteq> (s, AEndAtomic))`
          show ?case 
            using \<open>i' = i\<close> `s2 = s`  hasEndatomic.beginBefore hasEndatomic.beginatomic trace'_def by force
        qed
      qed

      with i1'
      show ?thesis
        by (metis i2 length_take lessI min_less_iff_conj nth_mem nth_take trace'_def traceCorrect_def) 
    next
      case True
    (* if it is in a transaction, move it right before the transaction and adapt it to the correct invocId
      then remove all others and use packedTracesCorrect  *)

      from this 
      obtain  ib  tx txns'
        where ib1: "trace ! ib = (s, ABeginAtomic tx txns')"
          and ib2: "ib < i"
          and ib3: "\<forall>j. ib < j \<and> j < i \<longrightarrow> trace ! j \<noteq> (s, AEndAtomic)"
        by auto

      have trace_split1: "trace = take i trace  @ trace!i # drop (Suc i) trace"
        using `ib < i` \<open>i < length trace\<close>  id_take_nth_drop by blast 

      have trace_split2: "trace = take ib trace @ drop ib (take i trace)  @ trace!i # drop (Suc i) trace"
        using `ib < i` \<open>i < length trace\<close>
        by (metis add_Suc_right add_diff_cancel_left' append.assoc drop_take id_take_nth_drop less_imp_Suc_add take_add)

      find_theorems "trace!i"

      define s'' where "s'' = fst (trace ! (ib -1))"
      define trace' where "trace' \<equiv> take ib trace @ [(s'', AInvcheck False)]"

      have trace_split3: "trace = take (Suc i) trace  @ drop (Suc i) trace"
        using `ib < i` \<open>i < length trace\<close>  id_take_nth_drop by simp  

      with steps
      have "initialState program ~~ take (Suc i) trace  @ drop (Suc i) trace \<leadsto>* S" 
        by simp
      from this
      obtain Si 
        where steps_Si: "initialState program ~~ take (Suc i) trace \<leadsto>* Si"
        using steps_append by blast

      have "\<exists>trace' s'. (\<exists>S'. initialState program ~~ trace' \<leadsto>* S') \<and>
                  packed_trace trace' \<and>
                  (\<forall>s. (s, AFail) \<notin> set trace') \<and>
                  (\<forall>s. (s, AInvcheck True) \<notin> set trace') \<and> last trace' = (s', AInvcheck False) \<and> 0 < length trace' \<and> no_invariant_checks_in_transaction trace'"
      proof (rule  move_invariant_checks_out_of_transactions[OF steps_Si])
        show "packed_trace (take (Suc i) trace)"
          by (metis isPrefix_appendI packed prefixes_are_packed trace_split3)
        show "\<And>s. (s, AFail) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD nofail)
        show "\<And>s. (s, AInvcheck True) \<notin> set (take (Suc i) trace)"
          by (meson in_set_takeD noTrueInvs)
        show "last (take (Suc i) trace) = (s, AInvcheck False)"
          by (simp add: i1' i2 take_Suc_conv_app_nth)
        show "0 < length (take (Suc i) trace)"
          using gr_implies_not_zero i2 by auto
        show "\<And>ia s' . ia < length (take (Suc i) trace) - 1 \<Longrightarrow> take (Suc i) trace ! ia \<noteq> (s', AInvcheck False)"
          using i_min by fastforce
      qed

      thus False
        apply auto
        by (metis last_in_set packedTracesCorrect traceCorrect_def)
    qed
  qed
qed


thm show_programCorrect_noTransactionInterleaving'
text {*
 To show that a program is correct, we only have to consider packed and finished transactions
*}
theorem show_programCorrect_noTransactionInterleaving'':
  assumes packedTracesCorrect: 
    "\<And>trace s. \<lbrakk>initialState program ~~ trace \<leadsto>* s; packed_trace trace; allTransactionsEnd trace;  \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk> \<Longrightarrow> traceCorrect trace"
  shows "programCorrect program"
proof (rule show_programCorrect_noTransactionInterleaving')
  fix trace :: "(invocId \<times> 'a action) list"
  fix s
  assume steps: "initialState program ~~ trace \<leadsto>* s"
    and packed: "packed_trace trace" 
    and nofail: "\<And>s. (s, AFail) \<notin> set trace"
    and no_inv_checks: "no_invariant_checks_in_transaction trace"


  define "induct_measure" where "induct_measure  \<equiv> \<lambda>trace::(invocId \<times> 'a action) list. \<lambda>pos'.
    case pos' of
        0 \<Rightarrow> True
      | Suc pos \<Rightarrow>  pos<length trace \<and> (\<exists>i j tx txns. fst(trace!pos) = i \<and>  j\<le>pos \<and> trace!j = (i, ABeginAtomic tx txns) \<and> (\<nexists>k. k>j \<and> k<length trace \<and> trace!k = (i, AEndAtomic)))" 

  have induct_measure_ex: "\<exists>x. induct_measure trace x" for trace
    by (rule_tac x=0 in exI, auto simp add: induct_measure_def)

  have induct_measure_bound: "\<exists>bound. \<forall>x. induct_measure trace x \<longrightarrow> x \<le> bound" for trace
    by (rule_tac x="length trace" in exI, auto simp add: induct_measure_def split: nat.split)

  from steps packed nofail no_inv_checks
  show "traceCorrect trace"
  proof (induct "GREATEST pos'. induct_measure trace pos'"
      arbitrary: trace s rule: less_induct)
    case (less trace')
    show ?case
    proof (cases "Greatest (induct_measure trace')")
      case (0)
      hence [simp]: "(GREATEST a. induct_measure trace' a) = 0" by simp
      have "induct_measure trace' (GREATEST x. induct_measure trace' x) \<and> (\<forall>y. induct_measure trace' y \<longrightarrow> y \<le> (GREATEST x. induct_measure trace' x))"
        by (rule use_Greatest[OF induct_measure_ex induct_measure_bound])
      hence "\<nexists>pos. pos < length trace' \<and>
                         (\<exists>i j tx txns. fst (trace' ! pos) = i \<and> j \<le> pos \<and> trace' ! j = (i, ABeginAtomic tx txns) \<and> \<not> (\<exists>k>j. k < length trace' \<and> trace' ! k = (i, AEndAtomic)))"
        apply simp
        by (auto simp add: induct_measure_def split: nat.splits)
      hence "allTransactionsEnd trace'"
        apply (auto simp add: allTransactionsEnd_def)
        by force
      thus "traceCorrect trace'"
        using "less.prems" packedTracesCorrect by blast
    next
      case (Suc pos )
      hence [simp]: "(GREATEST x. induct_measure trace' x) = Suc pos" by simp

      have "induct_measure trace' (GREATEST x. induct_measure trace' x) \<and> (\<forall>y. induct_measure trace' y \<longrightarrow> y \<le> (GREATEST x. induct_measure trace' x))"
        by (rule use_Greatest[OF induct_measure_ex induct_measure_bound])
      hence m: "induct_measure trace' (Suc pos)"
        and  m_max: "\<And>y. induct_measure trace' y \<Longrightarrow> y \<le> Suc pos"
        by auto

      from m have "pos<length trace' \<and> (\<exists>i j tx txns. fst(trace'!pos) = i \<and>  j\<le>pos \<and> trace'!j = (i, ABeginAtomic tx txns) \<and> (\<nexists>k. k>j \<and> k<length trace' \<and> trace'!k = (i, AEndAtomic)))"
        by (auto simp add: induct_measure_def split: nat.splits)
      from this obtain j tx txns
        where pos_less: "pos < length trace'"
          and j_leq_pos: "j \<le> pos"
          and noEndAtomic_trace': "\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (fst (trace' ! pos), AEndAtomic)"
          and beginAtomic_trace': "trace' ! j = (fst (trace' ! pos), ABeginAtomic tx txns)"
        by auto

      with m_max 
      have maxPos: "fst (trace'!pos') \<noteq> fst(trace'!pos)" if "pos' > pos" and "pos' < length trace'" for pos'
        using that apply (auto simp add: induct_measure_def split: nat.splits)
        apply (drule_tac x="Suc pos'" in meta_spec)
        apply auto
        apply (erule meta_mp)
        using less_imp_le order_trans by blast

\<comment> \<open>  get new trace by removing action at pos  \<close>
      define newTrace where "newTrace = take pos trace' @ drop (Suc pos) trace'"

      have newTraceLen: "length newTrace = length trace' - 1"
        using \<open>pos < length trace'\<close> newTrace_def by auto

      have [simp]: "min (length trace') pos = pos"
        using \<open>pos < length trace'\<close> by auto


      have newTraceIth: "newTrace!i = (if i<pos then trace'!i else trace'!Suc i)" if "i<length newTrace"  for i
        using that \<open>pos < length trace'\<close> by (auto simp add: newTrace_def nth_append)

      have IH: " \<lbrakk>Greatest (induct_measure trace) < Greatest (induct_measure trace'); \<exists>S. initialState program ~~ trace \<leadsto>* S; packed_trace trace; \<And>s. (s, AFail) \<notin> set trace; no_invariant_checks_in_transaction trace\<rbrakk>
     \<Longrightarrow> traceCorrect trace" for trace
        using less.hyps   by auto \<comment> \<open>  TODO prove no_invariant_checks_in_transaction trace' \<close>


      have "traceCorrect newTrace"
      proof (rule IH, simp)
        show "Greatest (induct_measure newTrace) < Suc pos"
        proof (rule Greatest_smaller[OF induct_measure_ex induct_measure_bound])
          fix y
          assume a0: "induct_measure newTrace y"
          {
            assume "y > 0" and "y > pos"

            with a0 obtain j tx txns
              where a1: "y < Suc (length newTrace)" 
                and a2: "j < y"
                and a3: "\<forall>k<length newTrace. j < k \<longrightarrow> newTrace ! k \<noteq> (fst (newTrace ! (y-1)), AEndAtomic)"
                and a4: "newTrace ! j = (fst (newTrace ! (y-1)), ABeginAtomic tx txns)"
              apply (auto simp add: induct_measure_def split: nat.splits )
              using le_imp_less_Suc by blast

            have [simp]: "j < length newTrace"
              using a1 a2 by linarith

            have [simp]: "y - Suc 0 < length newTrace"
              using \<open>0 < y\<close> a1 by linarith

            have [simp]: " \<not>(y - Suc 0 < pos)"
              using \<open>pos < y\<close> by linarith

            have [simp]: "Suc (y - Suc 0) = y"
              by (simp add: \<open>0 < y\<close>)

            from a4 have a4': "newTrace ! j = (fst (trace' ! y), ABeginAtomic tx txns)"
              by (simp add: newTraceIth)

            have [simp]: "y < length trace'"
              using \<open>pos < length trace'\<close> a1 newTraceLen by linarith

            have "induct_measure trace' (Suc y)"
              apply (auto simp add: induct_measure_def)
              using a4 a3
            proof (auto simp add: newTraceIth split: if_splits)
              show "\<exists>j\<le>y. (\<exists>tx txns. trace' ! j = (fst (trace' ! y), ABeginAtomic tx txns)) \<and> (\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic))" 
                if c1: "\<forall>k. (j < k \<longrightarrow> k < length newTrace \<longrightarrow> k < pos \<longrightarrow> trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic)) 
                      \<and> (j < k \<longrightarrow> k < length newTrace \<longrightarrow> k < pos \<or> trace' ! Suc k \<noteq> (fst (trace' ! y), AEndAtomic))"
                  and c2: "j < pos" 
                  and c3: "trace' ! j = (fst (trace' ! y), ABeginAtomic tx txns)"
              proof (rule_tac x=j in exI, auto simp add: c3)
                show "j \<le> y"
                  using a2 by linarith
                show "False" 
                  if "k < length trace'" 
                    and "j < k" 
                    and "trace' ! k = (fst (trace' ! y), AEndAtomic)" for k
                proof (cases "k < pos")
                  case True
                  with c1 have "trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic)"
                    using \<open>pos < y\<close> a1 that(2) by auto
                  thus False
                    using that(3) by blast
                next
                  case False
                  with c1[rule_format, where k="k - 1"]
                  have "trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic)"
                    by (smt One_nat_def Suc_pred \<open>pos < y\<close> \<open>y < length trace'\<close> c2 fst_conv less_Suc_eq maxPos newTraceLen not_less0 not_less_iff_gr_or_eq that(1) that(2))
                  thus False
                    using that(3) by blast
                qed
              qed
              show "\<exists>j\<le>y. (\<exists>tx txns. trace' ! j = (fst (trace' ! y), ABeginAtomic tx txns)) \<and> (\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic))"
                if c1: "\<forall>k<length newTrace. j < k \<longrightarrow> trace' ! Suc k \<noteq> (fst (trace' ! y), AEndAtomic)"
                  and c2: "\<not> j < pos"
                  and c3: "trace' ! Suc j = (fst (trace' ! y), ABeginAtomic tx txns)"
              proof (rule exI[where x="Suc j"], auto simp add: c3)
                show "Suc j \<le> y"
                  using a2 by auto
                show "False" if "k < length trace'"
                  and "Suc j < k"
                  and "trace' ! k = (fst (trace' ! y), AEndAtomic)"
                for k
                proof -
                  from c1[rule_format, where k="k-1"]
                  have "trace' ! k \<noteq> (fst (trace' ! y), AEndAtomic)"
                    by (metis One_nat_def Suc_less_eq Suc_pred linorder_neqE_nat newTraceLen not_less0 that(1) that(2))
                  thus False
                    using that(3) by linarith
                qed
              qed
            qed
            hence "y < Suc pos"
              using Suc_le_lessD m_max by blast
            hence False
              using \<open>pos < y\<close> not_less_eq by blast
          }
          thus "y < Suc pos"
            using not_less_eq by blast
        qed
        show "\<exists>S_newEnd. initialState program ~~ newTrace \<leadsto>* S_newEnd"
        proof -
          find_theorems "initialState program" trace'
          have "trace' = take pos trace' @ [trace'!pos] @ drop (Suc pos) trace'"
            by (simp add: \<open>pos < length trace'\<close> id_take_nth_drop)

          with `initialState program ~~ trace' \<leadsto>* s`
          obtain S_pos S_pos2 S_end 
            where S_pos_steps: "initialState program ~~ take pos trace' \<leadsto>* S_pos"
              and S_pos_step: "S_pos ~~ trace'!pos \<leadsto> S_pos2"
              and S_pos2_steps: "S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end"
            by (smt append_Cons self_append_conv2 steps_append steps_appendFront)

          hence S_pos2_steps_initial: "initialState program ~~ take (Suc pos) trace' \<leadsto>* S_pos2"
            by (metis \<open>pos < length trace'\<close> steps_step take_Suc_conv_app_nth)



          define invoc where "invoc = fst(trace'!pos)"

          from `trace' ! j = (fst (trace' ! pos), ABeginAtomic tx txns)`
          have beginAtomic: "trace' ! j = (invoc, ABeginAtomic tx txns)"
            by (simp add: invoc_def)

          from `\<forall>k<length trace'. j < k \<longrightarrow> trace' ! k \<noteq> (fst (trace' ! pos), AEndAtomic)`
          have noEndAtomic: "\<And>k. \<lbrakk>k<length trace'; j < k\<rbrakk> \<Longrightarrow> trace' ! k \<noteq> (invoc, AEndAtomic)"
            by (simp add: invoc_def)

          have inTx: "currentTransaction S_pos2 invoc \<noteq> None"
          proof (rule inTransaction_trace[OF S_pos2_steps_initial])

            from `trace' ! j = (invoc, ABeginAtomic tx txns)`
            show "take (Suc pos) trace' ! j = (invoc, ABeginAtomic tx txns)"
              by (simp add: \<open>j \<le> pos\<close> le_imp_less_Suc)

            show "j < length (take (Suc pos) trace')"
              by (simp add: Suc_leI \<open>j \<le> pos\<close> \<open>pos < length trace'\<close> le_imp_less_Suc min.absorb2)

            show "\<And>k. \<lbrakk>k < length (take (Suc pos) trace'); j < k\<rbrakk> \<Longrightarrow> take (Suc pos) trace' ! k \<noteq> (invoc, AEndAtomic)"
              by (simp add: noEndAtomic)

            show "\<And>i. (i, AFail) \<notin> set (take (Suc pos) trace')"
              by (meson in_set_takeD less.prems(3))
          qed

          find_theorems S_pos
          find_theorems S_pos2

          find_theorems "steps S_pos"

          obtain pos_action where pos_action_def[simp]: "trace'!pos = (invoc, pos_action)"
            by (metis invoc_def prod.collapse)

          from S_pos_step
          have S_pos_step': "S_pos ~~ (invoc, pos_action) \<leadsto> S_pos2" 
            by simp

          have other_invocation: "\<And>a. a \<in> set (drop (Suc pos) trace') \<Longrightarrow> fst a \<noteq> invoc"
            using `invoc = fst (trace' ! pos)` `min (length trace') pos = pos` `\<And>pos'. \<lbrakk>pos < pos'; pos' < length trace'\<rbrakk> \<Longrightarrow> fst (trace' ! pos') \<noteq> fst (trace' ! pos)`
            apply (auto simp add: in_set_conv_nth)
            by (metis Suc_leI add_Suc fst_conv le_add_diff_inverse less_add_Suc1 nat_add_left_cancel_less pos_less)

          have other_invocation'[simp]: "\<And>a. (invoc, a) \<notin> set (drop (Suc pos) trace')" 
            by (meson fst_conv other_invocation)


          thm S_pos2_steps

          from `S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end`
          have S_pos_steps_to_S_end: "S_pos ~~ (invoc, pos_action) # drop (Suc pos) trace' \<leadsto>* S_end"
            using S_pos_step' steps_appendFront by blast


          from `initialState program ~~ take pos trace' \<leadsto>* S_pos`
          have S_pos_wf[simp]: "state_wellFormed S_pos"
            using state_wellFormed_combine state_wellFormed_init
            by (metis contra_subsetD less.prems(3) set_take_subset) 

          have "\<exists>S_new_end. S_pos ~~ drop (Suc pos) trace' \<leadsto>* S_new_end"
          proof (cases "pos_action")
            case ALocal
            hence [simp]: "pos_action = ALocal" by simp

            show ?thesis
              apply (rule exI, rule remove_local_step[OF S_pos_step' S_pos_steps_to_S_end S_pos2_steps])
              by (auto simp add: other_invocation)

          next
            case (ANewId x2)

            show ?thesis 
              apply (rule exI)
              apply (rule remove_newId_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps])
              using ANewId by (auto simp add: other_invocation)


          next
            case (ABeginAtomic x31 x32)

            find_theorems ABeginAtomic steps

            show ?thesis
              apply (rule exI)
              apply (rule remove_beginAtomic_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps])
              using ABeginAtomic by (auto simp add: other_invocation)

          next
            case AEndAtomic
            then show ?thesis 
              using \<open>j \<le> pos\<close> \<open>pos < length trace'\<close> local.beginAtomic noEndAtomic by fastforce
          next
            case (ADbOp x51 x52 x53 x54)
            show ?thesis 
              apply (rule exI)
              apply (rule remove_DBOp_step[OF S_pos_steps_to_S_end S_pos_step' S_pos2_steps])
              using ADbOp by (auto simp add: other_invocation)
          next
            case (AInvoc x61 x62)

            \<comment> \<open>  We already have an beginAtomic before, so we already have an invocId \<close>
            have "invocationOp S_pos invoc \<noteq> None"
              using AInvoc S_pos_step' S_pos_steps S_pos_wf \<open>j \<le> pos\<close> \<open>pos < length trace'\<close> currentTransaction dual_order.strict_trans le_eq_less_or_eq length_take less.prems(3) local.beginAtomic min.absorb2 noEndAtomic nth_mem nth_take option.simps(3) pos_action_def preconditionI precondition_beginAtomic precondition_invoc wellFormed_invoc_notStarted(1)
              by (smt action.simps(42) inTransaction_trace less.prems(1) prod.inject) 


            with AInvoc
            show ?thesis
              using S_pos_step inTx by (auto simp add: step.simps inTx)
          next
            case (AReturn x7)
            then show ?thesis 
              using S_pos_step inTx by (auto simp add: step.simps inTx)
          next
            case AFail
            then show ?thesis
              using \<open>pos < length trace'\<close> `\<And>s. (s, AFail) \<notin> set trace'` nth_mem by fastforce
          next
            case (AInvcheck x92)
            hence "S_pos2 = S_pos"
              using S_pos_step by (auto simp add: step.simps)
            with `S_pos2 ~~ drop (Suc pos) trace' \<leadsto>* S_end` 
            show ?thesis by blast
          qed


          with `initialState program ~~ take pos trace' \<leadsto>* S_pos`
          show "\<exists>S_newEnd. initialState program ~~ newTrace \<leadsto>* S_newEnd"
            by (auto simp add: newTrace_def  steps_append)
        qed

        show "packed_trace newTrace"
          using `packed_trace trace'` apply (auto simp add: newTrace_def packed_trace_def nth_append)
          using \<open>pos < length trace'\<close> dual_order.strict_trans apply blast
          by (metis (no_types, hide_lams) Suc_pred diff_Suc_Suc diff_zero less_add_same_cancel1 maxPos not_gr_zero not_less_eq not_less_less_Suc_eq zero_less_Suc zero_less_diff)
        show " \<And>s. (s, AFail) \<notin> set newTrace"
          using `\<And>s. (s, AFail) \<notin> set trace'` by (auto simp add: newTrace_def dest: in_set_takeD in_set_dropD )

        show "no_invariant_checks_in_transaction newTrace"
        proof (cases "snd (trace' ! pos) \<noteq> AEndAtomic")
          case True
          show ?thesis 
            unfolding newTrace_def
            by (rule maintain_no_invariant_checks_in_transaction[OF `no_invariant_checks_in_transaction trace'` True \<open>pos < length trace'\<close>])
          next
            case False
            with `no_invariant_checks_in_transaction trace'`
            show ?thesis 
              apply (case_tac "trace' ! pos")
              apply (auto simp add: newTrace_def no_invariant_checks_in_transaction_def nth_append )
              using beginAtomic_trace' j_leq_pos le_eq_less_or_eq noEndAtomic_trace' pos_less by auto
          qed
        qed

\<comment> \<open>  because no inv-checks in transaction  \<close>
      have removedNoInvCheck: "snd (trace'!pos) \<noteq> AInvcheck v" for v
        find_theorems trace'
        using `no_invariant_checks_in_transaction trace'`
        apply (auto simp add: no_invariant_checks_in_transaction_def)
        by (smt \<open>pos < length trace' \<and> (\<exists>i j tx txns. fst (trace' ! pos) = i \<and> j \<le> pos \<and> trace' ! j = (i, ABeginAtomic tx txns) \<and> \<not> (\<exists>k>j. k < length trace' \<and> trace' ! k = (i, AEndAtomic)))\<close> allowed_context_switch_def allowed_context_switch_simps(9) le_eq_less_or_eq min_def min_less_iff_conj prod.collapse prod.inject)



      show "traceCorrect trace'"
      proof (auto simp add: traceCorrect_def newTrace_def in_set_conv_nth)
        fix s i
        assume  "i < length trace'" and "trace' ! i = (s, AInvcheck False)"

        {
          assume "i<pos"
          hence "newTrace ! i \<noteq> (s, AInvcheck False)"
            using `traceCorrect newTrace` apply (auto simp add: traceCorrect_def in_set_conv_nth)
            using \<open>pos < length trace'\<close> newTrace_def by auto
          hence "trace' ! i \<noteq> (s, AInvcheck False)"
            using \<open>i < pos\<close> \<open>pos < length trace'\<close> newTraceIth newTraceLen by force
        }
        moreover
        {
          assume "i = pos"
          hence "newTrace ! i \<noteq> (s, AInvcheck False)"
            using \<open>trace' ! i = (s, AInvcheck False)\<close> removedNoInvCheck by auto
          hence "trace' ! i \<noteq> (s, AInvcheck False)"
            using \<open>i = pos\<close> removedNoInvCheck by fastforce
        }
        moreover
        {
          assume "i>pos"
          hence "newTrace ! i \<noteq> (s, AInvcheck False)"
            by (smt Suc_leI Suc_less_SucD \<open>i < length trace'\<close> \<open>trace' ! i = (s, AInvcheck False)\<close> \<open>traceCorrect newTrace\<close> diff_Suc_1 in_set_conv_nth leD less_imp_Suc_add newTraceIth newTraceLen traceCorrect_def)
          hence "trace' ! i \<noteq> (s, AInvcheck False)"
            by (smt Suc_leI Suc_less_SucD \<open>i < length trace'\<close> \<open>pos < i\<close> \<open>traceCorrect newTrace\<close> diff_Suc_1 in_set_conv_nth leD less_imp_Suc_add newTraceIth newTraceLen traceCorrect_def)
        }
        ultimately have "trace' ! i \<noteq> (s, AInvcheck False)"
          using antisym_conv3 by blast
        thus False
          using \<open>trace' ! i = (s, AInvcheck False)\<close> by blast
      qed
    qed
  qed
qed


find_consts name: allowed

definition noContextSwitchesInTransaction :: "'any trace \<Rightarrow> bool" where
  "noContextSwitchesInTransaction tr \<equiv> \<forall>i k invoc. 
    i < k \<and> k \<le> length tr 
   \<and> (\<exists>tx txns.  tr!i = (invoc, ABeginAtomic tx txns))
   \<and> (\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic) )
   \<longrightarrow> (\<forall>j. i < j \<and> j < k \<longrightarrow>  \<not> allowed_context_switch (snd (tr!j)))"

lemma use_noContextSwitchesInTransaction:
  assumes "noContextSwitchesInTransaction tr"
    and " tr!i = (invoc, ABeginAtomic tx txns)"
    and "i < k" 
    and "k \<le> length tr "
    and "\<forall>j. i<j \<and> j<k \<longrightarrow> tr!j \<noteq> (invoc, AEndAtomic)"
    and "i < j"
    and "j < k"
  shows "\<not>allowed_context_switch (snd (tr!j))"
  using assms apply (auto simp add: allowed_context_switch_def)
  apply (smt allowed_context_switch_simps(3) assms(3) noContextSwitchesInTransaction_def)
  by (smt allowed_context_switch_simps(6) assms(3) noContextSwitchesInTransaction_def)



lemma prefixes_noContextSwitchesInTransaction:
  assumes "noContextSwitchesInTransaction tr'" 
    and "isPrefix tr tr'"
  shows "noContextSwitchesInTransaction tr"
proof (auto simp add: noContextSwitchesInTransaction_def)
fix i k j invoc tx txns
assume a0: "k \<le> length tr"
   and a1: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
   and a2: "tr ! i = (invoc, ABeginAtomic tx txns)"
   and a3: "i < j"
   and a4: "j < k"
   and a5: "allowed_context_switch (snd (tr ! j))"


  have "\<not>allowed_context_switch (snd (tr' ! j))"
  proof (rule use_noContextSwitchesInTransaction[OF `noContextSwitchesInTransaction tr'`, where i=i and j=j and k=k])
    show "tr' ! i = (invoc, ABeginAtomic tx txns)"
      using a0 a2 a3 a4 assms(2) isPrefix_same by fastforce
    show "i < j " using a3 .
    show "j < k" using a4 .
    show "i < k"
      using a3 a4 less_trans by blast 
    show " k \<le> length tr'"
      by (meson a0 assms(2) isPrefix_len leD le_trans nat_le_linear)
    show " \<forall>j. i < j \<and> j < k \<longrightarrow> tr' ! j \<noteq> (invoc, AEndAtomic)"
      using a0 a1 assms(2) isPrefix_same by fastforce
  qed
  thus "False"
    using a0 a4 a5 assms(2) isPrefix_same by fastforce
qed

lemma packed_trace_prefix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace xs"
  using assms isPrefix_appendI prefixes_are_packed by blast

lemma packed_trace_postfix: 
  assumes "packed_trace (xs@ys)"
  shows "packed_trace ys"
  using assms  apply (auto simp add: packed_trace_def )
  apply (drule_tac x="i + length xs" in spec)
  apply (auto simp add: nth_append split: if_splits)
  done

lemma packed_trace_take:
  assumes "packed_trace tr"
  shows "packed_trace (take i tr)"
  by (metis append_take_drop_id assms packed_trace_prefix)


lemma packed_trace_drop:
  assumes "packed_trace tr"
  shows "packed_trace (drop i tr)"
  by (metis append_take_drop_id assms packed_trace_postfix)


  

lemma packedTraces_stay_in_transaction:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "packed_trace tr"
    and "currentTransaction S invoc \<triangleq> tx"
    and "tr \<noteq> [] \<Longrightarrow> fst (hd tr) = invoc"
    and "(invoc, AEndAtomic) \<notin> set tr"
    and "\<And>i. (i, AFail) \<notin> set tr"
    and "\<And>a. a\<in>set tr \<Longrightarrow> \<not>allowed_context_switch (snd a)"
    and "j < length tr"
  shows "currentTransaction S' invoc \<triangleq> tx \<and> fst (tr ! j) = invoc"
  using assms proof (induct arbitrary: j rule: steps_induct)
  case initial
  then show ?case by auto
next
  case (step S' tr a S'' j)

  show ?case
  proof (cases tr)
    case Nil
    with step
    show ?thesis 
      by (auto simp add: step.simps)
  next
    case (Cons x xs)

    have [simp]: "packed_trace tr"
      using packed_trace_prefix step.prems(1) by blast
    hence [simp]: "packed_trace (x#xs)"
      by (simp add: local.Cons)

    have [simp]: "currentTransaction S' (fst x) = Some tx"
      using local.Cons step.IH step.prems by force

    have "fst (last tr) = invoc"
      using last_conv_nth local.Cons step.IH step.prems by fastforce

    from Cons step
    have "currentTransaction S'' invoc \<triangleq> tx"
      by (auto simp add: step.simps split: if_splits)

    {
      assume j_def[simp]: "j = length (x # xs)"

      from use_packed_trace[OF `packed_trace (tr @ [a])`, where i="length tr"]
      have a_allowed_ctxt_switch: "fst a = invoc"
        by (metis \<open>fst (last tr) = invoc\<close> diff_less j_def last_conv_nth length_greater_0_conv less_numeral_extra(1) list.simps(3) local.Cons nth_append_first nth_append_length nth_mem step.prems(6) step.prems(7)) 

      have ?thesis
        by (simp add: \<open>currentTransaction S'' invoc \<triangleq> tx\<close> a_allowed_ctxt_switch local.Cons) 
    }
    moreover
    {
      assume "j < length (x # xs)"
      have ?thesis
        by (metis \<open>currentTransaction S'' invoc \<triangleq> tx\<close> \<open>j < length (x # xs)\<close> \<open>packed_trace tr\<close> append_is_Nil_conv butlast_snoc hd_append2 in_set_butlastD local.Cons nth_append_first step.IH step.prems(2) step.prems(3) step.prems(4) step.prems(5) step.prems(6))
    }
    ultimately show ?thesis
      using local.Cons step.prems(7) by fastforce
  qed
qed

lemmas packedTraces_stay_in_transaction1 = packedTraces_stay_in_transaction[THEN conjunct1]
lemmas packedTraces_stay_in_transaction2 = packedTraces_stay_in_transaction[THEN conjunct2]


lemma drop_nth:
"drop n xs ! i = (xs ! (min n (length xs) + i))"
proof (induct xs)
  case Nil
  then show ?case 
    by auto

next
  case (Cons a xs)
  then show ?case 
    apply auto
    by (metis (no_types, lifting) add_diff_cancel_left' append_take_drop_id length_Cons length_take min.commute not_add_less1 nth_append)
qed


lemma take_nth:
"take n xs ! i = (if i < n then xs ! i else []!(i - min n (length xs)))"
proof (induct xs arbitrary: n i)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  show ?case 
  proof (cases n)
    case 0
    thus ?thesis by auto
  next
    case (Suc n')
    thus ?thesis 
      apply auto
       apply (case_tac i)
      apply auto
      by (metis Cons.hyps One_nat_def Suc_pred diff_Suc_eq_diff_pred less_Suc_eq_0_disj neq0_conv)
  qed
qed

lemma packedTraces_transactions_same_invocation:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and beginTx: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and noEndTx: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and noContextSwitch: "\<forall>j. i < j \<and> j < k \<longrightarrow> \<not>allowed_context_switch (snd (tr!j))"
    and [simp]: "i < j" 
    and [simp]: "j < k"
    and [simp]: "k \<le> length tr"
  shows "fst (tr ! j) = invoc"
proof -
  have "take (Suc i) tr @ drop (Suc i) (take k tr) @ drop k tr = tr"
    apply (auto simp add: drop_take append_eq_conv_conj min_def)
    using `i < j` `j < k` apply linarith
    by (metis add_Suc_right `i < j` `j < k` le_add_diff_inverse2 less_imp_le less_trans_Suc)

  from this
  obtain S1 S2
    where "S ~~ take (Suc i) tr \<leadsto>* S1"
      and "S1 ~~ drop (Suc i) (take k tr) \<leadsto>* S2"
      and "S2 ~~ drop k tr \<leadsto>* S'"
    by (smt steps steps_append)


  from `S1 ~~ drop (Suc i) (take k tr) \<leadsto>* S2`
  have "fst ( drop (Suc i) (take k tr) ! (j - Suc i)) = invoc"
  proof (rule packedTraces_stay_in_transaction2)
    show "packed_trace (drop (Suc i) (take k tr))"
      using `packed_trace tr` packed_trace_drop packed_trace_take by blast 
    from `S ~~ take (Suc i) tr \<leadsto>* S1`
    have "S ~~ take i tr @ [tr!i] \<leadsto>* S1"
      by (metis `i < j` `j < k` `k \<le> length tr` dual_order.strict_trans min.absorb2 min_less_iff_conj take_Suc_conv_app_nth)
    from this
    obtain S1_pre where "S1_pre ~~ tr!i \<leadsto> S1"
      using steps_appendBack by blast

    thus  "currentTransaction S1 invoc \<triangleq> tx"
      using beginTx by (auto simp add: step_simps)
      
    show  "drop (Suc i) (take k tr) \<noteq> [] \<Longrightarrow> fst (hd (drop (Suc i) (take k tr))) = invoc"
      using `packed_trace tr` by (smt One_nat_def \<open>take (Suc i) tr @ drop (Suc i) (take k tr) @ drop k tr = tr\<close> append_Cons append_eq_append_conv append_is_Nil_conv append_self_conv append_take_drop_id `i < j` `j < k` `k \<le> length tr` beginTx diff_Suc_Suc diff_zero fst_conv hd_Cons_tl lessI less_trans_Suc noContextSwitch not_le_imp_less nth_via_drop packed_trace_def take_all zero_less_Suc)
      
    show  "(invoc, AEndAtomic) \<notin> set (drop (Suc i) (take k tr))"
      by (auto simp add: in_set_conv_nth take_nth drop_nth noEndTx)

    show  "\<And>ia. (ia, AFail) \<notin> set (drop (Suc i) (take k tr))"
      using noFail by (meson in_set_dropD in_set_takeD )

    show  "\<And>a. a \<in> set (drop (Suc i) (take k tr)) \<Longrightarrow> \<not> allowed_context_switch (snd a)"
      using noContextSwitch  apply (auto simp add: in_set_conv_nth take_nth drop_nth min_def  split: if_splits)
         apply (metis less_add_Suc1 snd_conv)
      apply (metis add.commute add_Suc assms(9) le_antisym less_add_Suc1 less_diff_conv snd_conv)
      apply (metis less_add_Suc1 snd_conv)
      by (metis add_Suc le_add_diff_inverse less_add_Suc1 nat_add_left_cancel_less snd_conv)

    show  "j - Suc i < length (drop (Suc i) (take k tr))"
      by (simp add: Suc_leI diff_less_mono min.absorb2)
      
  qed
  thus "fst (tr ! j) = invoc "
    using assms(7) assms(8) assms(9) by auto
qed




lemma noContextSwitchAllowedInTransaction:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and  packed: "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and beginAtomic: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and noEndAtomic: "\<forall>j. i < j \<and> j < k \<longrightarrow> snd (tr!j) \<noteq> AEndAtomic"
    and sameInvoc: "fst (tr!j) = invoc"
    and i_less_j: "i<j" 
    and k_less_k: "j<k"
    and k_length: "k\<le>length tr"
    and wf: "state_wellFormed S"
  shows "\<not>allowed_context_switch (snd (tr ! j))"
proof 
  assume a0: "allowed_context_switch (snd (tr ! j))"

  from steps
  have "S ~~ take j tr @ (tr!j # drop (Suc j) tr) \<leadsto>* S'"
    by (metis id_take_nth_drop k_length k_less_k less_le_trans)

  from this
  obtain S1 S2
    where "S ~~ take j tr \<leadsto>* S1"
      and "S1 ~~ tr!j \<leadsto> S2"
    using steps_append steps_appendFront by blast 

  have "fst (tr!j) = invoc"
    using i_less_j k_less_k sameInvoc by blast

  moreover have "currentTransaction S1 invoc \<triangleq> tx"
    by (smt currentTransaction \<open>S ~~ take j tr \<leadsto>* S1\<close>  i_less_j k_length k_less_k length_take less_imp_le less_le_trans local.beginAtomic min.absorb2 noEndAtomic noFail nth_mem nth_take snd_conv)

  moreover have "localState S1 invoc \<noteq> None"
    using \<open>S ~~ take j tr \<leadsto>* S1\<close> `currentTransaction S1 invoc \<triangleq> tx` inTransaction_localState local.wf state_wellFormed_combine
    by (metis noFail set_rev_mp set_take_subset) 
  ultimately 
  show False
    using  `S1 ~~ tr!j \<leadsto> S2` and `allowed_context_switch (snd (tr ! j))`
    by (auto simp add: step.simps allowed_context_switch_def)
qed

lemma noContextSwitchesInTransaction_when_packed_and_all_end:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and "allTransactionsEnd tr"
    and "packed_trace tr"
    and noFail: "\<And>i. (i, AFail) \<notin> set tr"
    and wf: "state_wellFormed S"
  shows "noContextSwitchesInTransaction tr"
proof (auto simp add: noContextSwitchesInTransaction_def)
  fix i k j invoc tx txns
  assume a0: "k \<le> length tr"
    and a1: "tr ! i = (invoc, ABeginAtomic tx txns)"
    and a3: "\<forall>j. i < j \<and> j < k \<longrightarrow> tr ! j \<noteq> (invoc, AEndAtomic)"
    and a4: "i < j"
    and a5: "j < k"
    and a6: "allowed_context_switch (snd (tr ! j))"


  obtain j_min 
    where a4_min: "i < j_min"
      and a5_min: "j_min < k"
      and a6_min: "allowed_context_switch (snd(tr!j_min))"
      and j_min_min: "\<forall>j. i<j \<and> j<k \<and> allowed_context_switch (snd (tr ! j)) \<longrightarrow> j_min \<le> j"
    apply atomize_elim
    apply (rule_tac x="Least (\<lambda>j. i<j \<and> j<k \<and> allowed_context_switch (snd (tr ! j)))" in exI)
    apply (rule LeastI2_wellorder_ex)
    using a4 a5 a6 by auto

  have tr_split: "tr = take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr"
    apply auto
    using a0 a5_min id_take_nth_drop less_le_trans by blast
  with steps have tr_split_steps: "S ~~ take j_min tr @ [tr!j_min] @ drop (Suc j_min) tr \<leadsto>* S'" by simp
  from this
  obtain S_j_min_pre S_j_min 
    where S_j_min_pre_steps: "S ~~ take j_min tr \<leadsto>* S_j_min_pre"
      and j_min_step: "S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min"
      and S_j_min_steps: "S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'"
    by (auto simp add: steps_append steps_appendFront  )


  have S_j_min_pre_wf: "state_wellFormed S_j_min_pre"
    by (meson S_j_min_pre_steps local.wf noFail rev_subsetD set_take_subset state_wellFormed_combine)

  hence "state_wellFormed S_j_min"
    using S_j_min_pre_steps j_min_step local.wf state_wellFormed_combine steps_step
    by (metis (no_types, lifting) append_assoc append_same_eq append_take_drop_id in_set_takeD noFail tr_split) 



  \<comment> \<open>  we are still in a transaction:  \<close>
  obtain tx 
    where currentTx: "currentTransaction S_j_min_pre invoc \<triangleq> tx"
    by (smt \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> a0 a1 a3 a4_min a5_min append_take_drop_id currentTransaction length_take less_imp_le less_le_trans min.absorb2 noFail nth_append_first nth_mem)

  hence ls: "localState S_j_min_pre invoc \<noteq> None"
    using \<open>S ~~ take j_min tr \<leadsto>* S_j_min_pre\<close> inTransaction_localState local.wf state_wellFormed_combine
    using S_j_min_pre_wf by blast


  with `S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min` 
    and `allowed_context_switch (snd(tr!j_min))`
  have "fst (tr!j_min) \<noteq> invoc"
    by (auto simp add: step.simps currentTx)


  \<comment> \<open>  there must be an endAtomic for the beginAtomic   \<close>
  from `allTransactionsEnd tr` 
  obtain i_end 
    where "tr!i_end = (invoc, AEndAtomic)" and "i_end \<ge> k" and "i_end \<le> length tr"
    apply (auto simp add: allTransactionsEnd_def)
    by (smt a0 a1 a3 a4 a5 dual_order.order_iff_strict dual_order.strict_trans not_less_eq not_less_less_Suc_eq)


  \<comment> \<open>  this means, we must go back to invoc. Take the first index where we go back to invoc  \<close>
  from this
  obtain back_min 
    where "back_min > j_min"
      and "back_min \<le> length tr"
      and "fst (tr!back_min) = invoc"
      and back_min_min: "\<forall>i. i > j_min \<and> i < length tr \<and> fst (tr!i) = invoc \<longrightarrow> i\<ge> back_min"
    apply atomize_elim
    apply (rule_tac x="Least (\<lambda>i. i > j_min \<and> i < length tr \<and> fst (tr!i) = invoc)" in exI)
    apply (rule LeastI2_wellorder_ex)
     apply auto
    by (smt a1 a3 a4_min a5_min allTransactionsEnd_def assms(2) dual_order.strict_trans dual_order.strict_trans1 fstI not_le_imp_less)

  have "back_min < length tr"
      by (smt \<open>back_min \<le> length tr\<close> \<open>j_min < back_min\<close> a1 a3 a4_min a5_min allTransactionsEnd_def assms(2) back_min_min dual_order.strict_trans fst_conv le_neq_implies_less not_le_imp_less)


  \<comment> \<open>  this must be a valid context switch, since it is the first to change back  \<close>
  from `packed_trace tr`
  have "allowed_context_switch (snd (tr ! back_min))"
  proof (rule use_packed_trace)
    show "0 < back_min"
      using \<open>j_min < back_min\<close> gr_implies_not0 by blast

    show "back_min < length tr"
      by (simp add: \<open>back_min < length tr\<close>)
    have "fst (tr ! (back_min - 1)) \<noteq> invoc"
      using back_min_min[rule_format, where i="back_min-1"]
      apply auto
      using \<open>back_min < length tr\<close> \<open>fst (tr ! j_min) \<noteq> invoc\<close> \<open>j_min < back_min\<close> not_less_less_Suc_eq by fastforce

    thus "fst (tr ! (back_min - 1)) \<noteq> fst (tr ! back_min)"
      by (auto simp add: `fst (tr!back_min) = invoc`)
  qed

  \<comment> \<open>  but since we are already in a transaction, that cannot work   \<close>

  have "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ drop back_min tr"
    by (auto simp add: Suc_leI \<open>back_min \<le> length tr\<close> \<open>j_min < back_min\<close> min.absorb2 min_diff nth_append add.commute intro: nth_equalityI)
  hence "drop (Suc j_min) tr = take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr"
    using Cons_nth_drop_Suc \<open>back_min < length tr\<close> by fastforce

  with `S_j_min ~~ drop (Suc j_min) tr \<leadsto>* S'`
  have "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) @ tr!back_min # drop (Suc back_min) tr \<leadsto>* S'"
    by force
  from this
  obtain S_back_min_pre S_back_min
    where S_back_min_pre_steps: "S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre"
      and back_min_step: "S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min"
      and S_back_min_steps: "S_back_min ~~ drop (Suc back_min) tr \<leadsto>* S'"
    by  (auto simp add: steps_append steps_appendFront )


  from S_back_min_pre_steps `state_wellFormed S_j_min`
  have "state_wellFormed S_back_min_pre"
    by (meson state_wellFormed_combine in_set_dropD in_set_takeD noFail)

  from `currentTransaction S_j_min_pre invoc \<triangleq> tx`
  have "currentTransaction S_j_min invoc \<triangleq> tx"
    using `S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min` 
    using \<open>fst (tr ! j_min) \<noteq> invoc\<close> by (auto simp add: step.simps )


  from  `S_j_min ~~ take (back_min - Suc j_min) (drop (Suc j_min) tr) \<leadsto>* S_back_min_pre`
  have "currentTransaction S_back_min_pre invoc \<triangleq> tx"
    find_theorems currentTransaction steps
  proof (rule currentTransaction_unchangedInternalSteps4(1))
    show "currentTransaction S_j_min invoc \<triangleq> tx"
      by (simp add: \<open>currentTransaction S_j_min invoc \<triangleq> tx\<close>) 
    show "state_wellFormed S_j_min"
    proof (rule state_wellFormed_combine[OF wf])
      show " S ~~ take j_min tr @ [tr ! j_min] \<leadsto>* S_j_min"
        using `S ~~ take j_min tr \<leadsto>* S_j_min_pre` `S_j_min_pre ~~ tr ! j_min \<leadsto> S_j_min`
        using steps_step by blast 
      show "\<And>i. (i, AFail) \<notin> set (take j_min tr @ [tr ! j_min])"
        using noFail \<open>back_min < length tr\<close> \<open>j_min < back_min\<close> apply auto
        apply (metis a6_min allowed_context_switch_simps(8) snd_conv)
        by (meson in_set_takeD)
    qed

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, AEndAtomic)"
      apply (auto simp add: in_set_conv_nth)
      by (metis add.commute add_Suc back_min_min fst_conv less_add_Suc1 less_diff_conv linorder_not_le)

    show "\<And>a. a \<in> set (take (back_min - Suc j_min) (drop (Suc j_min) tr)) \<Longrightarrow> a \<noteq> (invoc, AFail)"
      by (meson in_set_dropD in_set_takeD noFail)
  qed





  hence "localState S_back_min_pre invoc \<noteq> None"
    using `state_wellFormed S_back_min_pre`
    using inTransaction_localState by blast



  \<comment> \<open>  a contradiction  \<close>
  with `S_back_min_pre ~~ tr!back_min \<leadsto> S_back_min`
    and `allowed_context_switch (snd (tr ! back_min))`
    and \<open>fst (tr ! back_min) = invoc\<close>
    and `currentTransaction S_back_min_pre invoc \<triangleq> tx`
    and `localState S_back_min_pre invoc \<noteq> None`
  show "False"
    by (auto simp add:step.simps )
qed



end

