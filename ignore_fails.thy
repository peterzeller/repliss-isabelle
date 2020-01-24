section "Ignore Failures"

theory ignore_fails
  imports execution_invariants utils simulation_proofs
begin


text "In this section we show that we do not handle crashes (action @{term ACrash}) in order to prove 
correctness.
The main idea is that we we cannot distinguish a crash from arbitrary long waiting."


lemma can_ignore_fails:
  shows "(\<forall>tr\<in>traces program. traceCorrect tr) 
  \<longleftrightarrow> (\<forall>tr\<in>traces program. (\<nexists>s. (s, ACrash) \<in> set tr) \<longrightarrow>  traceCorrect tr)"
proof (rule iffI2; clarsimp)
  fix tr
  assume is_trace: "tr \<in> traces program"
    and tr_fail: "\<not> traceCorrect tr"

  from this obtain aFail S' 
    where "aFail\<in>set tr" 
      and "\<not>actionCorrect (get_action aFail)"
      and "initialState program ~~ tr \<leadsto>* S'"
    by (auto simp add: traceCorrect_def traces_def)  


  text \<open>
  Idea: a failed node and a node without progress are not really distinguishable in practice.
  In our semantics there are two small differences:
  
  1) state is different after failure
\<close>

  show "\<exists>tr\<in>traces program. (\<forall>s. (s, ACrash) \<notin> set tr) \<and> \<not> traceCorrect tr"
  proof (rule bexI[where x="[x\<leftarrow>tr . \<not>isACrash (get_action x)]"], intro conjI allI)

    show "\<And>s. (s, ACrash) \<notin> set [x\<leftarrow>tr . \<not>isACrash (get_action x)]"
      by (auto simp add: isACrash_def)

    show "\<not> traceCorrect [tr\<leftarrow>tr . \<not> isACrash (get_action tr)]"
      using tr_fail by (auto simp add: traceCorrect_def isACrash_def actionCorrect_def, force+)



    from \<open>initialState program ~~ tr \<leadsto>* S'\<close>
    have "\<exists>S''. (initialState program ~~ [tr\<leftarrow>tr . \<not> isACrash (get_action tr)] \<leadsto>* S'') 
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
         \<and> (\<forall>s. (s, ACrash) \<notin> set tr \<longrightarrow> ( 
             localState S'' s = localState S' s
           \<and> currentTransaction S'' s = currentTransaction S' s
           \<and> currentProc S'' s = currentProc S' s
           \<and> visibleCalls S'' s = visibleCalls S' s 
         ))
        )"                      
    proof (induct rule: trace_simulationProof)
      case initial                    
      then show ?case by auto
    next
      case f_empty_to_empty
      then show ?case by auto
    next
      case (induct_step tr a S1 S2 S1')
      from steps_append2[OF induct_step.steps2]
      have [simp]: "(initialState program ~~ [tr\<leftarrow>tr . \<not> isACrash (get_action tr)] @ trb \<leadsto>* C) \<longleftrightarrow> (S2 ~~ trb \<leadsto>* C)" for trb C .


      from \<open>S1 ~~ a \<leadsto> S1'\<close>
      show ?case 
      proof (cases rule: step.cases)
        case (local s ls f failed ls')

        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls')\<rparr>"],
              intro conjI,
              insert induct_step.coupling no_fail local,
              auto simp add: step_simps state_ext local induct_step steps_single)
      next
        case (newId s ls f ls' uid uidv ls'')
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls''), generatedIds := (generatedIds S2)(uid \<mapsto> s )\<rparr>"],
              insert induct_step.coupling no_fail newId,
              auto simp add: step_simps state_ext  induct_step steps_single)

      next
        case (beginAtomic s ls f ls' t vis snapshot)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))


        show ?thesis 
          by (rule exI[where x="S2\<lparr>
                  localState := localState S2(s \<mapsto> ls'), 
                  currentTransaction := currentTransaction S2(s \<mapsto> t), 
                  transactionStatus := transactionStatus S1(t \<mapsto> Uncommitted),
                  transactionOrigin := transactionOrigin S2(t \<mapsto> s),
                  visibleCalls := visibleCalls S2(s \<mapsto> snapshot)\<rparr>"],
              insert induct_step.coupling no_fail beginAtomic,
              auto simp add: step_simps state_ext  induct_step steps_single )

      next
        case (endAtomic s ls f ls' t)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls'), currentTransaction := (currentTransaction S2)(s := None), transactionStatus := transactionStatus S1(t \<mapsto> Committed)\<rparr>"],
              insert induct_step.coupling no_fail endAtomic,
              auto simp add: step_simps state_ext  induct_step steps_single)
      next
        case (dbop s ls f Op ls' t c res vis)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> ls' res), calls := calls S2(c \<mapsto> Call Op res), callOrigin := callOrigin S1(c \<mapsto> t), visibleCalls := visibleCalls S2(s \<mapsto> vis \<union> {c}), happensBefore := happensBefore S1 \<union> vis \<times> {c}\<rparr>"],
              insert induct_step.coupling no_fail dbop,
              auto simp add: step_simps state_ext  induct_step steps_single)

      next
        case (invocation s procName initialLocalState impl)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>invocationOp S1 s = None\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (meson everything_starts_with_an_invocation in_set_conv_nth)

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := localState S2(s \<mapsto> initialLocalState), currentProc := currentProc S2(s \<mapsto> impl), visibleCalls := visibleCalls S2(s \<mapsto> {}), invocationOp := invocationOp S2(s \<mapsto> procName)\<rparr>"],
              insert induct_step.coupling no_fail invocation,
              auto simp add: step_simps state_ext  induct_step steps_single)
      next
        case (return s ls f res)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))

        show ?thesis 
          by (rule exI[where x="S2\<lparr>localState := (localState S2)(s := None), currentProc := (currentProc S2)(s := None), visibleCalls := (visibleCalls S2)(s := None), invocationRes := invocationRes S1(s \<mapsto> res), knownIds := knownIds S1 \<union> uniqueIds res\<rparr>"],
              insert induct_step.coupling no_fail return,
              auto simp add: step_simps state_ext  induct_step steps_single)
      next
        case (fail s ls)
        from \<open>initialState program ~~ tr \<leadsto>* S1\<close> \<open>localState S1 s \<triangleq> ls\<close>
        have no_fail: "(s, ACrash) \<notin> set tr"
          by (metis (full_types) everything_starts_with_an_invocation in_set_conv_nth option.simps(3))
        show ?thesis 
          by (rule exI[where x="S2"],
              auto simp add: step_simps state_ext  induct_step  fail)

      next
        case (invCheck res s)

        show ?thesis 
          by (rule exI[where x="S2"],
              insert  induct_step.coupling  invCheck,
              auto simp add: step_simps state_ext  induct_step steps_single)
      qed
    qed


    then show "[tr\<leftarrow>tr . \<not> isACrash (get_action tr)] \<in> traces program"
      by (auto simp add: traces_def)
  qed
qed


end