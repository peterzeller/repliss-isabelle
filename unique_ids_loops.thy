section "Unique Ids in loop programs"

theory unique_ids_loops
  imports program_proof_rules_loops
begin

text "We show that programs using the loop language are well formed with respect to unique identifiers."

text_raw \<open>\DefineSnippet{invocations_cannot_guess_ids_io}{\<close>
lemma invocations_cannot_guess_ids_io:
  assumes proc_initial: "\<And>proc store localKnown cmd impl. 
    procedure progr proc = ((store, localKnown, cmd), impl) \<Longrightarrow> 
      impl = toImpl
      \<and> localKnown = uniqueIds proc"
shows "invocations_cannot_guess_ids progr"
text_raw \<open>}%EndSnippet\<close>
  unfolding invocations_cannot_guess_ids_def
proof
  fix i

  have always_toImpl: "impl = toImpl"
    if "initialState progr ~~ tr \<leadsto>* S"
      and "currentProc S i \<triangleq> impl"
    for tr S impl
    using that
  proof (induct rule: steps_induct)
    case initial
    then show ?case
      by (simp add: initialState_def)
  next
    case (step S' tr a S'')
    then show ?case 
      by (auto simp add: step.simps proc_initial prog_initial steps_do_not_change_prog split: if_splits)
  qed

  have localKnownTi: "localKnown = trace_inputs tr i"
    if "initialState progr ~~ tr \<leadsto>* S"
      and "localState S i \<triangleq> (store, localKnown, cmd)"
    for tr S store localKnown cmd
    using that
  proof (induct  arbitrary: store localKnown cmd rule: steps_induct)
    case initial
    then show ?case 
      by (simp add: initialState_def)
  next
    case (step S' tr a S'')


    show ?case
    proof (cases "currentProc S' i \<triangleq> toImpl")
      case False
      hence "currentProc S' i = None"
        using always_toImpl exists_optionI step.steps by blast

      with step 
      show "localKnown = trace_inputs (tr @ [a]) i"
        using proc_initial 
        by (auto simp add: step.simps proc_initial prog_initial steps_do_not_change_prog trace_inputs_append trace_inputs_cons trace_inputs_empty trace_inputs_if_no_op split: if_splits,
            use proc_initial in \<open>blast+\<close>)
    next
      case True

      from this 
      obtain store1 localKnown1 cmd1
        where ls: "localState S' i \<triangleq> (store1, localKnown1, cmd1)"
        using wf_localState_currentProc_m
        by (metis (no_types, hide_lams) exists_optionI option.distinct(1) prod_cases3 state_wellFormed_init step.steps wf_localState_currentProc)

      have IH: "localKnown1 = trace_inputs tr i"
        by (simp add: ls step.IH)

      show "localKnown = trace_inputs (tr @ [a]) i"
      proof (cases "fst a = i")
        case False
        with step
        show ?thesis 
          by (auto simp add: step.simps trace_inputs_append trace_inputs_cons trace_inputs_empty)
      next
        case True

        from `S' ~~ a \<leadsto> S''`
        have "S' ~~ (i, get_action a)  \<leadsto> S''"
          using True by auto


        from this                                           
        have  "localKnown = localKnown1 \<union> action_inputs (get_action a)"
          using ls[simplified IH] `currentProc S' i \<triangleq> toImpl` `localState S'' i \<triangleq> (store, localKnown, cmd)` IH
          by (auto simp add: step.simps elim!: toImpl.elims split: if_splits prod.splits)

        thus "localKnown = trace_inputs (tr @ [a]) i"
          by (simp add: IH True trace_inputs_append trace_inputs_cons trace_inputs_empty)
      qed
    qed
  qed


  show "invocation_cannot_guess_ids {} i (initialState progr)"
  proof (rule show_invocation_cannot_guess_ids)
    fix x tr a S'
    assume a0: "initialState progr ~~ tr @ [(i, a)] \<leadsto>* S'"
      and a1: "x \<in> action_outputs a"
      and a2: "x \<notin> {}"

    from a0
    obtain S where "initialState progr ~~ tr \<leadsto>* S" and "S ~~ (i, a) \<leadsto> S'"
      using steps_appendBack by blast

    show "x \<in> trace_inputs tr i"
    proof (cases "localState S i")
      case None
      then show ?thesis 
        using `S ~~ (i, a) \<leadsto> S'` `x \<in> action_outputs a`
        by (auto simp add: step.simps)
    next
      case (Some ls)
      from this
      obtain store1 cmd1
        where ls: "localState S i \<triangleq> (store1, trace_inputs tr i, cmd1)"
        using \<open>initialState progr ~~ tr \<leadsto>* S\<close> localKnownTi 
        by (metis prod_cases3)

      hence "currentProc S i \<triangleq> toImpl"
        by (smt \<open>initialState progr ~~ tr \<leadsto>* S\<close> always_toImpl not_Some_eq state_wellFormed_init wf_localState_currentProc wf_localState_currentProc_m)




      from `S ~~ (i, a) \<leadsto> S'`
        and `localState S i \<triangleq> (store1, trace_inputs tr i, cmd1)`
        and `currentProc S i \<triangleq> toImpl`
        and `x \<in> action_outputs a`
      show ?thesis 
        by (cases cmd1, auto simp add: step.simps split: prod.splits if_splits)
    qed
  qed
qed

   

end