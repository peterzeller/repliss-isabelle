section "Completeness (Part 2)"
theory completeness2
  imports program_proof_rules_loops
begin

text "The goal here is to prove the inverse of the soundness theorem @{thm execution_s_check_sound}."

thm steps_io.induct



lemma steps_io_to_steps_s:
  assumes steps_io: "steps_io Inv qrySpec PS ls S' res"
    and res_cases: "res = None \<or> (\<exists>r. res = Some r \<and> \<not>P S' r)"
    and rel: "proof_state_rel PS S"
    and "Inv = (invariant (program S))"
    and "qrySpec = (querySpec (program S))"
    and "ps_i PS = i"
    and ls_def: "localState S (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ls)"
    and P_inv: "\<And>S' res. \<lbrakk>
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(ps_i PS \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>));
        uniqueIds res \<subseteq> ps_localKnown S'\<rbrakk>
        \<Longrightarrow> P S' res"
  shows "\<exists> CS' tr. (S ~~ (ps_i PS, tr) \<leadsto>\<^sub>S* CS')
              \<and> proof_state_rel S' CS'
              \<and> \<not>traceCorrect_s tr"
  using assms proof (induct rule: steps_io.induct, fuzzy_goal_cases steps_io_final steps_io_step steps_io_step)
  case (steps_io_final PS' res)
  hence "\<not>P PS' res"
    by blast

  have "ps_i PS' = ps_i PS"
    by (simp add: assms(6) steps_io_final.ps_i_eq)


  have "\<not>invariant (prog S) (invariantContext.truncate 
              (PS'\<lparr>invocationRes := invocationRes PS'(ps_i PS \<mapsto> res), 
                  knownIds := knownIds PS' \<union> uniqueIds res\<rparr>)) \<or> \<not>uniqueIds res \<subseteq> ps_localKnown PS'"
    using \<open>\<not> P PS' res\<close> assms(6) steps_io_final.ps_i_eq steps_io_final.P
    by auto

  have "currentProc S (ps_i PS) \<triangleq> impl_language_loops.toImpl"
    by (simp add: proof_state_rel_impl `proof_state_rel PS S`)

  have "currentTransaction S (ps_i PS) = ps_tx PS"
    using `proof_state_rel PS S` proof_state_rel_currentTx by blast

  thm proof_state_rel_facts[OF `proof_state_rel PS S`]

  have "ps_tx PS = None"
    sorry

  have "S ~~ (ps_i PS, [(AReturn res, False)]) \<leadsto>\<^sub>S*  S
             \<lparr>localState := (localState S)(ps_i PS := None), currentProc := (currentProc S)(ps_i PS := None),
                visibleCalls := (visibleCalls S)(ps_i PS := None), invocationRes := invocationRes S(ps_i PS \<mapsto> res),
                knownIds := knownIds S \<union> uniqueIds res\<rparr>"
  proof (auto simp add: steps_s_single step_s.simps ` localState S (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, impl_language_loops.io.WaitReturn res)`)
    show "\<exists>f. currentProc S (ps_i PS) \<triangleq> f 
        \<and> f (ps_store PS, ps_localKnown PS, impl_language_loops.io.WaitReturn res) = Return res 
        \<and> currentTransaction S (ps_i PS) = None"
      apply (rule exI[where x=toImpl])
      apply auto
      using \<open>currentProc S (ps_i PS) \<triangleq> impl_language_loops.toImpl\<close> apply blast
      apply (simp add: \<open>currentTransaction S (ps_i PS) = ps_tx PS\<close> \<open>ps_tx PS = None\<close>)




    assume "invariant (prog S) (invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S) (knownIds S \<union> uniqueIds res) (invocationOp S) (invocationRes S(i \<mapsto> res)))"

    show "False"
      if c0: 
      

  show ?case

  then show ?case sorry
next
  case (steps_io_error S cmd S' cmd')
  then show ?case sorry
next
  case (steps_io_step S cmd S' cmd' S'' res)
  then show ?case sorry
qed


lemma execution_s_check_sound:
  assumes ls_def: "localState S i \<triangleq> (Map.empty, localKnown, ls)"
    and vis_def: "visibleCalls S i \<triangleq> vis"
    and progr_def: "prog S = progr"
    and toImpl: "currentProc S i \<triangleq> toImpl"
    and generatedLocal: "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and generatedLocalPrivate1: "generatedLocalPrivate \<subseteq> generatedLocal"
    and generatedLocalPrivate2: "\<forall>v\<in>generatedLocalPrivate. uid_is_private i S v"
    and S_wf: "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    and no_currentTxn: "currentTransaction S i = None"
    and firstTx_def: "(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed ))"
    and localKnown: "localKnown = generatedLocal \<union> uniqueIds (the (invocationOp S i))"
    and no_guess: "invocation_cannot_guess_ids localKnown i S"
    and P_inv: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and P_ids: "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
    and prog_wf: "program_wellFormed (prog S)"
    and PS_def: "PS = \<lparr>
      calls = (calls S),
      happensBefore = (happensBefore S),
      callOrigin = (callOrigin S),
      transactionOrigin = (transactionOrigin S),
      knownIds = (knownIds S),
      invocationOp = (invocationOp S),
      invocationRes = (invocationRes S),
      ps_i = i,
      ps_generatedLocal = generatedLocal,
      ps_generatedLocalPrivate = generatedLocalPrivate,
      ps_localKnown = localKnown,
      ps_vis = vis,
      ps_localCalls = [],
      ps_tx = (currentTransaction S i),
      ps_firstTx = firstTx,
      ps_store = Map.empty,
      ps_prog = prog S\<rparr>"
    and s_correct: "execution_s_correct S i" 
    \<comment> \<open>The execution check ensures that executing statement s only produces valid traces ending in a state 
   satisfying P.\<close>
  shows "execution_s_check (invariant progr) (querySpec progr) PS ls P"
unfolding execution_s_check_def
proof (intro allI impI)
  fix S' res
  assume a0: "steps_io (invariant progr) (querySpec progr) PS ls S' res"
    and a1: "proof_state_wellFormed PS"

  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
  proof (rule ccontr)
    assume "\<not> (case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r)"
    hence res_cases: "res = None \<or> (\<exists>r. res = Some r \<and> \<not>P S' r)"
      by (auto split: option.splits)

    have "ps_i PS = i"
      by (simp add: PS_def)


    have "proof_state_rel PS S"
      unfolding proof_state_rel_def
    proof (intro conjI, goal_cases)
      case 1
      then show ?case 
        by (simp add: S_wf)

    next
      case 2
      then show ?case 
        by (simp add: PS_def)

    next
      case 3
      then show ?case 
        by (simp add: PS_def)

    next
      case 4
      then show ?case 
        by (simp add: PS_def)

    next
      case 5
      then show ?case 
        by (simp add: PS_def no_currentTxn)

    next
      case 6
      then show ?case 
        by (simp add: PS_def)

    next
      case 7
      then show ?case 
        by (simp add: PS_def)

    next
      case 8
      then show ?case 
        by (simp add: PS_def)

    next
      case 9
      then show ?case 
        using PS_def generatedLocal by auto

    next
      case 10
      then show ?case 
        using ls_def by (auto simp add:  PS_def)
    next
      case 11
      then show ?case 
        by (simp add: PS_def toImpl)

    next
      case 12
      then show ?case 
        by (simp add: PS_def vis_def)

    next
      case 13
      then show ?case 
        by (simp add: PS_def)

    next
      case 14
      then show ?case 
        by (simp add: PS_def no_uncommitted)

    next
      case 15
      then show ?case 
        by (simp add: PS_def no_currentTxn)

    next
      case 16
      then show ?case 
        by (simp add: PS_def sorted_by_empty)

    next
      case 17
      then show ?case 
        using PS_def by auto

    next
      case 18
      then show ?case 
        using PS_def by auto

    next
      case 19
      then show ?case 
        by (simp add: a1 proof_state_wellFormed_disjoint_happensBefore_localCalls)

    next
      case 20
      then show ?case 
        by (simp add: PS_def)

    next
      case 21
      then show ?case 
        using firstTx_def by (auto simp add: PS_def)
    next
      case 22
      then show ?case 
        using a1 proof_state_rel_see_my_updates proof_state_wellFormed_def by blast

    next
      case 23
      then show ?case
        using a1 proof_state_rel_localPrivateSub proof_state_wellFormed_def by blast 

    next
      case 24
      then show ?case 
        by (auto simp add: PS_def generatedLocalPrivate2)
    next
      case 25
      then show ?case 
        using a1 proof_state_wellFormed_finite_store by blast

    next
      case 26
      then show ?case 
        by (simp add: PS_def no_guess)

    next
      case 27
      then show ?case
        using a1 proof_state_rel_generatedLocalSub proof_state_wellFormed_def by blast 

    next
      case 28
      then show ?case 
        by (auto simp add: PS_def)

    next
      case 29
      then show ?case 
        by (simp add: PS_def no_currentTxn)

    qed

    from `steps_io (invariant progr) (querySpec progr) PS ls S' res`
    obtain CS' tr
      where "S ~~ (i, tr) \<leadsto>\<^sub>S* CS'"
      and "proof_state_rel S' CS'"
      and "\<not>traceCorrect_s tr"

      sorry

    thus False
      using execution_s_correct_def s_correct by blast
  qed
qed


lemma execution_s_check_sound4:
  fixes S :: "('proc::valueType, 'any store \<times>  uniqueId set \<times> ('any,'operation, 'any) impl_language_loops.io, 'operation::valueType, 'any::valueType) state"
  assumes a1: "localState S i \<triangleq> (Map.empty, uniqueIds op, ls)"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocationOp S i \<triangleq> op"
    and prog_wf: "program_wellFormed (prog S)"
    and inv: "invariant_all' S"
    and s_correct: "execution_s_correct S i"
  shows "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
\<lbrakk>
\<And>tx. s_transactionOrigin tx \<noteq> Some i;
invariant progr \<lparr>
  calls = s_calls,
  happensBefore = s_happensBefore,
  callOrigin = s_callOrigin,
  transactionOrigin = s_transactionOrigin,
  knownIds = s_knownIds,
  invocationOp = s_invocationOp(i\<mapsto>op),
  invocationRes = s_invocationRes(i:=None)
\<rparr>
\<rbrakk> \<Longrightarrow>
  execution_s_check (invariant progr) (querySpec progr) \<lparr>
      calls = s_calls,
      happensBefore = s_happensBefore,
      callOrigin = s_callOrigin,
      transactionOrigin = s_transactionOrigin,
      knownIds = s_knownIds,
      invocationOp = s_invocationOp(i\<mapsto>op),
      invocationRes = s_invocationRes(i:=None),
      ps_i = i,
      ps_generatedLocal = {},
      ps_generatedLocalPrivate = {},
      ps_localKnown = uniqueIds op,
      ps_vis = {},
      ps_localCalls = [],
      ps_tx = None,
      ps_firstTx = True,
      ps_store = Map.empty,
      ps_prog = progr\<rparr> ls (finalCheck (invariant progr) i)" 
  unfolding execution_s_check_def
proof (intro allI impI)
  fix s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes S' res
  assume noTx: "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
    and inv: "invariant progr          \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,             transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> op),             invocationRes = s_invocationRes(i := None)\<rparr>"
    and steps_io: "steps_io (invariant progr) (querySpec progr)          
          \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,             transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> op),             invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {},             ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds op, ps_vis = {}, ps_localCalls = [],             ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> 
          ls S' res"
    and wf: "proof_state_wellFormed          \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,             transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> op),             invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {},             ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds op, ps_vis = {}, ps_localCalls = [],             ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr>"



  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> finalCheck (invariant progr) i S' r"
  proof (rule ccontr)
    assume "\<not> (case res of None \<Rightarrow> False | Some r \<Rightarrow> finalCheck (invariant progr) i S' r)"
    hence res_cases: "res = None \<or> (\<exists>r. res = Some r \<and> \<not>finalCheck (invariant progr) i S' r)"
      by (auto split: option.splits)

    define PS where 
      "PS \<equiv> \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,             transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> op),             invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {},             ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds op, ps_vis = {}, ps_localCalls = [],             ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr>"

    have "proof_state_rel PS S"
      unfolding proof_state_rel_def
    proof (intro conjI)
   show "state_wellFormed S"
  using a2 initialStates'_same initialStates_wellFormed by blast
 show "calls S = calls PS"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "happensBefore S = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "callOrigin S = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS))"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "transactionOrigin S = (case ps_tx PS of None \<Rightarrow> transactionOrigin PS | Some tx \<Rightarrow> transactionOrigin PS(tx \<mapsto> ps_i PS))"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "knownIds S = knownIds PS"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "invocationOp S = invocationOp PS"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "invocationRes S = invocationRes PS"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "ps_generatedLocal PS = {x. generatedIds S x \<triangleq> ps_i PS}"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry

 show "\<exists>ps_ls. localState S (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ps_ls)"
 apply (auto simp add: PS_def)
 sledgehammer[cvc4]
 
sledgehammer[cvc4]
sorry


    from steps_io
    obtain CS CS' tr
      where "CS ~~ (i, tr) \<leadsto>\<^sub>S* CS'"
      and "proof_state_rel S CS"
      and "proof_state_rel S' CS'"
      and "\<not>traceCorrect_s tr"
      
sledgehammer[cvc4]
sorry


    from s_correct[simplified execution_s_correct_def, rule_format]

    show False

    thus False


  oops

end
