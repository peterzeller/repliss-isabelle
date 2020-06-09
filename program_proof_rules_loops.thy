section "Program Proof Rules With Loops"

theory program_proof_rules_loops
  imports 
    invariant_simps 
    unique_ids2
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language_loops
    topological_sort
    program_verification_tactics
    "HOL-Eisbach.Eisbach_Tools"
    crdt_specs_v
begin

term "set"

text "We define some proof rules for our implementation languages, so that 
we can automate the generation of verification conditions.

The proof rules can simulate symbolic execution of a procedure.
We add some additional state compared to the system state in the semantics, so that we can derive
additional assumptions for the verification conditions."

\<comment> \<open>
Maybe it would have been better to use a record below.
However, with records it is sometimes difficult to get them into 
a normalized form where rules are directly applicable.
Still, it might be worth a try as it would make the rules more readable.
\<close>



record ('proc, 'any, 'operation) proof_state = "('proc, 'operation, 'any) invariantContext" +
  ps_i :: invocId
  ps_generatedLocal  :: "uniqueId set"
  ps_generatedLocalPrivate  :: "uniqueId set"
  ps_localKnown :: "uniqueId set"
  ps_vis :: "callId set"
  ps_localCalls :: "callId list"
  ps_tx :: "txid option"
  ps_firstTx :: bool
  ps_store :: "'any store"
  ps_prog :: "('proc, ('any store \<times> uniqueId set \<times> ('any, 'operation, 'any) io), 'operation, 'any) prog"

lemma proof_state_ext: "((x::('proc, 'any, 'operation) proof_state) = y) \<longleftrightarrow> (
    calls x = calls y
  \<and> happensBefore x = happensBefore y
  \<and> callOrigin x = callOrigin y
  \<and> transactionOrigin x = transactionOrigin y
  \<and> knownIds x = knownIds y
  \<and> invocationOp x = invocationOp y
  \<and> invocationRes x = invocationRes y
  \<and> ps_i x = ps_i y
  \<and> ps_generatedLocal x = ps_generatedLocal y
  \<and> ps_generatedLocalPrivate x = ps_generatedLocalPrivate y
  \<and> ps_localKnown x = ps_localKnown y
  \<and> ps_vis x = ps_vis y
  \<and> ps_localCalls x = ps_localCalls y
  \<and> ps_tx x = ps_tx y
  \<and> ps_firstTx x = ps_firstTx y
  \<and> ps_store x = ps_store y
  \<and> ps_prog x = ps_prog y
)"
  by auto


lemmas proof_stateEqI = proof_state_ext[THEN iffToImp, simplified imp_conjL, rule_format]



definition proof_state_rel :: "
     ('proc::valueType, 'any::valueType, 'operation::valueType) proof_state 
  \<Rightarrow> ('proc, ('any store \<times> uniqueId set \<times> ('any, 'operation, 'any) io), 'operation, 'any) state 
  \<Rightarrow> bool" where
  "proof_state_rel PS CS \<equiv> 
         state_wellFormed CS
       \<and> calls CS = calls PS
       \<and> happensBefore CS = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)
       \<and> callOrigin CS = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS))
       \<and> transactionOrigin CS = (case ps_tx PS of Some tx \<Rightarrow>  transactionOrigin PS(tx \<mapsto> ps_i PS) | None \<Rightarrow> transactionOrigin PS)
       \<and> knownIds CS = (knownIds PS)
       \<and> invocationOp CS = (invocationOp PS)
       \<and> invocationRes CS = (invocationRes PS)
       \<and> ps_generatedLocal PS = {x. generatedIds CS x \<triangleq> ps_i PS}
       \<and> (\<exists>ps_ls. localState CS (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS,  ps_ls))
       \<and> currentProc CS (ps_i PS) \<triangleq> toImpl 
       \<and> visibleCalls CS (ps_i PS) \<triangleq>  (ps_vis PS \<union> set (ps_localCalls PS))
       \<and> currentTransaction CS (ps_i PS) = ps_tx PS
       \<and> (\<forall>tx'. ps_tx PS \<noteq> Some tx' \<longrightarrow> transactionStatus CS tx' \<noteq> Some Uncommitted)
       \<and> (case ps_tx PS of Some tx' \<Rightarrow> set (ps_localCalls PS) =  {c. callOrigin CS c \<triangleq> tx'} 
                          | None \<Rightarrow> ps_localCalls PS = [])
       \<and> (sorted_by (happensBefore CS) (ps_localCalls PS))
       \<and> (ps_vis PS \<inter> set (ps_localCalls PS) = {})
       \<and> (dom (callOrigin PS) \<inter> set (ps_localCalls PS) = {})
       \<and> (Field (happensBefore PS) \<inter> set (ps_localCalls PS) = {})
       \<and> distinct (ps_localCalls PS)
       \<and> (ps_firstTx PS \<longleftrightarrow> (\<nexists>c tx . callOrigin CS c \<triangleq> tx \<and> transactionOrigin CS tx \<triangleq> ps_i PS \<and> transactionStatus CS tx \<triangleq> Committed ))
       \<and> (\<forall>c. i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c \<triangleq> (ps_i PS) \<longrightarrow> c \<in> (ps_vis PS))
       \<and> (ps_generatedLocalPrivate PS \<subseteq> ps_generatedLocal PS)
       \<and> (\<forall>v\<in>ps_generatedLocalPrivate PS. uid_is_private (ps_i PS) CS v)
       \<and> (finite (dom (ps_store PS)))
       \<and> (invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) CS)
       \<and> (ps_generatedLocal PS \<subseteq> ps_localKnown PS)
       \<and> prog CS = ps_prog PS
       \<and> (\<forall>t. ps_tx PS \<triangleq> t \<longrightarrow> transactionOrigin PS t = None)
"

\<comment> \<open>There might be a more elegant solution for this. Deatomize\<close>

lemmas proof_state_rel_wf = proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]
lemmas proof_state_rel_calls =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_hb =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_callOrigin =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_txOrigin =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_knownIds =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_invocationOp =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_invocationRes =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_genLocal =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_ls =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_impl =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_vis =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_currentTx =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_noUncommitted =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_localCalls =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_localCallsSorted =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_vis_localCalls_disjoint =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_callOrigin_localCalls_disjoint =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_happensBefore_localCalls_disjoint =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_localCalls_distinct =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_firstTx =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_see_my_updates =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_localPrivateSub =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_uid_private =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_finiteStore =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_icgi =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_generatedLocalSub =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_prog =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas proof_state_rel_transactionOriginNone =   proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]


lemmas proof_state_rel_facts = 
  proof_state_rel_wf
  proof_state_rel_calls
  proof_state_rel_hb
  proof_state_rel_callOrigin
  proof_state_rel_txOrigin
  proof_state_rel_knownIds
  proof_state_rel_invocationOp
  proof_state_rel_invocationRes
  proof_state_rel_genLocal
  proof_state_rel_ls
  proof_state_rel_impl
  proof_state_rel_vis
  proof_state_rel_currentTx
  proof_state_rel_noUncommitted
  proof_state_rel_localCalls
  proof_state_rel_localCallsSorted
  proof_state_rel_vis_localCalls_disjoint
  proof_state_rel_callOrigin_localCalls_disjoint
  proof_state_rel_happensBefore_localCalls_disjoint
  proof_state_rel_localCalls_distinct
  proof_state_rel_firstTx
  proof_state_rel_see_my_updates
  proof_state_rel_localPrivateSub
  proof_state_rel_uid_private
  proof_state_rel_finiteStore
  proof_state_rel_icgi
  proof_state_rel_generatedLocalSub
  proof_state_rel_prog
  proof_state_rel_transactionOriginNone


text "Define execution of a command."



definition "proof_state_wellFormed PS \<equiv> \<exists>S. proof_state_rel PS S"


lemma show_proof_state_wellFormed:
  assumes"proof_state_rel PS S" 
  shows "proof_state_wellFormed PS"
  using assms proof_state_wellFormed_def by auto


lemma proof_state_wellFormed_to_state_wellFormed:
  fixes PS :: " ('proc::valueType, 'any::valueType, 'operation::valueType) proof_state "
  assumes "proof_state_wellFormed PS"
  shows "\<exists>(s_prog:: ('proc, 'any store \<times>uniqueId set \<times>('any, 'operation, 'any) io, 'operation, 'any) prog) 
    s_transactionStatus s_generatedIds s_localState s_currentProc s_visibleCalls s_currentTransaction.
  (\<forall>tx'. ps_tx PS \<noteq> Some tx' \<longrightarrow> s_transactionStatus tx' \<noteq> Some Uncommitted)
  \<and> ps_generatedLocal PS = {x. s_generatedIds x \<triangleq> ps_i PS}
  \<and> (\<exists>ps_ls. s_localState (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS,  ps_ls))
  \<and> s_currentProc (ps_i PS) \<triangleq> toImpl
  \<and> s_visibleCalls (ps_i PS) \<triangleq>  (ps_vis PS \<union> set (ps_localCalls PS))
  \<and> s_currentTransaction (ps_i PS) = ps_tx PS
  \<and> state_wellFormed \<lparr>
        calls = calls PS, 
        happensBefore = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS), 
        callOrigin = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
        transactionOrigin = (case ps_tx PS of Some tx \<Rightarrow>  transactionOrigin PS(tx \<mapsto> ps_i PS) | None \<Rightarrow> transactionOrigin PS), 
        knownIds = knownIds PS, 
        invocationOp = invocationOp PS,
        invocationRes = invocationRes PS, 
        prog = s_prog,
        transactionStatus = s_transactionStatus,
        generatedIds = s_generatedIds,
        localState = s_localState,
        currentProc = s_currentProc,
        visibleCalls = s_visibleCalls,
        currentTransaction = s_currentTransaction
      \<rparr>"
proof -
  from  assms[simplified proof_state_wellFormed_def]
  obtain S :: "('proc, 'any store \<times>uniqueId set \<times>('any, 'operation, 'any) io,'operation, 'any) state"
    where rel: "proof_state_rel PS S" by blast


  thm  proof_state_rel_wf[OF rel]

  show ?thesis
  proof (intro exI, intro conjI)

    show "state_wellFormed
     \<lparr>calls = calls PS, 
        happensBefore = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS), 
        callOrigin = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
        transactionOrigin = (case ps_tx PS of Some tx \<Rightarrow>  transactionOrigin PS(tx \<mapsto> ps_i PS) | None \<Rightarrow> transactionOrigin PS), 
        knownIds = knownIds PS, 
        invocationOp = invocationOp PS,
        invocationRes = invocationRes PS, 
        prog = prog S, 
        transactionStatus = transactionStatus S,
        generatedIds = generatedIds S, 
        localState = localState S, 
        currentProc = currentProc S,
        visibleCalls = visibleCalls S, 
        currentTransaction = currentTransaction S\<rparr>"
    proof (rule arg_cong[THEN iffD1,rotated, where f1=state_wellFormed, OF proof_state_rel_wf[OF rel]], 
        subst state_ext, intro conjI, 
        unfold operationContext.simps distributed_state.simps state.simps invariantContext.simps)
      show "calls S = calls PS"
        using proof_state_rel_calls rel by blast
      show "happensBefore S = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)"
        using proof_state_rel_hb rel by blast

      show "callOrigin S = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS))"
        by (simp add: proof_state_rel_callOrigin rel)
      show "transactionOrigin S = (case ps_tx PS of Some tx \<Rightarrow>  transactionOrigin PS(tx \<mapsto> ps_i PS) | None \<Rightarrow> transactionOrigin PS)"
        using proof_state_rel_txOrigin rel by blast
      show "knownIds S = knownIds PS"
        by (simp add: proof_state_rel_knownIds rel)
      show "invocationOp S = invocationOp PS"
        using proof_state_rel_invocationOp rel by blast
      show "invocationRes S = invocationRes PS"
        using proof_state_rel_def rel by blast
    qed (simp; fail)+

    show "\<exists>s_ls. localState S (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, s_ls)"
      by (simp add: proof_state_rel_ls rel)


  qed ((auto simp add: proof_state_rel_facts[OF \<open>proof_state_rel PS S\<close>])[1]; fail)+
qed

\<comment> \<open>TODO : more properties about freshness: uid cannot be used anywhere \<close>

definition "uid_fresh uid S \<equiv> uid_is_private' (ps_i S) (calls S)
  (invocationOp S) (invocationRes S) (knownIds S) uid"


\<comment> \<open>TODO: need some information about Growing \<close>
definition "ps_growing S S' t \<equiv> 
  \<exists>CS CS'.
    proof_state_rel S CS
  \<and> proof_state_rel S' CS'
  \<and> ps_localCalls S = []
  \<and> ps_localCalls S' = []
  \<and> ps_tx S = None
  \<and> ps_tx S' \<triangleq> t
  \<and> ps_i S' = ps_i S
  \<and> ps_prog S' = ps_prog S
  \<and> ps_generatedLocal S' = ps_generatedLocal S
  \<and> ps_generatedLocalPrivate S' = ps_generatedLocalPrivate S
  \<and> ps_localKnown S' = ps_localKnown S
  \<and> ps_firstTx S' = ps_firstTx S
  \<and> ps_store S' = ps_store S
  \<and> state_monotonicGrowth (ps_i S) CS (CS' \<lparr>
        transactionStatus := (transactionStatus CS')(t := None), 
        transactionOrigin := (transactionOrigin CS')(t := None),
        currentTransaction := (currentTransaction CS')(ps_i S := None), 
        localState := (localState CS')(ps_i S := localState CS (ps_i S)),
        visibleCalls := (visibleCalls CS')(ps_i S := visibleCalls CS (ps_i S))\<rparr>)"


definition "current_operationContext S \<equiv> \<lparr>
  calls = calls S,
  happensBefore = updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)
\<rparr>"

definition "current_vis S \<equiv> ps_vis S \<union> set (ps_localCalls S)"

text "Define execution of io commands:"


definition step_io :: "
     (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool)
  \<Rightarrow> ('operation, 'operation, 'any) ccrdtSpec
  \<Rightarrow> ('proc, 'any, 'operation) proof_state 
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> ('proc, 'any, 'operation) proof_state
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> bool \<comment> \<open>step is correct\<close>
  \<Rightarrow> bool " where
  "step_io progInv qrySpec S cmd S' cmd' Inv \<equiv> 
  (Inv \<longrightarrow> proof_state_wellFormed S')
  \<and> (case cmd of
    WaitReturn r \<Rightarrow> False
  | WaitLocalStep cont \<Rightarrow> 
       (\<exists>store' ok.  
           cont (ps_store S) =  (ok, store', cmd') 
         \<and> (Inv \<longleftrightarrow> ok \<and> finite (dom store'))
         \<and> (S' = S\<lparr>      
            ps_store := store'
           \<rparr>))
  | WaitBeginAtomic n \<Rightarrow>
      \<exists>t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes'.
          cmd' = n
        \<and> Inv
        \<and> ps_tx S = None
        \<and> progInv (invariantContext.truncate (S'\<lparr>transactionOrigin := transactionOrigin'\<rparr>))
        \<and> transactionOrigin' t = None 
        \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> (transactionOrigin S t' \<triangleq> ps_i S \<longleftrightarrow> transactionOrigin' t' \<triangleq> ps_i S))
        \<and> chooseSnapshot_h vis' (ps_vis S) (\<lambda>tx. Some Committed) callOrigin' happensBefore'
        \<and> consistentSnapshotH calls' happensBefore' callOrigin' (\<lambda>tx. Some Committed) vis'
        \<and> (\<forall>c. callOrigin' c \<noteq> Some t)
        \<and> (S' = S\<lparr>
             calls := calls',
             happensBefore := happensBefore',
             callOrigin := callOrigin',
             transactionOrigin := transactionOrigin',
             knownIds := knownIds',
             invocationOp := invocationOp',
             invocationRes := invocationRes',
             ps_tx := Some t,
             ps_vis := vis'
          \<rparr>)
        \<and> ps_growing S S' t
        \<and> transactionOrigin S t = None
  | WaitEndAtomic n \<Rightarrow>
        cmd' = n
      \<and> (S' = S\<lparr>
        happensBefore := updateHb (happensBefore S) (ps_vis S) (ps_localCalls S),
        callOrigin := map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S)),
        transactionOrigin := transactionOrigin S(the (ps_tx S) \<mapsto> ps_i S),
        ps_tx := None,
        ps_localCalls := [],
        ps_vis := ps_vis S \<union> set (ps_localCalls S),
        ps_firstTx := ps_firstTx S \<and> ps_localCalls S = []
      \<rparr>)
      \<and> (Inv  \<longleftrightarrow> progInv (invariantContext.truncate S'))
  | WaitNewId P n \<Rightarrow>
    \<exists> uidv uid.
       cmd' = n uidv
     \<and> Inv
     \<and> uniqueIds uidv = {uid}
     \<and> uid \<notin> ps_generatedLocal S
     \<and> uid_fresh uid S
     \<and> P uidv
     \<and> (S' = S\<lparr>
          ps_localKnown := ps_localKnown S \<union> {uid},
          ps_generatedLocal := ps_generatedLocal S \<union> {uid},
          ps_generatedLocalPrivate := ps_generatedLocalPrivate S \<union> {uid}
         \<rparr>)
  | WaitDbOperation oper n \<Rightarrow>
       (if Inv then
          \<exists>c res. 
           calls S c = None
         \<and> ps_tx S \<noteq> None
         \<and> uniqueIds oper \<subseteq> ps_localKnown S 
         \<and> toplevel_spec qrySpec (current_operationContext S) (current_vis S) oper res
         \<and> cmd' = n res
         \<and> (S' = S\<lparr>
            ps_localKnown := ps_localKnown S \<union> uniqueIds res, 
            ps_generatedLocalPrivate := ps_generatedLocalPrivate S - uniqueIds oper,
            calls := (calls S)(c \<mapsto> Call oper res),
            ps_localCalls := ps_localCalls S @ [c]
          \<rparr>)
        else
          S' = S \<and> cmd' = cmd \<and> \<not>(uniqueIds oper \<subseteq> ps_localKnown S) 
        )
  | Loop i body n \<Rightarrow> 
      cmd' = loop_body_from_V body i \<bind> (\<lambda>r. case r of Continue x \<Rightarrow> Loop x body n | Break x \<Rightarrow> n x )
      \<and> Inv
      \<and> (S' = S))
"




text \<open>@{term steps_io} is an inductive definition for combining multiple steps and getting 
  a result value (from WaitReturn).
If the result is None, there was an error in the execution.
Otherwise, the result is Some r.
\<close>

inductive steps_io :: "
     (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool)
  \<Rightarrow> ('operation, 'operation, 'any) ccrdtSpec
  \<Rightarrow> ('proc, 'any, 'operation) proof_state 
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> ('proc, 'any, 'operation) proof_state
  \<Rightarrow> 'a option
  \<Rightarrow> bool " for progInv qrySpec where
  steps_io_final:
  "steps_io progInv qrySpec S (WaitReturn res) S (Some res)"
| steps_io_error:
  "step_io progInv qrySpec S cmd S' cmd' False
  \<Longrightarrow> steps_io progInv qrySpec S cmd S' None"
| steps_io_step:
  "\<lbrakk>step_io progInv qrySpec S cmd S' cmd' True;
   steps_io progInv qrySpec S' cmd' S'' res
\<rbrakk>
 \<Longrightarrow>  steps_io progInv qrySpec S cmd S'' res"

\<comment> \<open>TODO might want to change this: remove the trace 
and steps-io-partial. Instead return None when not ok and 
only allow to make a step when ok. \<close>

\<comment> \<open>TODO: better to have a case on the action? 
Hmm, not really. Then I would not know when I am done.

One problem is: Two io values can be different but have the same semantics (e.g. unrolled loops).
I should define semantic equality below.
\<close>




lemma cmd_is_local:
  assumes noReturn: "\<And>r. cmd \<noteq> WaitReturn r"
  shows
    "(cmd \<bind> cmdCont = WaitLocalStep n)
\<longleftrightarrow> (\<exists>n'. cmd = WaitLocalStep n' 
      \<and> (\<forall>store. 
          let (ok,  st, cmd) = n store;
              (ok', st', cmd') = n' store
          in st = st' \<and> ok = ok' \<and> cmd = (cmd' \<bind> cmdCont))) "
  using noReturn  apply (induct cmd)
        apply (auto simp add: noReturn dest!: fun_cong2 intro!: HOL.ext split: prod.splits)
proof -
  fix x :: "(nat \<Rightarrow> 'c option) \<Rightarrow> bool \<times> (nat \<Rightarrow> 'c option) \<times> ('a, 'b, 'c) impl_language_loops.io" and s :: "nat \<Rightarrow> 'c option" and x1 :: bool and a :: "nat \<Rightarrow> 'c option" and b :: "('a, 'b, 'c) impl_language_loops.io"
  assume a1: "\<forall>store x1 a b x1a aa ba. x store = (x1a, aa, ba) \<longrightarrow> n store = (x1, a, b) \<longrightarrow> a = aa \<and> x1 = x1a \<and> b = ba \<bind> cmdCont"
  assume a2: "x s = (x1, a, b)"
  obtain bb :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> bool" and zz :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> nat \<Rightarrow> 'c option" and ii :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> ('d, 'b, 'c) impl_language_loops.io" where
    f3: "\<forall>p. p = (bb p, zz p, ii p)"
    by (meson prod_cases3)
  then have "n s = (bb (n s), zz (n s), ii (n s))"
    by meson
  then have f4: "zz (n s) = a \<and> (\<not> bb (n s)) \<noteq> x1 \<and> ii (n s) = b \<bind> cmdCont"
    using a2 a1 by presburger
  have "n s = (bb (n s), zz (n s), ii (n s))"
    using f3 by meson
  then show "(x1, a, b \<bind> cmdCont) = n s"
    using f4 by force
qed

abbreviation
  "currentCommand S i \<equiv> snd (snd (the (localState S i)))"



lemma prop_subst': "t = s \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by auto

\<comment> \<open>Strange rotations and shifting to remove the first equality that you
usually get when using a cases rule.\<close>
method remove_first_equality = (
    ((drule allI impI)+)?,
    (rotate_tac 1),
    ((erule rev_mp)+)?,
    (rule impI),
    (erule prop_subst'),
    ((rule impI)+)?,
    ((erule rev_mp)+)?,
    (unfold triv_forall_equality)?,
    ((rule impI)+)?
    )

lemma "\<And>y a b q. \<lbrakk>x = y; A x y a; B x y b; C x y \<rbrakk> \<Longrightarrow> D x y a"
  apply remove_first_equality
  oops

lemma "\<lbrakk>S = Sxxxxxxxxxxxxxxxxxx; (i, action, Inv) = (ia, ABeginAtomic t vis', True); S' = S'';
     localState Sxxxxxxxxxxxxxxxxxx ia \<triangleq> ls; currentProc Sxxxxxxxxxxxxxxxxxx ia \<triangleq> f; f ls = BeginAtomic ls';
     currentTransaction Sxxxxxxxxxxxxxxxxxx ia = None; transactionStatus Sxxxxxxxxxxxxxxxxxx t = None;
     prog S'a = prog Sxxxxxxxxxxxxxxxxxx; state_monotonicGrowth ia Sxxxxxxxxxxxxxxxxxx S'a;
     \<And>t. transactionOrigin Sxxxxxxxxxxxxxxxxxx t \<triangleq> ia = transactionOrigin S'a t \<triangleq> ia; invariant_all S'a;
     \<And>tx. transactionStatus S'a tx \<noteq> Some Uncommitted; state_wellFormed S'a; state_wellFormed S'';
     localState S'a ia \<triangleq> ls; currentProc S'a ia \<triangleq> f; currentTransaction S'a ia = None;
     visibleCalls Sxxxxxxxxxxxxxxxxxx ia \<triangleq> vis; visibleCalls S'a ia \<triangleq> vis; chooseSnapshot vis' vis S'a;
     consistentSnapshot S'a vis'; transactionStatus S'a t = None; \<And>c. callOrigin S'a c \<noteq> Some t;
     transactionOrigin S'a t = None;
     S'' = S'a
     \<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommitted),
        transactionOrigin := transactionOrigin S'a(t \<mapsto> ia), currentTransaction := currentTransaction S'a(ia \<mapsto> t),
        localState := localState S'a(ia \<mapsto> ls'), visibleCalls := visibleCalls S'a(ia \<mapsto> vis')\<rparr>\<rbrakk>
    \<Longrightarrow> False"
  apply remove_first_equality
  oops




method cmd_step_cases uses step insert simps  = 
  (rule step_s.cases[OF step]; 
    remove_first_equality;
    insert insert;
    (((auto simp add: simps split: prod.splits)[1]; fail)?); 
    ((erule Pair_inject)+)?,
    fuzzy_goal_cases A)
  (*
  erule prop_subst;
  fuzzy_goal_cases A)
*)


(* TODO move to utils: *)
definition "marker_L x \<equiv> x"
definition "marker_R x \<equiv> x"

lemma conjI_marked: 
  assumes "marker_L P" and "marker_R Q"
  shows "P \<and> Q"
  using assms unfolding marker_L_def marker_R_def by simp



method conj_one_by_one uses pre = (
    match pre in 
    p: "?P \<and> ?Q" \<Rightarrow> \<open>
        (unfold marker_L_def marker_R_def)?, 
        rule conjI_marked;( 
            (match conclusion in "marker_L _" \<Rightarrow> \<open>(conj_one_by_one pre: p[THEN conjunct1])?\<close>)
          | (match conclusion in "marker_R _" \<Rightarrow> \<open>(conj_one_by_one pre: p[THEN conjunct2])?\<close>))\<close>)
    | ((unfold marker_L_def marker_R_def)?, insert pre)

lemma
  assumes c: "a 0 \<and> a 1 \<and> a 2  \<and> a 3"
    and imp: "\<And>i. a i \<Longrightarrow> a' i"
  shows "a' 0 \<and> a' 1 \<and> a' 2 \<and> a' 3"
  apply (conj_one_by_one pre: c)
  using imp by auto


lemma step_io_simulation:
  assumes rel: "proof_state_rel PS S"
    and step: "S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'"
    and i_def: "i = ps_i PS"
    and cmd_prefix: "currentCommand S i = cmd \<bind> cmdCont"
    and cm_no_return: "\<And>r. cmd \<noteq> WaitReturn r"
    and prog_wf: "program_wellFormed (prog S)"
    and spec_rel: "crdt_spec_rel (querySpec (prog S)) querySpec'"
    and no_generate_db: "\<And>c Op res. action = ADbOp c Op res \<Longrightarrow> uniqueIds Op \<subseteq> ps_localKnown PS"
  shows "\<exists>PS' cmd'. step_io (invariant (prog S)) querySpec' 
                            PS cmd PS' cmd' Inv 
               \<and> (Inv \<longrightarrow> proof_state_rel PS' S' \<and> currentCommand S' i = cmd' \<bind> cmdCont)" (is ?g)
proof (rule ccontr)
  assume "\<not>?g"

  hence goal: False if ?g
    using that by blast



  have toImpl: "currentProc S (ps_i PS) \<triangleq> toImpl"
    by (simp add: assms(1) proof_state_rel_impl)
  hence currentProc[simp]: "currentProc S i \<triangleq> toImpl"
    using i_def by simp


  have ls[simp]: "localState S i \<triangleq> (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
    using cmd_prefix i_def proof_state_rel_ls rel by force

  have "state_wellFormed S"
    using proof_state_rel_wf rel by auto
  hence "state_wellFormed S'"
    using local.step state_wellFormed_combine_s1 by blast


  have [simp]: "invocationOp S i \<noteq> None"
    by (simp add: \<open>state_wellFormed S\<close> wf_localState_to_invocationOp)

  have [simp]: "finite (dom (ps_store PS))"
    using proof_state_rel_finiteStore rel by blast


  have no_guess: "(invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S)"
    by (simp add: proof_state_rel_icgi rel)


  have "(the (localState S (ps_i PS))) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
    using i_def ls by auto

  have uip: "uid_is_private i S' uidv" 
    if "uid_is_private i S uidv"
      and "uidv \<notin> action_outputs action"
    for uidv
  proof (rule uid_is_private_step_s_same)
    show "S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'"
      using `S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'` .

    show "state_wellFormed S"
      by (simp add: \<open>state_wellFormed S\<close>)
    show "program_wellFormed (prog S)"
      using prog_wf by auto
    show "uid_is_private i S uidv"
      using that by simp
    show "uidv \<notin> action_outputs action"
      using that by simp
  qed

  hence uip': "uid_is_private (ps_i PS) S' uidv" 
    if "uid_is_private (ps_i PS) S uidv"
      and "uidv \<notin> action_outputs action"
    for uidv
    by (simp add: i_def that(1) that(2))




  show False
  proof (cases cmd)
    case (WaitLocalStep n)

    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitLocalStep)
      case (A i' ls f ok ls')

      have  "i' = i" using A by simp

      have f_impl[simp]: "f = toImpl"
        using `currentProc S i' \<triangleq> f` currentProc `i' = i` by auto

      from `f ls = LocalStep ok ls'` `localState S i' \<triangleq> ls`
      have toImpl: "toImpl (ps_store PS, ps_localKnown PS,  cmd \<bind> cmdCont) = LocalStep ok ls'"
        and ls_parts: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto

      from toImpl
      obtain ok' store' cmd'
        where c0: "n (ps_store PS) = (ok', store', cmd')"
          and c1: "ls' = (store', ps_localKnown PS, cmd' \<bind> cmdCont)"
          and c2: "ok = (ok' \<and> finite (dom store'))"
        by (auto simp add: WaitLocalStep split: prod.splits)


      have  cmd_def[simp]: "cmd = impl_language_loops.io.WaitLocalStep n"
        by (simp add: WaitLocalStep)
      have action_def: "action = ALocal Inv"
        using A(7) A(8) by auto

      have Inv: "Inv \<longleftrightarrow> (ok \<and> finite (dom (store')))"
        using A(8) c2 by blast
      have S'_def: "S' = S\<lparr>localState := localState S(i \<mapsto> (store', ps_localKnown PS, cmd' \<bind> cmdCont))\<rparr>"
        by (auto simp add: A(1) c1 `i' = i`)


      define PS' where "PS' \<equiv> PS\<lparr>
      ps_store := store'
    \<rparr>"

      show False
      proof (rule goal, intro exI conjI impI)
        show "proof_state_rel PS' S'" if Inv
          unfolding proof_state_rel_def 
        proof (intro conjI)

          from `Inv` and Inv
          have " ok" and  [simp]: "finite (dom store')"
            by auto

          show "state_wellFormed S'" using \<open>state_wellFormed S'\<close> .


          have old_priv: "uid_is_private (ps_i PS) S v" if "v \<in> ps_generatedLocalPrivate PS" for v
            by (simp add: proof_state_rel_uid_private rel that)


          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.  uid_is_private (ps_i PS') S' v"
          proof (auto simp add: uid_is_private_def PS'_def)
            fix v
            assume a0: "v \<in> ps_generatedLocalPrivate PS"


            show "new_unique_not_in_invocationOp (invocationOp S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)

            show "new_unique_not_in_calls (calls S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show " new_unique_not_in_calls_result (calls S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "new_unique_not_in_invocationRes (invocationRes S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "v \<in> knownIds S' \<Longrightarrow> False"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "generatedIds S' v \<triangleq> ps_i PS"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "new_unique_not_in_other_invocations (ps_i PS) S' v"
            proof (rule new_unique_not_in_other_invocations_maintained)
              show "new_unique_not_in_other_invocations (ps_i PS) S v"
                using old_priv[OF a0] by (auto simp add: uid_is_private_def)
              from step
              show "S ~~ (ps_i PS, action, Inv) \<leadsto>\<^sub>S S'"
                using `i = ps_i PS` by simp
            qed (simp add: action_def)+

          qed

          show "finite (dom (ps_store PS'))"
            by (auto simp add: PS'_def)


          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def)
            show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S'"
              using no_guess
            proof (fuzzy_rule show_invocation_cannot_guess_ids_step)
              show "S ~~ (ps_i PS, action) \<leadsto> S'"
                using step action_def step_s_to_step i_def by blast

              show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
                using action_def by simp
            qed
          qed



        qed ((insert proof_state_rel_facts[OF rel], (auto simp add: i_def S'_def PS'_def  split: option.splits)[1]); fail)+



        thus "step_io (invariant (prog S)) querySpec' PS cmd PS' cmd' Inv"
          by (auto simp add: step_io_def c0 c2 action_def Inv PS'_def show_proof_state_wellFormed)

        show "currentCommand S' i = cmd' \<bind> cmdCont"
          if c0: "Inv"
          by (auto simp add: S'_def)
      qed
    qed
  next
    case (WaitBeginAtomic n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitBeginAtomic)
      case (A i' ls f ls' t Sn Sf vis vis' )


      have Sf_def: "Sf = Sn
      \<lparr>transactionStatus := transactionStatus Sn(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin Sn(t \<mapsto> i'),
         currentTransaction := currentTransaction Sn(i' \<mapsto> t), localState := localState Sn(i' \<mapsto> ls'),
         visibleCalls := visibleCalls Sn(i' \<mapsto> vis')\<rparr>"
        using A by force

      have [simp]: "ps_localCalls PS = []"
        using A.currentTransaction_eq A.i_def i_def proof_state_rel_currentTx proof_state_rel_localCalls rel by fastforce 

      have [simp]: "i' = ps_i PS"
        using A.i_def i_def by blast

      have [simp]: "ls' = (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        using A.currentProc_eq A.f_eq A.localState_eq WaitBeginAtomic \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> toImpl by auto

      have Sn_toImpl[simp]: "currentProc Sn (ps_i PS) \<triangleq> toImpl"
        using toImpl A by auto




      define PS' where "PS' \<equiv> PS\<lparr>
             calls := calls Sn,
             happensBefore := happensBefore Sn,
             callOrigin := callOrigin Sn,
             transactionOrigin := transactionOrigin Sn,
             knownIds := knownIds Sn,
             invocationOp := invocationOp Sn,
             invocationRes := invocationRes Sn,
             ps_tx := Some t,
             ps_vis := vis'
          \<rparr>"


      have [simp]: "ps_i PS' = ps_i PS"
        by (simp add: PS'_def)


      show ?thesis
      proof (rule goal, intro exI conjI impI)

        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def `S' = Sf`
        proof (intro conjI)




          show "ps_generatedLocal PS' = {x. generatedIds Sf x \<triangleq> ps_i PS'}"
            apply (auto simp add: PS'_def A )
            using A.state_monotonicGrowth proof_state_rel_genLocal rel state_monotonicGrowth_generatedIds_same1 apply fastforce
            using A.state_monotonicGrowth proof_state_rel_facts(9) rel state_monotonicGrowth_generatedIds_same1 by fastforce

          from proof_state_rel_firstTx[OF rel]
          show "ps_firstTx PS' =
               (\<nexists>c tx. callOrigin Sf c \<triangleq> tx \<and> transactionOrigin Sf tx \<triangleq> ps_i PS' \<and> transactionStatus Sf tx \<triangleq> Committed)"
            apply (auto simp add: PS'_def A )
             apply (smt A \<open>state_wellFormed S\<close> i_def in_dom state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin_i state_wellFormed_ls_visibleCalls_callOrigin transactionConsistent_Committed wellFormed_callOrigin_dom wellFormed_visibleCallsSubsetCalls_h(2) wf_transactionConsistent_noTx)
            by (metis (no_types, lifting) A \<open>state_wellFormed S\<close> state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin state_monotonicGrowth_transactionStatus2 wellFormed_state_callOrigin_transactionStatus)


          show "\<forall>c. i_callOriginI PS' c \<triangleq> ps_i PS' \<longrightarrow> c \<in> ps_vis PS'"
            apply (auto simp add: PS'_def A  i_callOriginI_h_def split: option.splits)
            using A chooseSnapshot_def state_wellFormed_ls_visibleCalls_callOrigin by fastforce

          show "ps_generatedLocalPrivate PS' \<subseteq> ps_generatedLocal PS'"
            apply (auto simp add: PS'_def A )
            using proof_state_rel_localPrivateSub rel by blast

          from proof_state_rel_facts[OF rel]
          have uid_private: "uid_is_private (ps_i PS) S v"
            if "v \<in> ps_generatedLocalPrivate PS"
            for v
            using that by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
               uid_is_private (ps_i PS') Sf v"
          proof (rule ballI)
            fix v
            assume v_priv: "v \<in> ps_generatedLocalPrivate PS'"

            have  "uid_is_private i' S v"
            proof (fuzzy_rule uid_private)
              show "v \<in> ps_generatedLocalPrivate PS"
                using v_priv by (auto simp add: PS'_def)
              show "ps_i PS = i'" by simp
            qed


            have "uid_is_private i S' v"
            proof (rule uip)
              show "uid_is_private i S v"
                using `i = i'` \<open>uid_is_private i' S v\<close> by blast

              show "v \<notin> action_outputs action"
                using `action = ABeginAtomic t vis'` by simp
            qed


            from this
            show "uid_is_private (ps_i PS') Sf v"
              by (simp add: A(1) i_def)
          qed 

          have toImpl_ba: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = BeginAtomic (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
            using toImpl `f ls = BeginAtomic ls'` `currentProc S i' \<triangleq> f` `localState S i' \<triangleq> ls` i_def ls
            by auto

          have ls_Sf: "localState Sf (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
            by (auto simp add: A)



          show "ps_generatedLocal PS' \<subseteq> ps_localKnown PS'"
            using \<open>ps_generatedLocal PS \<subseteq> ps_localKnown PS\<close> PS'_def by auto


          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') Sf"
          proof (simp add: PS'_def A(4)[symmetric])

            have "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  S"
              by (simp add: no_guess)

            from `state_monotonicGrowth i' S Sn`
            obtain tr
              where "state_wellFormed S"
                and "S ~~ tr \<leadsto>* Sn" 
                and "\<forall>(i'',a)\<in>set tr. i'' \<noteq> i'"
                and "\<forall>i. (i, ACrash) \<notin> set tr"
              by (auto simp add: state_monotonicGrowth_def)


            from no_guess `S ~~ tr \<leadsto>* Sn`
            have "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  Sn"
            proof (rule show_invocation_cannot_guess_ids_steps_other)
              show "\<forall>(i', a)\<in>set tr. i' \<noteq> ps_i PS"
                using A(26) \<open>\<forall>(i'', a)\<in>set tr. i'' \<noteq> i'\<close> i_def by blast
            qed

            have ls_split: "ls = (fst ls, fst (snd ls), snd (snd ls))"
              by force

            have " Sn ~~ (ps_i PS, ABeginAtomic t vis' ) \<leadsto> S'"
              using A ls_split by (auto simp add: step.simps state_ext intro!: exI[where x=Sn] exI HOL.ext)

            from `invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  Sn`
              and `Sn ~~ (ps_i PS, ABeginAtomic t vis' ) \<leadsto> S'`
            show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) Sf "
            proof (fuzzy_rule show_invocation_cannot_guess_ids_step)
              show "ps_localKnown PS \<union> action_inputs (ABeginAtomic t vis') = ps_localKnown PS"
                by simp
              show "S' = Sf"
                by (simp add: A(1))
            qed
          qed

          show "prog Sf = ps_prog PS'"
            by (auto simp add: A.prog_eq \<open>prog S = ps_prog PS\<close> Sf_def PS'_def)



        qed ((insert A, (auto simp add: PS'_def sorted_by_empty)[1]); fail)+



        show "step_io (invariant (prog S)) querySpec' PS cmd PS' n Inv"
        proof (auto simp add: step_io_def `cmd = impl_language_loops.io.WaitBeginAtomic n`; (intro exI conjI)?)

          show "proof_state_wellFormed PS'"
          proof (rule show_proof_state_wellFormed)

            show "proof_state_rel PS' Sf"
              using A(1) \<open>proof_state_rel PS' S'\<close> by blast
          qed



          show "Inv"
            using A by simp


          have [simp]: "(transactionOrigin Sn)(t := None) = transactionOrigin Sn"
            using A(20) by auto



          have invContext_simp: "invariantContext.truncate (PS'\<lparr>transactionOrigin := ((transactionOrigin Sn)(t \<mapsto> ps_i PS))(t := None)\<rparr>)
          = invContext Sn"
            apply (auto simp add: invContextH_def PS'_def A invariantContext.defs committedCalls_allCommitted restrict_relation_def)
               apply (meson A(10) option.exhaust wellFormed_happensBefore_calls_l)
              apply (meson A(10) option.exhaust wellFormed_happensBefore_calls_r)
             apply (metis A(10) restrict_map_noop2 wellFormed_callOrigin_dom)
            by (smt A Collect_cong domD dom_def mem_Collect_eq option.distinct(1) restrict_map_noop2 transactionStatus.exhaust wf_transaction_status_iff_origin)

          show "invariant (prog S)
         (invariantContext.truncate
           (PS'\<lparr>transactionOrigin := (transactionOrigin Sn)\<rparr>))"
            unfolding invContext_simp
            using A.invariant A.prog_eq invContext_simp by auto


          show "transactionOrigin Sn t = None"
            by (simp add: A.transactionOrigin_eq)

          show "PS' = PS\<lparr>
            calls := calls Sn,
            happensBefore := happensBefore Sn, 
            callOrigin := callOrigin Sn,
            transactionOrigin := transactionOrigin Sn, 
            knownIds := knownIds Sn,
            invocationOp := invocationOp Sn,
            invocationRes := invocationRes Sn,
            ps_tx := Some t, 
            ps_vis := vis'\<rparr>"
            by (auto simp add: PS'_def i_def)

          show " ps_growing PS PS' t"
            unfolding ps_growing_def
          proof (intro exI conjI)
            show "proof_state_rel PS S" using rel .

            show "state_monotonicGrowth (ps_i PS) S (Sf\<lparr>transactionStatus := (transactionStatus Sf)(t := None),
                 transactionOrigin := (transactionOrigin Sf)(t := None),
                 currentTransaction := (currentTransaction Sf)(ps_i PS := None),
                 localState := (localState Sf)(ps_i PS := localState S (ps_i PS)),
                 visibleCalls := (visibleCalls Sf)(ps_i PS := visibleCalls S (ps_i PS))\<rparr>)"
              by (fuzzy_rule `state_monotonicGrowth i' S Sn`) (use A in \<open>auto simp add: state_ext Sf_def\<close>)

            show "proof_state_rel PS' Sf"
              unfolding proof_state_rel_def
              by (conj_one_by_one pre: \<open>proof_state_rel PS' S'\<close>[simplified proof_state_rel_def])
                (simp add: A PS'_def Sf_def)+
            show "ps_localCalls PS = []"
              using \<open>ps_localCalls PS = []\<close> by blast
            show " ps_tx PS = None"
              using A.currentTransaction_eq proof_state_rel_currentTx rel by fastforce
          qed (simp add: PS'_def; fail)+

          show "transactionOrigin PS t = None"
            using A(6) A.currentTransaction_eq \<open>state_wellFormed S\<close> proof_state_rel_currentTx proof_state_rel_txOrigin rel wf_transactionOrigin_and_status by fastforce


          have "currentTransaction S (ps_i PS) = None"
            using A(5) \<open>i' = ps_i PS\<close> by blast 

          have "currentTransaction S (ps_i PS) = ps_tx PS"
            using proof_state_rel_def rel by blast

          show "ps_tx PS = None"
            using `currentTransaction S i' = None` `i = i'`
              \<open>currentTransaction S (ps_i PS) = ps_tx PS\<close>
            by simp

          from proof_state_rel_facts[OF `proof_state_rel PS S`]
          have " transactionOrigin S = (case ps_tx PS of None \<Rightarrow> transactionOrigin PS | Some tx \<Rightarrow> transactionOrigin PS(tx \<mapsto> ps_i PS))" by simp

          from this
          show "\<forall>t'. t' \<noteq> t \<longrightarrow> transactionOrigin PS t' \<triangleq> ps_i PS = transactionOrigin Sn t' \<triangleq> ps_i PS"
            using ` \<forall>t. transactionOrigin S t \<triangleq> i' = transactionOrigin Sn t \<triangleq> i'`
            by (simp add: \<open>ps_tx PS = None\<close>)

          from `chooseSnapshot vis' vis Sn`
          show "chooseSnapshot_h vis' (ps_vis PS) (\<lambda>tx. Some Committed) (callOrigin Sn) (happensBefore Sn)"
            using `visibleCalls S i' \<triangleq> vis` \<open>visibleCalls S (ps_i PS) \<triangleq> (ps_vis PS \<union> set (ps_localCalls PS))\<close>
            by (auto simp add: chooseSnapshot_h_def)

          from `consistentSnapshot Sn vis'`
          show "consistentSnapshotI Sn vis'"
            by (auto simp add: consistentSnapshotH_def transactionConsistent_committed_def transactionConsistent_def)

          show "\<forall>c. callOrigin Sn c \<noteq> Some t"
            by (simp add: A(24))


        qed

        show "currentCommand S' i = n \<bind> cmdCont"
          by (auto simp add: A)

      qed

    qed
  next
    case (WaitEndAtomic n)

    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitEndAtomic)
      case (A i' ls f ls' t S'' valid)


      have  "i' = i" using A by simp
      hence "i' = ps_i PS"
        using i_def by blast


      have f_impl[simp]: "f = toImpl"
        using `currentProc S i' \<triangleq> f` currentProc `i' = i` by auto

      from `f ls = EndAtomic ls'` `localState S i' \<triangleq> ls`
      have toImpl: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = EndAtomic ls'"
        and ls_parts: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto




      from toImpl
      have ls'_def: "ls' = (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        by (auto simp add: WaitEndAtomic)

      have S''_def: "S'' = S
    \<lparr>localState := localState S(i' \<mapsto> ls'), currentTransaction := (currentTransaction S)(i' := None),
       transactionStatus := transactionStatus S(t \<mapsto> Committed)\<rparr>"
        using A by auto

      have [simp]: "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        by (auto simp add: `S' = S''` S''_def `i' = ps_i PS` ls'_def)


      define PS' where "PS' \<equiv> PS\<lparr>
        happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
        callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
        transactionOrigin := transactionOrigin PS(t \<mapsto> ps_i PS),
        ps_tx := None,
        ps_localCalls := [],
        ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
        ps_firstTx := ps_firstTx PS \<and> ps_localCalls PS = []
      \<rparr>"


      show False
      proof (rule goal, intro exI conjI impI)

        show "currentCommand S' i = n \<bind> cmdCont"
          by (simp add: S''_def `S' = S''` `i = i'` ls'_def)

        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)
          show "state_wellFormed S'"
            by (simp add: \<open>state_wellFormed S'\<close>)

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
            by (simp add: PS'_def)

          have [simp]: "ps_tx PS \<triangleq> t"
            using A.currentTransaction_eq \<open>i' = ps_i PS\<close> proof_state_rel_currentTx rel by fastforce

          have no_other_uncommitted: "transactionStatus S tx \<noteq> Some Uncommitted" if "t \<noteq> tx" for tx

            by (rule proof_state_rel_noUncommitted[OF rel, rule_format], simp add: that)




          show "\<forall>tx'. ps_tx PS' \<noteq> Some tx' \<longrightarrow> transactionStatus S' tx' \<noteq> Some Uncommitted"
            by (simp add: PS'_def  `S' = S''` S''_def no_other_uncommitted)

          from proof_state_rel_firstTx[OF rel]
          show "ps_firstTx PS' =
           (\<nexists>c tx. callOrigin S' c \<triangleq> tx \<and> transactionOrigin S' tx \<triangleq> ps_i PS' \<and> transactionStatus S' tx \<triangleq> Committed)"
            using proof_state_rel_localCalls[OF rel]
            apply (auto simp add: PS'_def  `S' = S''` S''_def)
            using A(5) \<open>i' = ps_i PS\<close> \<open>state_wellFormed S\<close> state_wellFormed_current_transaction_origin by blast

          show "\<forall>c. i_callOriginI PS' c \<triangleq> ps_i PS' \<longrightarrow> c \<in> ps_vis PS'"
            apply (auto simp add: PS'_def)
            by (smt \<open>ps_tx PS \<triangleq> t\<close> i_callOriginI_h_update_to2 i_callOriginI_h_update_to4 mem_Collect_eq option.simps(5) proof_state_rel_callOrigin proof_state_rel_localCalls proof_state_rel_see_my_updates rel)


          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.  uid_is_private (ps_i PS') S' v"

          proof (auto simp add: PS'_def )
            fix v
            assume a0: "v \<in> ps_generatedLocalPrivate PS"

            have "uid_is_private (ps_i PS) S v"
              using a0 proof_state_rel_uid_private rel by blast

            show "uid_is_private (ps_i PS) S' v"
            proof (fuzzy_rule uip)
              show "uid_is_private i S v"
                by (simp add: \<open>uid_is_private (ps_i PS) S v\<close> i_def)
              show "v \<notin> action_outputs action"
                by (simp add: A(11)) 
              show "i = ps_i PS"
                by (simp add: i_def) 
            qed
          qed

          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(11) i_def local.step step_s_to_step by blast
            show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
              using `action = AEndAtomic` by simp
          qed

          from proof_state_rel_txOrigin[OF rel]
          show "transactionOrigin S' =
              (case ps_tx PS' of None \<Rightarrow> transactionOrigin PS' | Some tx \<Rightarrow> transactionOrigin PS'(tx \<mapsto> ps_i PS'))"
            by (auto simp add: PS'_def A.S'_def S''_def)

        qed ((insert proof_state_rel_facts[OF rel], (auto simp add: sorted_by_empty i_def S''_def PS'_def `S' = S''` `i = i'` `i' = ps_i PS`  split: option.splits)[1]); fail)+

        have "\<And>t. transactionStatus S'' t \<noteq> Some Uncommitted"
          apply (auto simp add: S''_def)
          by (metis A.currentTransaction_eq \<open>state_wellFormed S\<close> option.inject proof_state_rel_noUncommitted rel wellFormed_currentTransaction_unique_h(2))



        have committed_all: "committedCallsH (callOrigin S) (transactionStatus S(t \<mapsto> Committed))
          = dom (calls S)"
          apply (auto simp add: committedCallsH_def isCommittedH_def)
          using \<open>state_wellFormed S\<close> wellFormed_callOrigin_dom apply fastforce
            apply (simp add: \<open>state_wellFormed S\<close> wellFormed_callOrigin_dom2)
          using A(5) \<open>state_wellFormed S\<close> wellFormed_currentTransaction_unique_h(2) apply fastforce
          using \<open>state_wellFormed S\<close> not_None_eq not_uncommitted_cases rel wellFormed_callOrigin_dom3 wellFormed_currentTransaction_unique_h(2) wf_no_transactionStatus_origin_for_nothing 
          by (smt A.currentTransaction_eq proof_state_rel_noUncommitted)



        have context_Same: "invariantContext.truncate PS' = invContext S''"
          apply (auto simp add: invContext_same_allCommitted'[OF `state_wellFormed S''` `\<And>t. transactionStatus S'' t \<noteq> Some Uncommitted`])
          using A.currentTransaction_eq \<open>i' = ps_i PS\<close> proof_state_rel_currentTx rel
          by (auto simp add: PS'_def S''_def invariantContext.defs proof_state_rel_facts[OF rel]  split: option.splits)




        have prog_same: "prog S'' = prog S"
          using A(1) local.step steps_s_single unchangedProg by blast

        have inv: "Inv  \<longleftrightarrow> invariant (prog S) (invariantContext.truncate PS')"
          by (simp add: context_Same `Inv = valid` `valid = invariant_all S''` prog_same)


        have tx: "ps_tx PS \<triangleq> t"
          using A.currentTransaction_eq \<open>i' = ps_i PS\<close> proof_state_rel_currentTx rel by fastforce 


        show "step_io (invariant (prog S)) querySpec' PS cmd PS' n Inv"
        proof (auto simp add: step_io_def WaitEndAtomic)
          show "Inv \<Longrightarrow> proof_state_wellFormed PS'"
            using show_proof_state_wellFormed[OF `proof_state_rel PS' S'`].
          show "Inv \<Longrightarrow> invariant (prog S) (invariantContext.truncate PS')"
            using inv by simp
          show "invariant (prog S) (invariantContext.truncate PS') \<Longrightarrow> Inv"
            using inv by simp
          show "PS' =
            ps_tx_update Map.empty
             (PS\<lparr>happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
                   callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
                   transactionOrigin := transactionOrigin PS(the (ps_tx PS) \<mapsto> ps_i PS)\<rparr>)
            \<lparr>ps_localCalls := [], ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
               ps_firstTx := ps_firstTx PS \<and> ps_localCalls PS = []\<rparr>"
            by (auto simp add: proof_state_ext PS'_def tx)
        qed
      qed
    qed


  next
    case (WaitNewId P n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitNewId)
      case (A i' ls f ls' uid uidv ls'')

      have S'_def: "S' = S\<lparr>localState := localState S(i' \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i')\<rparr>"
        using A by simp

      have S'_wf: "state_wellFormed S'"
        by (simp add: \<open>state_wellFormed S'\<close>)

      have "i' = ps_i PS"
        using A(10) i_def by auto


      have ls''_def: "ls'' = (ps_store PS, ps_localKnown PS \<union> uniqueIds uidv, n uidv \<bind> cmdCont)"
        by (smt A(10) A(2) A(3) A(4) A(7) WaitNewId i_def impl_language_loops.bind.simps(4) toImpl.simps(4) localAction.inject(4) ls option.sel option.simps(3) toImpl)

      define cmd' where "cmd' \<equiv> n uidv"


      define PS' where "PS' = PS\<lparr> 
          ps_localKnown := ps_localKnown PS \<union> {uid},
          ps_generatedLocal := ps_generatedLocal PS \<union> {uid},
          ps_generatedLocalPrivate := ps_generatedLocalPrivate PS \<union> {uid}
        \<rparr>"




      show False
      proof (rule goal, intro exI conjI impI)
        show "currentCommand S' i = cmd' \<bind> cmdCont"
          by (simp add: S'_def ls''_def cmd'_def `i = i'`)


        have uid_priv: "uid_is_private (ps_i PS) S' uid"
          unfolding uid_is_private_def
        proof (intro conjI)
          show "new_unique_not_in_invocationOp (invocationOp S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_invocationOp_def prog_wf wf_onlyGeneratedIdsInInvocationOps by (auto simp add: A, blast)
          show "new_unique_not_in_calls (calls S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_calls_def prog_wf wf_onlyGeneratedIdsInCalls by (auto simp add: A, blast)
          show "new_unique_not_in_calls_result (calls S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_calls_result_def prog_wf wf_onlyGeneratedIdsInCallResults by (auto simp add: A, blast)
          show "new_unique_not_in_invocationRes (invocationRes S') uid"
            apply (auto simp add: A)
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_invocationRes_def prog_wf wf_onlyGeneratedIdsInInvocationRes by blast
          show "uid \<notin> knownIds S'"
            apply (auto simp add: A)
            using A(5) A(8) \<open>state_wellFormed S\<close> prog_wf wf_onlyGeneratedIdsInKnownIds by blast
          show "generatedIds S' uid \<triangleq> ps_i PS"
            using \<open>i' = ps_i PS\<close> by (auto simp add: A)
          have "new_unique_not_in_other_invocations (ps_i PS) S uid"
          proof (rule wf_invocation_cannot_guess_ids_not_generated)
            show "state_wellFormed S"
              using \<open>state_wellFormed S\<close> by auto
            show "program_wellFormed (prog S)"
              by (simp add: prog_wf)
            show "generatedIds S uid = None"
              by (simp add: A(5))
          qed
          thus "new_unique_not_in_other_invocations (ps_i PS) S' uid"
            using A(11) i_def local.step new_unique_not_in_other_invocations_maintained by blast
        qed


        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)
          show "state_wellFormed S'"
            using S'_wf by simp

          show "ps_generatedLocal PS' = {x. generatedIds S' x \<triangleq> ps_i PS'}"
            by (auto simp add: PS'_def S'_def `i' = ps_i PS` proof_state_rel_genLocal[OF rel])

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
            by (auto simp add: PS'_def S'_def `i' = ps_i PS` ls''_def `uniqueIds uidv = {uid}`)





          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
           uid_is_private (ps_i PS') S' v"
          proof (auto simp add: PS'_def)
            show "uid_is_private (ps_i PS) S' uid"
              using uid_priv by blast
            show "uid_is_private (ps_i PS) S' v" if "v \<in> ps_generatedLocalPrivate PS" for v
              by (simp add: A.action_def proof_state_rel_uid_private rel that uip')
          qed



          have ls''_def: "ls'' = (the (localState S' (ps_i PS)))"
            by (auto simp add: S'_def \<open>i' = ps_i PS\<close>)

          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(11) i_def local.step step_s_to_step by blast
            show "ps_localKnown PS \<union> action_inputs action = insert uid (ps_localKnown PS)"
              using `action = ANewId uidv` `uniqueIds uidv = {uid}` by auto
          qed




        qed ((insert proof_state_rel_facts[OF rel], (auto simp add: i_def  S'_def PS'_def  split: option.splits)[1]); fail)+



        show "step_io (invariant (prog S)) querySpec' PS cmd PS' cmd' Inv"
        proof (auto simp add: step_io_def WaitNewId; (intro exI conjI)?)

          from `f ls = NewId ls'`
          have "toImpl ls = NewId ls'"
            using A(3) \<open>i' = ps_i PS\<close> toImpl by auto


          have ls_def: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
            using A(10) A(2) ls by auto



          show "cmd' = n uidv"
            using cmd'_def by simp




          show "uniqueIds uidv = {uid}"
            by (simp add: A(6))

          show "uid \<notin> ps_generatedLocal PS"
            using A.generatedIds_eq proof_state_rel_genLocal rel by force

          from uid_is_private'_implies[OF uid_priv]
          have h: " uid_is_private' (ps_i PS) (calls S') (invocationOp S') (invocationRes S') (knownIds S') uid" .

          have "uid_is_private' (ps_i PS) (calls PS) (invocationOp PS) (invocationRes PS) (knownIds PS) uid"
            using h
            by (auto simp add: S'_def  proof_state_rel_facts[OF rel])

          thus "uid_fresh uid PS"
            by (auto simp add: uid_fresh_def)

          show "PS' = PS
                \<lparr>  ps_localKnown := insert uid (ps_localKnown PS),
                   ps_generatedLocal := insert uid (ps_generatedLocal PS),
                   ps_generatedLocalPrivate := insert uid (ps_generatedLocalPrivate PS)\<rparr>"
            by (auto simp add: PS'_def)
          show "Inv"
            by (simp add: A(12))

          show "P uidv"
            using A(10) A(3) A(4) A(7) WaitNewId currentProc ls_def option.inject by fastforce

          show "Inv \<Longrightarrow> proof_state_wellFormed PS'"
            using show_proof_state_wellFormed[OF `proof_state_rel PS' S'`] by simp

        qed
      qed
    qed

  next
    case (WaitDbOperation oper n)

    show False 
    proof (cases "\<exists>c Op res. action = ADbOp c Op res")
      case False
      hence a: "action \<noteq> ADbOp c Op res" for c Op res
        by blast

\<comment> \<open>TODO move to utils\<close>
      have if_simp1: "((if c then x else y) = z) \<longleftrightarrow> (if c then x = z else y = z)" for c and  x y z :: "('ls, 'operation, 'any) localAction"
        by auto

      have if_simp2: "(if c then False else y) \<longleftrightarrow> \<not>c \<and> y" for c y
        by auto


      show False
        apply (rule step_s.cases[OF step];     remove_first_equality)
              apply (insert a cmd_prefix )
              apply (auto simp add: WaitDbOperation if_simp1  if_simp2 split: prod.splits cong: if_cong)
        apply (rule ccontr)
      proof (fuzzy_goal_cases A)
        case (A x)

        define PS' where "PS' = PS"

        show False
        proof (rule goal, intro exI conjI impI)
          show "step_io (invariant (prog S)) querySpec' PS cmd PS' cmd Inv"
            using `cmd = impl_language_loops.io.WaitDbOperation oper n`
              `x \<in> uniqueIds oper` `x \<notin> ps_localKnown PS`
            by (auto simp add: step_io_def `\<not> Inv` PS'_def)

        qed (simp add: `\<not>Inv`)+
      qed
    next
      case True
      from this
      obtain c Op res where "action = ADbOp c Op res"
        by blast

      have validUids: "uniqueIds oper \<subseteq> ps_localKnown PS"
        using step `action = ADbOp c Op res` `cmd = impl_language_loops.io.WaitDbOperation oper n`
        by (auto simp add: step_s.simps split: if_splits)


      show False
      proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitDbOperation validUids)
        case (A i' ls f Op ls' t c res vis)


        have [simp]: "i = i'" using A by simp
        have [simp]: "ps_i PS = i'"
          using i_def by auto 

        have Inv
          by (simp add: A(12))

        have S'_def: "S' = S
        \<lparr>localState := localState S(i' \<mapsto> ls' res), calls := calls S(c \<mapsto> Call Op res),
           callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(i' \<mapsto> vis \<union> {c}),
           happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>"
          using A by simp

        have [simp]: "oper = Op"
          using A WaitDbOperation i_def ls toImpl `uniqueIds oper \<subseteq> ps_localKnown PS` by auto


        define PS' where "PS' \<equiv> PS\<lparr> 
            ps_localKnown := ps_localKnown PS \<union> uniqueIds res,
            ps_generatedLocalPrivate := ps_generatedLocalPrivate PS - uniqueIds Op,
            calls := (calls PS)(c \<mapsto> Call oper res),
            ps_localCalls := ps_localCalls PS @ [c]
      \<rparr>"

        show False
        proof (rule goal, intro exI conjI impI)

          show "currentCommand S' i = n res \<bind> cmdCont"
            apply (simp add: S'_def)
            using A(2) A(3) A(4) WaitDbOperation i_def ls toImpl validUids by auto

          have vis_def: "vis = ps_vis PS \<union> set (ps_localCalls PS)"
            by (metis A.i_def A.visibleCalls_eq i_def option.sel proof_state_rel_facts(12) rel)

          have t_def: "t = the (ps_tx PS)"
            by (metis A.currentTransaction_eq \<open>ps_i PS = i'\<close> option.sel proof_state_rel_currentTx rel)

          have ps_tx: "ps_tx PS \<triangleq> t"
            by (metis A.currentTransaction_eq A.i_def i_def proof_state_rel_currentTx rel)



          show "proof_state_rel PS' S'"
            unfolding proof_state_rel_def 
          proof (intro conjI)

            show "state_wellFormed S'"
              by (simp add: \<open>state_wellFormed S'\<close>)

            show "happensBefore S' = updateHb (happensBefore PS') (ps_vis PS') (ps_localCalls PS')"
              by (auto simp add: vis_def proof_state_rel_hb[OF rel] updateHb_simp1 S'_def PS'_def in_sequence_append in_sequence_cons updateHb_cases updateHb_chain)


            show "callOrigin S' = map_update_all (callOrigin PS') (ps_localCalls PS') (the (ps_tx PS'))"
              by (auto simp add: S'_def PS'_def map_update_all_get t_def proof_state_rel_callOrigin[OF rel] intro!: HOL.ext)


            show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
              using A(2) A(3) A(4) WaitDbOperation ls toImpl validUids by (auto simp add: S'_def PS'_def)

            show "visibleCalls S' (ps_i PS') \<triangleq> (ps_vis PS' \<union> set (ps_localCalls PS'))"
              by (auto simp add: S'_def PS'_def vis_def)

            show "case ps_tx PS' of None \<Rightarrow> ps_localCalls PS' = [] | Some tx' \<Rightarrow> set (ps_localCalls PS') = {c. callOrigin S' c \<triangleq> tx'}"
              apply (auto simp add: proof_state_rel_callOrigin[OF rel] map_update_all_get ps_tx S'_def PS'_def split: option.splits)
              using proof_state_rel_localCalls[OF rel]
              by (metis (mono_tags, lifting) map_update_all_get mem_Collect_eq option.simps(5) proof_state_rel_callOrigin ps_tx rel)

            have sorted: "sorted_by (happensBefore S) (ps_localCalls PS)"
              by (simp add: proof_state_rel_localCallsSorted rel)

            have "c \<notin> set (ps_localCalls PS)"
              using A(6) A(8) \<open>state_wellFormed S\<close> vis_def wellFormed_visibleCallsSubsetCalls2 by auto


            show "sorted_by (happensBefore S') (ps_localCalls PS')"
            proof (auto simp add: S'_def PS'_def sorted_by_append_iff sorted_by_single)

              show "sorted_by (happensBefore S \<union> vis \<times> {c}) (ps_localCalls PS)"
                using sorted \<open>c \<notin> set (ps_localCalls PS)\<close> 
                by (auto simp add: sorted_by_def)
              show "\<And>x. \<lbrakk>x \<in> set (ps_localCalls PS); (c, x) \<in> happensBefore S\<rbrakk> \<Longrightarrow> False"
                using A(6) \<open>state_wellFormed S\<close> wellFormed_happensBefore_calls_l by blast
              show "\<lbrakk>c \<in> set (ps_localCalls PS); c \<in> vis\<rbrakk> \<Longrightarrow> False"
                using \<open>c \<notin> set (ps_localCalls PS)\<close> by blast
            qed

            have "c \<notin> ps_vis PS"
              using A(6) A(8) \<open>state_wellFormed S\<close> vis_def wellFormed_visibleCallsSubsetCalls2 by auto


            show "ps_vis PS' \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_vis_localCalls_disjoint[OF rel]
              by (auto simp add: PS'_def `c \<notin> ps_vis PS`)

            have co_c: "callOrigin PS c = None"
              by (metis A.calls_eq \<open>state_wellFormed S\<close> map_update_all_None proof_state_rel_callOrigin rel wellFormed_callOrigin_dom3)


            show "dom (callOrigin PS') \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_callOrigin_localCalls_disjoint[OF rel]
              by (auto simp add: PS'_def co_c)

            have co_hb: "c \<notin> Field (happensBefore PS)"
              by (metis A.calls_eq Field_Un UnCI \<open>state_wellFormed S\<close> proof_state_rel_hb rel updateHb_simp_split wellFormed_happensBefore_Field)


            show "Field (happensBefore PS') \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_happensBefore_localCalls_disjoint[OF rel]
              by (auto simp add: PS'_def co_hb)

            show "distinct (ps_localCalls PS')"
              using proof_state_rel_localCalls_distinct[OF rel]
              by (auto simp add: PS'_def \<open>c \<notin> set (ps_localCalls PS)\<close> )

            show "ps_firstTx PS' =
            (\<nexists>c tx. callOrigin S' c \<triangleq> tx \<and> transactionOrigin S' tx \<triangleq> ps_i PS' \<and> transactionStatus S' tx \<triangleq> Committed)"
              apply ( simp add: PS'_def S'_def)
              apply safe
              using A(5) \<open>state_wellFormed S\<close> not_uncommitted_cases wellFormed_currentTransactionUncommitted apply blast
              using \<open>ps_i PS = i'\<close> proof_state_rel_firstTx rel apply blast
              by (metis A.calls_eq \<open>ps_i PS = i'\<close> \<open>state_wellFormed S\<close> option.distinct(1) proof_state_rel_firstTx rel wellFormed_callOrigin_dom3)


            have  prog_wf': "program_wellFormed (prog S')"
              by (metis local.step prog_wf steps_s_empty steps_s_step unchangedProg)

            hence "invocations_cannot_guess_ids (prog S')" 
              and "queries_cannot_guess_ids (querySpec (prog S'))"
              by (auto simp add: program_wellFormed_def)


            have toImpl_db: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = DbOperation Op ls'"
              using toImpl `currentProc S i' \<triangleq> f` `f ls = DbOperation Op ls'` `localState S i' \<triangleq> ls` ls by auto



            have "localState S' i' \<triangleq> ls' res" 
              by (auto simp add: S'_def )


            show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
            proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
              show "S ~~ (i', action) \<leadsto> S'"
                using A(10) A(11) local.step step_s_to_step by blast
              show "ps_i PS = i'"
                by simp
              show "action_inputs action = uniqueIds res"
                using ` action = ADbOp c Op res` by auto
            qed

            from use_invocation_cannot_guess_ids_return[OF no_guess]
            have "uniqueIds Op \<subseteq> ps_localKnown PS"
              by (metis A(11) action.distinct(33) action.distinct(53) i_def local.step no_guess step_s_to_step use_invocation_cannot_guess_ids_dbop)

            from prog_wf
            have "query_cannot_guess_ids (uniqueIds opr) (querySpec (prog S) opr)" for opr
              by (auto simp add: program_wellFormed_def queries_cannot_guess_ids_def)

            hence qcgi: "query_cannot_guess_ids (uniqueIds Op) (querySpec (prog S) Op)" .

            from qcgi[simplified query_cannot_guess_ids_def, rule_format, OF `querySpec (prog S) Op (getContext S i') res`]
            have " uniqueIds res
              \<subseteq> uniqueIds Op \<union> \<Union> {x. \<exists>cId c. x = uniqueIds (call_operation c) \<and> calls (getContext S i') cId \<triangleq> c}"
              .

            hence uniqueIdsRes: "\<exists>cId c. calls (getContext S i') cId \<triangleq> c \<and> x \<in> uniqueIds (call_operation c)" 
              if "x \<in> uniqueIds res" 
                and "x \<notin> uniqueIds Op"
              for x
              using that
              using A(7) qcgi by fastforce 


            show " \<forall>v\<in>ps_generatedLocalPrivate PS'.
            uid_is_private (ps_i PS') S' v"
              using A(10) A(11) action_outputs.simps(5) i_def proof_state_rel_def rel uip by (auto simp add: PS'_def, blast)

            show "transactionOrigin S' =
               (case ps_tx PS' of None \<Rightarrow> transactionOrigin PS' | Some tx \<Rightarrow> transactionOrigin PS'(tx \<mapsto> ps_i PS'))"
              apply (auto simp add: PS'_def S'_def ps_tx split: option.splits)
              by (metis A.i_def i_def option.case_eq_if option.distinct(1) option.sel proof_state_rel_def ps_tx rel)


          qed ((insert proof_state_rel_facts[OF rel], (auto simp add: PS'_def S'_def sorted_by_empty)[1]); fail)+


          show "step_io (invariant (prog S)) querySpec' PS cmd PS' (n res) Inv"
          proof (auto simp add: step_io_def WaitDbOperation; (intro exI conjI)?)

            show "ps_tx PS \<triangleq> t"
              by (simp add: ps_tx)

            show "calls PS c = None"
              using A.calls_eq proof_state_rel_calls rel by fastforce

            have  vis: "visibleCalls S i' \<triangleq> (ps_vis PS \<union> set (ps_localCalls PS))"
              using A(8) vis_def by blast

            have ctxt_same: "(getContextH (calls S) (happensBefore S) (Some (ps_vis PS \<union> set (ps_localCalls PS))))
            = (getContextH (calls PS) (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
                  (Some (ps_vis PS \<union> set (ps_localCalls PS))))"
              by (auto simp add: getContextH_def proof_state_rel_facts[OF rel])

            from `querySpec (prog S) Op (getContext S i') res`
            have "querySpec (prog S) Op
         (getContextH (calls PS) (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
           (Some (ps_vis PS \<union> set (ps_localCalls PS))))
           res" 
              by (auto simp add: vis ctxt_same)

            show "toplevel_spec querySpec' (current_operationContext PS) (current_vis PS) Op res"

              sorry


            show "uniqueIds Op \<subseteq> ps_localKnown PS"
              using validUids by auto

            show "Inv \<Longrightarrow> proof_state_wellFormed PS'"
              using show_proof_state_wellFormed[OF `proof_state_rel PS' S'`] by simp

          qed (auto simp add: PS'_def \<open>Inv\<close>)
        qed
      qed
    qed
  next
    case (WaitReturn n)
    with cm_no_return 
    show False
      by auto
  next
    case (Loop init body n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: Loop)
      case (A i' ls f ok ls')

      have S'_def: "S' = S\<lparr>localState := localState S(i' \<mapsto> ls')\<rparr>" using A by simp

      have "Inv"
        using A(2) A(3) A(4) A(6) A(8) Loop \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> i_def toImpl by auto


      show False
      proof (rule goal, intro exI conjI impI)

        have [simp]: "ps_i PS = i'"
          using A(6) i_def by auto




        have toImpl_ls: "toImpl ls = LocalStep ok ls'"
          using `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def)

        have toImpl1: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = LocalStep ok ls'"
          using A(2) \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> toImpl_ls by auto


        have ls_S'1: "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, 
            loop_body_from_V body init \<bind> (\<lambda>r. case r of Break x \<Rightarrow> n x \<bind> cmdCont | Continue x \<Rightarrow> Loop x body n \<bind> cmdCont))"

          using \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def )



        have ls_S': "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, 
                (loop_body_from_V body init \<bind>io (\<lambda>r. case r of Break x \<Rightarrow> n x | Continue x \<Rightarrow> Loop x body n)) \<bind>io cmdCont)" (is ?g)
        proof -
          have "(\<lambda>r. case r of Continue x \<Rightarrow> Loop x body n \<bind> cmdCont | Break x \<Rightarrow> n x \<bind> cmdCont)
              = (\<lambda>a. (case a of Continue x \<Rightarrow> Loop x body n | Break x \<Rightarrow> n x) \<bind> cmdCont)"
            by (auto split: loopResult.splits)

          with ls_S'1
          show ?g
            by auto
        qed


        show "proof_state_rel PS S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)

          show "state_wellFormed S'"
            by (simp add: \<open>state_wellFormed S'\<close>)

          show " \<exists>ps_ls. localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ps_ls)"
            using ls_S' by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS. uid_is_private (ps_i PS) S' v"

            using A.action_def proof_state_rel_uid_private rel uip' by fastforce

          show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S'"
          proof (use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(7) i_def local.step step_s_to_step by blast

            show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
              using ` action = ALocal ok` by auto
          qed


        qed ((insert proof_state_rel_facts[OF rel], (auto simp add: i_def S'_def   split: option.splits)[1]); fail)+


        show "currentCommand S' i = (loop_body_from_V body init \<bind>io (\<lambda>r. case r of Continue x \<Rightarrow> Loop x body n | Break x \<Rightarrow> n x)) \<bind>io cmdCont"
          using i_def ls_S' by auto


        show "step_io (invariant (prog S)) querySpec' PS cmd PS
         (loop_body_from_V body init \<bind> (\<lambda>r. case r of Continue x \<Rightarrow> Loop x body n | Break x \<Rightarrow> n x)) Inv"
          using `proof_state_rel PS S`
          by (auto simp add: step_io_def Loop `Inv` show_proof_state_wellFormed)

      qed
    qed
  qed
qed

lemma step_io_same_i:
  assumes "step_io progInv qrySpec S cmd S' cmd' Inv"
  shows "ps_i S' = ps_i S"
  using assms  by ( auto simp add: step_io_def split: io.splits if_splits)


definition proof_state_wellFormed' :: "('proc::valueType, 'any::valueType, 'operation::valueType) proof_state \<Rightarrow> bool" where 
  "proof_state_wellFormed' S \<equiv> 
    finite (dom (ps_store S))
   \<and> (ps_tx S = None \<longrightarrow> ps_localCalls S = [])
   \<and> Field (happensBefore S) \<subseteq> dom (calls S) - set (ps_localCalls S)
   \<and> ps_vis S \<subseteq> dom (calls S)
   \<and> set (ps_localCalls S) \<subseteq> dom (calls S)
"

lemma proof_state_wellFormed'_finite_store:
  assumes "proof_state_wellFormed' S"
  shows "finite (dom (ps_store S))"
  using assms unfolding proof_state_wellFormed'_def 
  by auto

lemma proof_state_wellFormed'_localCalls:
  assumes "proof_state_wellFormed' S"
    and "ps_tx S = None"
  shows "ps_localCalls S = []"
  using assms unfolding proof_state_wellFormed'_def 
  by auto

lemma proof_state_wellFormed'_happensBefore_subset_calls:
  assumes "proof_state_wellFormed' S"
  shows "Field (happensBefore S) \<subseteq> dom (calls S)"
  using assms unfolding proof_state_wellFormed'_def 
  by auto


lemma proof_state_wellFormed'_disjoint_happensBefore_localCalls:
  assumes "proof_state_wellFormed' S"
  shows "Field (happensBefore S) \<inter> set (ps_localCalls S) = {}"
  using assms unfolding proof_state_wellFormed'_def 
  by auto

lemma proof_state_wellFormed'_vis_subset_calls:
  assumes "proof_state_wellFormed' S"
  shows "ps_vis S \<subseteq> dom (calls S)"
  using assms unfolding proof_state_wellFormed'_def 
  by auto

lemma proof_state_wellFormed'_vis_subset_calls':
  assumes "proof_state_wellFormed' S"
  shows "c \<in> ps_vis S \<Longrightarrow> \<exists>y. calls S c \<triangleq> y"
  using assms unfolding proof_state_wellFormed'_def 
  by auto


lemma proof_state_wellFormed'_localCalls_subset_calls:
  assumes "proof_state_wellFormed' S"
  shows "set (ps_localCalls S) \<subseteq> dom (calls S)"
  using assms unfolding proof_state_wellFormed'_def 
  by auto

lemma proof_state_wellFormed'_localCalls_subset_calls':
  assumes "proof_state_wellFormed' S"
  shows "c \<in> set (ps_localCalls S) \<Longrightarrow> \<exists>y. calls S c \<triangleq> y"
  using assms unfolding proof_state_wellFormed'_def 
  by auto



lemma proof_state_wellFormed_finite_store:
  assumes "proof_state_wellFormed S"
  shows "finite (dom (ps_store S))"
  using assms unfolding proof_state_wellFormed_def
  using proof_state_rel_finiteStore by blast

lemma proof_state_wellFormed_localCalls:
  assumes "proof_state_wellFormed S"
    and "ps_tx S = None"
  shows "ps_localCalls S = []"
  using assms unfolding proof_state_wellFormed_def
  using proof_state_rel_localCalls by fastforce

lemma proof_state_wellFormed_happensBefore_subset_calls:
  assumes "proof_state_wellFormed S"
  shows "Field (happensBefore S) \<subseteq> dom (calls S)"
proof -
  from assms obtain S' where rel: "proof_state_rel S S'" 
    unfolding proof_state_wellFormed_def by blast

  hence "state_wellFormed S'"
    using proof_state_rel_def by blast

  have "Field (happensBefore S') \<subseteq> dom (calls S')"
    by (meson \<open>state_wellFormed S'\<close> domIff subsetI wellFormed_happensBefore_Field)

  thus ?thesis
    apply (auto simp add: proof_state_rel_facts[OF rel])
    by (metis (no_types, hide_lams) Field_Un Un_iff  domIff not_Some_eq  subsetD updateHb_simp_split)
qed


lemma proof_state_wellFormed_disjoint_happensBefore_localCalls:
  assumes "proof_state_wellFormed S"
  shows "Field (happensBefore S) \<inter> set (ps_localCalls S) = {}"
  using assms 
  using proof_state_rel_happensBefore_localCalls_disjoint proof_state_wellFormed_def by blast


lemma proof_state_wellFormed_vis_subset_calls:
  assumes "proof_state_wellFormed S"
  shows "ps_vis S \<subseteq> dom (calls S)"
proof -
  from assms obtain S' where rel: "proof_state_rel S S'" 
    unfolding proof_state_wellFormed_def by blast

  hence "state_wellFormed S'"
    using proof_state_rel_def by blast

  from proof_state_rel_facts[OF rel]
  have "visibleCalls S' (ps_i S) \<triangleq> (ps_vis S \<union> set (ps_localCalls S))" 
    by simp


  thus ?thesis
    using \<open>calls S' = calls S\<close> \<open>state_wellFormed S'\<close>  wellFormed_visibleCallsSubsetCalls_h(2) by fastforce
qed


lemma proof_state_wellFormed_vis_subset_calls':
  assumes "proof_state_wellFormed S"
  shows "c \<in> ps_vis S \<Longrightarrow> \<exists>y. calls S c \<triangleq> y"
  using assms 
  by (meson in_dom proof_state_wellFormed_vis_subset_calls)


lemma proof_state_wellFormed_localCalls_subset_calls:
  assumes "proof_state_wellFormed S"
  shows "set (ps_localCalls S) \<subseteq> dom (calls S)"
proof -
  from assms obtain S' where rel: "proof_state_rel S S'" 
    unfolding proof_state_wellFormed_def by blast

  hence "state_wellFormed S'"
    using proof_state_rel_def by blast

  from proof_state_rel_facts[OF rel]
  have "case ps_tx S of None \<Rightarrow> ps_localCalls S = [] | Some tx' \<Rightarrow> set (ps_localCalls S) = {c. callOrigin S' c \<triangleq> tx'}" 
    by simp


  thus ?thesis
    apply (auto simp add:  split: option.splits)
    by (metis \<open>calls S' = calls S\<close> \<open>state_wellFormed S'\<close> option.distinct(1) option.exhaust_sel wf_callOrigin_and_calls)
qed

lemma proof_state_wellFormed_localCalls_subset_calls':
  assumes "proof_state_wellFormed S"
  shows "c \<in> set (ps_localCalls S) \<Longrightarrow> \<exists>y. calls S c \<triangleq> y"
  using assms 
  by (meson domD proof_state_wellFormed_localCalls_subset_calls subset_iff)



lemma proof_state_wellFormed_implies:
  assumes wf:
    "proof_state_wellFormed PS"
  shows "proof_state_wellFormed' PS"
  unfolding proof_state_wellFormed'_def
proof (intro conjI)
  from wf obtain S where rel: "proof_state_rel PS S"
    unfolding proof_state_wellFormed_def by blast

  have "state_wellFormed S"
    using \<open>proof_state_rel PS S\<close> proof_state_rel_facts(1) by blast

  thm proof_state_rel_facts[OF rel]
  have "dom (callOrigin PS) \<inter> set (ps_localCalls PS) = {}"
    using proof_state_rel_facts(18) rel by blast
  have "Field (happensBefore PS) \<inter> set (ps_localCalls PS) = {}"
    using proof_state_rel_facts(19) rel by blast

  have tx_cases: "case ps_tx PS of None \<Rightarrow> ps_localCalls PS = [] | Some tx' \<Rightarrow> set (ps_localCalls PS) = {c. callOrigin S c \<triangleq> tx'}"
    using proof_state_rel_facts(15) rel by blast

  have "Field (happensBefore S) \<subseteq> dom (calls S)"
    by (meson \<open>state_wellFormed S\<close> domIff subsetI wellFormed_happensBefore_Field)
  have "Field (happensBefore PS) \<subseteq> Field (happensBefore S)"
    by (auto simp add: proof_state_rel_facts[OF rel] Field_def updateHb_cases)

  have "Field (happensBefore PS) \<subseteq> dom (calls PS)"
    using \<open>Field (happensBefore PS) \<subseteq> Field (happensBefore S)\<close> \<open>Field (happensBefore S) \<subseteq> dom (calls S)\<close> proof_state_rel_facts(2) rel by fastforce

  show "finite (dom (ps_store PS))"
    using local.wf proof_state_rel_facts(25) proof_state_wellFormed_def by blast
  show "ps_tx PS = None \<longrightarrow> ps_localCalls PS = []"
    using \<open>proof_state_rel PS S\<close> proof_state_rel_facts(15) by fastforce
  show "Field (happensBefore PS) \<subseteq> dom (calls PS) - set (ps_localCalls PS)"
    using tx_cases \<open>Field (happensBefore PS) \<subseteq> dom (calls PS)\<close>
      \<open>Field (happensBefore PS) \<inter> set (ps_localCalls PS) = {}\<close>
    by (auto simp add: split: option.splits)
  show "ps_vis PS \<subseteq> dom (calls PS)"
    using \<open>state_wellFormed S\<close> proof_state_rel_facts(12) proof_state_rel_facts(2) rel wellFormed_visibleCallsSubsetCalls_h(2) by fastforce
  show "set (ps_localCalls PS) \<subseteq> dom (calls PS)"
    using tx_cases \<open>Field (happensBefore PS) \<subseteq> dom (calls PS)\<close>
    apply (auto simp add: split: option.splits)
    by (metis (no_types, lifting) \<open>state_wellFormed S\<close> domExists_simp proof_state_rel_facts(2) rel wellFormed_callOrigin_dom)
qed

lemma step_io_wf_maintained:
  assumes wf: "proof_state_wellFormed S"
    and step: "step_io progInv qrySpec S cmd S' cmd' True"
  shows "proof_state_wellFormed S'"
  using assms by (auto simp add: step_io_def)


lemma step_io_wf_maintained':
  assumes wf: "proof_state_wellFormed' S"
    and step: "step_io progInv qrySpec S cmd S' cmd' True"
  shows "proof_state_wellFormed' S'"
  unfolding proof_state_wellFormed'_def
proof (conj_one_by_one pre: wf[simplified proof_state_wellFormed'_def])
  show "finite (dom (ps_store S)) \<Longrightarrow> finite (dom (ps_store S'))"
    using step by (auto simp add: step_io_def split: io.splits)
  show "ps_tx S = None \<longrightarrow> ps_localCalls S = [] \<Longrightarrow> ps_tx S' = None \<longrightarrow> ps_localCalls S' = []"
    using step by (auto simp add: step_io_def split: io.splits)
  show "ps_vis S' \<subseteq> dom (calls S')" if pre: "ps_vis S \<subseteq> dom (calls S)"
  proof (cases cmd)
    case (WaitBeginAtomic x2)
    then show ?thesis using step  
    proof (auto simp add: step_io_def split: io.splits, fuzzy_goal_cases G)
      case (G x t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes')

      from G.consistentSnapshotH
      have "vis' \<subseteq> dom calls'"
        by (simp add: consistentSnapshotH_def)

      with `x \<in> vis'`
      show "\<exists>y. calls' x \<triangleq> y"
        by blast
    qed
  next
    case (WaitEndAtomic x3)
    then show ?thesis using step 
    proof (auto simp add: step_io_def split: io.splits, fuzzy_goal_cases A B)
      case (A x)

      show "\<exists>y. calls S x \<triangleq> y"
        by (simp add: A.member local.wf proof_state_wellFormed'_vis_subset_calls')
    next
      case (B x)
      then show "\<exists>y. calls S x \<triangleq> y"
        using local.wf proof_state_wellFormed'_localCalls_subset_calls' by blast
    qed

  qed (use step pre in \<open>auto simp add: step_io_def split: io.splits\<close>)

  show "Field (happensBefore S') \<subseteq> dom (calls S') - set (ps_localCalls S')"
    if pre: " Field (happensBefore S) \<subseteq> dom (calls S) - set (ps_localCalls S) "
  proof (cases cmd)
    case (WaitBeginAtomic x2)
    then show ?thesis using step 
    proof (auto simp add: step_io_def split: io.splits, fuzzy_goal_cases A B)
      case (A x t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes')

      from A.proof_state_wellFormed
      have proof_state_wellFormed':  "proof_state_wellFormed'
         (S\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
              transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',
              invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr>)"
        by (rule proof_state_wellFormed_implies)


      from proof_state_wellFormed'_happensBefore_subset_calls[OF proof_state_wellFormed']
      have "Field happensBefore' \<subseteq> dom calls'"
        by auto

      from `x \<in> Field happensBefore'`
      show "\<exists>y. calls' x \<triangleq> y"
        using \<open>Field happensBefore' \<subseteq> dom calls'\<close> by blast
    next
      case (B x t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes')

      from `x \<in> Field happensBefore'`
      show "False"
        using B.member2 B.ps_tx_eq local.wf proof_state_wellFormed'_localCalls by force
    qed
  next
    case (WaitEndAtomic x3)
    then show ?thesis using step pre 
      apply (auto simp add: step_io_def Field_def updateHb_cases split: io.splits)
      subgoal
        by blast
      subgoal
        using local.wf proof_state_wellFormed'_vis_subset_calls' by blast
      subgoal
        by (simp add: in_sequence_in1 local.wf proof_state_wellFormed'_localCalls_subset_calls')
      subgoal
        by blast
      subgoal
        using local.wf proof_state_wellFormed'_localCalls_subset_calls' by blast
      subgoal 
        by (simp add: in_sequence_in2 local.wf proof_state_wellFormed'_localCalls_subset_calls')
      done
  next
  qed (use step pre in \<open>auto simp add: step_io_def split: io.splits\<close>)


  show "set (ps_localCalls S') \<subseteq> dom (calls S')"
    if  pre: "set (ps_localCalls S) \<subseteq> dom (calls S)"
  proof (cases cmd)
    case (WaitBeginAtomic x2)
    then show ?thesis using step pre
    proof (auto simp add: step_io_def split: io.splits, fuzzy_goal_cases G)
      case (G x t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes')
      show "\<exists>y. calls' x \<triangleq> y"
        using G.member G.ps_tx_eq local.wf proof_state_wellFormed'_localCalls by force
    qed
  qed (use step pre in \<open>auto simp add: step_io_def split: io.splits\<close>)
qed

lemma steps_io_wf_maintained'2:
  assumes wf: "proof_state_wellFormed' S"
    and steps: "steps_io progInv qrySpec S cmd S' res"
    and ok: "res \<noteq> None"
  shows "proof_state_wellFormed' S'"
  using steps wf ok proof (induct)
  case (steps_io_final  S res)
  then show ?case 
    by auto
next
  case (steps_io_error  S cmd S' cmd')
  then show ?case 
    by auto
next
  case (steps_io_step S cmd S' cmd' S'' res)
  then show ?case 
    using step_io_wf_maintained' by blast
qed



lemma steps_io_wf_maintained':
  assumes wf: "proof_state_wellFormed' S"
    and steps: "steps_io progInv qrySpec S cmd S' (Some res)"
  shows "proof_state_wellFormed' S'"
  using local.wf steps steps_io_wf_maintained'2 by fastforce


lemma steps_io_wf_maintained:
  assumes wf: "proof_state_wellFormed S"
    and steps: "steps_io progInv qrySpec S cmd S' res"
    and ok: "res \<noteq> None"
  shows "proof_state_wellFormed S'"
  using steps wf ok proof (induct)
  case (steps_io_final  S res)
  then show ?case 
    by auto
next
  case (steps_io_error  S cmd S' cmd')
  then show ?case 
    by auto
next
  case (steps_io_step S cmd S' cmd' S'' res)
  then show ?case 
    using step_io_wf_maintained by blast
qed

lemma steps_io_wf_maintained_Some:
  assumes wf: "proof_state_wellFormed S"
    and steps: "steps_io progInv qrySpec S cmd S' (Some res)"
  shows "proof_state_wellFormed S'"
  using local.wf steps steps_io_wf_maintained by fastforce


text \<open>We now show that all errors in an execution of the single-invocation semantics 
can be simulated by the steps-io approximation.
Thus it is sufficient to show that the steps-io approximation is correct.

\<close>

definition invariant_return :: "
  (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool) 
\<Rightarrow> ('proc, 'any, 'operation) proof_state 
\<Rightarrow> 'any option
\<Rightarrow> bool" where
  "invariant_return progInv PS resO \<equiv>
  \<exists>res. resO \<triangleq> res 
      \<and> uniqueIds res \<subseteq> ps_localKnown PS
      \<and> progInv (invariantContext.truncate (PS\<lparr> invocationRes := invocationRes PS(ps_i PS \<mapsto> res), knownIds := knownIds PS \<union> uniqueIds res  \<rparr>))"
  \<comment> \<open>TODO maybe add: there is no current transaction. \<close>

lemma steps_nonempty_first:
  assumes "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
    and "tr \<noteq> []"
  shows "\<exists>S' a. S ~~ (i, a) \<leadsto>\<^sub>S S'"
  using assms proof (induct rule: step_s_induct)
  case initial
  then show ?case by auto
next
  case (step tr S' a S'')
  show ?case
  proof (cases "tr")
    case Nil
    show ?thesis 
    proof (intro exI)
      show "S ~~ (i, a) \<leadsto>\<^sub>S S''"
        using step Nil by (auto simp add: steps_s_empty)
    qed
  next
    case (Cons a list)
    then show ?thesis
      using step by auto
  qed
qed



lemma steps_io_simulation:
  fixes PS :: "('proc::valueType, 'any::valueType, 'operation::valueType) proof_state"
  assumes rel: "proof_state_rel PS S"
    and steps: "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
    and i_def: "i = ps_i PS"
    and not_correct: "\<not>traceCorrect_s tr"
    and prog_wf: "program_wellFormed (prog S)"
    and cmd_def: "cmd = currentCommand S i"
    and qry_rel: "crdt_spec_rel (querySpec (prog S)) querySpec'"
  shows "\<exists>PS' res. steps_io (invariant (prog S)) querySpec' PS cmd  PS' res
               \<and> (res = None \<or> \<not>invariant_return (invariant (prog S))  PS' res)
               " \<comment> \<open>TODO or final state after return that does not satisfy invariant.\<close>
  using rel steps i_def not_correct prog_wf cmd_def qry_rel proof (induct "length tr" arbitrary: S' tr PS S cmd)
  case (0 tr S' PS S cmd)
  hence "tr = []"
    by auto
  hence "traceCorrect_s tr"
    by (simp add: traceCorrect_s_def)
  with `\<not>traceCorrect_s tr` 
  show ?case by auto
next
  case (Suc k tr S' PS S cmd)
  from this obtain action ok tr' 
    where tr_def: "tr = ((action, ok)#tr')"
    by (metis length_Suc_conv prod.collapse)

  with `S ~~ (i, tr) \<leadsto>\<^sub>S* S'`
  obtain S1 
    where first_step:"S ~~ (i, action, ok) \<leadsto>\<^sub>S S1" 
      and other_steps:"S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'"
    using steps_s_cons_simp by blast

  have "prog S1 = prog S"
    using unchangedProg1[OF first_step]
    by simp

  show ?case
  proof (cases "\<exists>res. cmd = WaitReturn res")
    case True
    from this obtain res
      where "cmd = WaitReturn res"
      by blast

    have "currentProc S i \<triangleq> toImpl"
      by (simp add: Suc.prems(1) Suc.prems(3) proof_state_rel_facts(11))


    have "ps_i PS = i"
      by (simp add: Suc.prems(3))


    have wf: "state_wellFormed S"
      using proof_state_rel_wf[OF `proof_state_rel PS S`] by simp

    from first_step `cmd = currentCommand S i`[symmetric]
      `cmd = WaitReturn res`
      `currentProc S i \<triangleq> toImpl`
      wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf]
    have c3: "localState S i \<triangleq> (ps_store PS, ps_localKnown PS, impl_language_loops.io.WaitReturn res)"
      using proof_state_rel_facts(10)[OF `proof_state_rel PS S`]
      by ( auto simp add: step_s.simps `ps_i PS = i`)



    show ?thesis
    proof (cases "action = ALocal False")
      case True

      from first_step `cmd = currentCommand S i`[symmetric]
        `cmd = WaitReturn res`
        `currentProc S i \<triangleq> toImpl`
        wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf] 
        c3
        `action = ALocal False`
      obtain u
        where  "u \<notin> ps_localKnown PS"
          and action_def: "action = ALocal False"
          and c5: "u \<in> uniqueIds res"
          and c6: "S1 = (S\<lparr>localState := localState S1(i \<mapsto> (ps_store PS, ps_localKnown PS, impl_language_loops.io.WaitReturn res))\<rparr>)"
          and c7: "\<not> ok"
        by (auto simp add: step_s.simps  split: if_splits) 

      define PS' where "PS' \<equiv> PS"

      have "\<not>invariant_return (invariant (prog S))  PS (Some res)"
        using  `u \<in> uniqueIds res` `u \<notin> ps_localKnown PS` by (auto simp add: invariant_return_def)


      thus ?thesis
        using \<open>cmd = impl_language_loops.io.WaitReturn res\<close> steps_io_final by fastforce
    next
      case False



      from first_step `cmd = currentCommand S i`[symmetric]
        `cmd = WaitReturn res`
        `currentProc S i \<triangleq> toImpl`
        wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf] 
        c3
      have c0: "cmd = impl_language_loops.io.WaitReturn res"
        and c1: "currentProc S i \<triangleq> impl_language_loops.toImpl"
        and c2: "action = AReturn res"
        and uids_wf: "uniqueIds res \<subseteq> ps_localKnown PS"
        and c4: "currentTransaction S i = None"
        and c5: "S1 = S \<lparr>localState := (localState S)(i := None), currentProc := (currentProc S)(i := None), visibleCalls := (visibleCalls S)(i := None), invocationRes := invocationRes S(i \<mapsto> res), knownIds := knownIds S \<union> uniqueIds res\<rparr>"
        and c6: "ok \<longleftrightarrow> invariant (prog S) (invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S) (knownIds S \<union> uniqueIds res) (invocationOp S) (invocationRes S(i \<mapsto> res)))"
        unfolding atomize_conj 
        by (auto simp add: step_s.simps `action \<noteq> ALocal False`  split: if_splits)

      have "invocationRes S1 i = Some res"
        using c5 by simp


      have "tr' = []"    \<comment> \<open>Can do no step after return \<close>
      proof (rule ccontr)
        assume "tr' \<noteq> []"
        with `S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'`
        obtain S1' a where "S1 ~~ (i, a) \<leadsto>\<^sub>S S1'"
          using steps_nonempty_first by blast

        have "invocationOp S i \<noteq> None"
          using c3 local.wf wf_localState_to_invocationOp by fastforce


        from c5 `invocationOp S i \<noteq> None` `S1 ~~ (i, a) \<leadsto>\<^sub>S S1'`
        show False by (auto simp add: step_s.simps)
      qed

      with `\<not>traceCorrect_s tr`
      have "\<not>ok"
        by (simp add: tr_def traceCorrect_s_def)

      have "ps_tx PS = None"
        using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_facts(13) by fastforce

      show ?thesis
      proof (intro conjI exI)
        show "steps_io (invariant (prog S)) querySpec' PS cmd PS (Some res)"
        proof (fuzzy_rule steps_io_final)
          show "impl_language_loops.io.WaitReturn res = cmd"
            using `cmd = WaitReturn res` by simp

        qed

        have "\<not> invariant_return (invariant (prog S)) PS (Some res)"
          unfolding invariant_return_def not_ex de_Morgan_conj disj_not1
        proof (intro impI allI )
          fix r
          assume "Some res \<triangleq> r"

          have allCommitted: "committedCalls S = dom (calls S)"
            by (smt Suc.prems(1) Suc.prems(3) c4 committedCalls_allCommitted option.discI proof_state_rel_def)

          have h2: "committedCallsH (map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS))) (transactionStatus S)
          = dom (calls PS)"
            using Suc.prems(1) allCommitted proof_state_rel_facts(2) proof_state_rel_facts(4) by fastforce


          have ctx_same: "(invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S)
          (knownIds S \<union> uniqueIds res) (invocationOp S) (invocationRes S(i \<mapsto> res)))
        =(invariantContext.truncate (PS\<lparr>invocationRes := invocationRes PS(ps_i PS \<mapsto> r), knownIds := knownIds PS \<union> uniqueIds r\<rparr>))"
            \<comment> \<open>TODO extract this into lemma (invContextH and truncate if all committed)\<close>
            apply (auto simp add: invContextH_def invariantContext.defs allCommitted h2 restrict_relation_def
                updateHb_simp_distinct2 `i = ps_i PS` restrict_map_def domD domIff
                proof_state_rel_facts[OF `proof_state_rel PS S`]
                intro!: HOL.ext)
            subgoal
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_facts(13) proof_state_rel_facts(15) by fastforce
            subgoal
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_facts(13) proof_state_rel_facts(15) by fastforce
            subgoal
              using Suc.prems(1) happensBefore_in_calls_left local.wf proof_state_rel_facts(2) proof_state_rel_facts(3) updateHb_simp_distinct2 by fastforce
            subgoal
              using Suc.prems(1) happensBefore_in_calls_right local.wf proof_state_rel_facts(2) proof_state_rel_facts(3) updateHb_simp_distinct2 by fastforce
            subgoal
              apply (auto simp add: map_update_all_def)
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_facts(13) proof_state_rel_facts(15) by fastforce
            subgoal
              by (metis Suc.prems(1) local.wf map_update_all_None proof_state_rel_facts(2) proof_state_rel_facts(4) wellFormed_callOrigin_dom3)
            subgoal for x
              apply (case_tac "transactionStatus S x", auto)
              by (simp add: \<open>ps_tx PS = None\<close>)
            subgoal
              by (smt Suc.prems(1) \<open>ps_tx PS = None\<close> domIff option.distinct(1) option.exhaust_sel option.simps(4) proof_state_rel_def transactionStatus.exhaust wf_transaction_status_iff_origin_dom)

            using \<open>Some res \<triangleq> r\<close> by blast+


          from `\<not>ok` c6
          show "\<not> invariant (prog S) (invariantContext.truncate (PS\<lparr>invocationRes := invocationRes PS(ps_i PS \<mapsto> r), knownIds := knownIds PS \<union> uniqueIds r\<rparr>))"
            by (auto simp add: ctx_same)
        qed
        thus "Some res = None \<or> \<not> invariant_return (invariant (prog S)) PS (Some res)"
          by simp
      qed
    qed
  next
    case False

    have current: "currentCommand S i = currentCommand S i \<bind> return"
      by simp

    have "\<exists>PS' cmd'.
       step_io (invariant (prog S)) querySpec' PS (currentCommand S i) PS' cmd' ok \<and>
       (ok \<longrightarrow> proof_state_rel PS' S1 \<and> currentCommand S1 i = cmd' \<bind> impl_language_loops.return)"
      using `proof_state_rel PS S` first_step `i = ps_i PS` current
    proof (rule step_io_simulation)
      show "\<And>r. currentCommand S i \<noteq> impl_language_loops.io.WaitReturn r"
        using False `cmd = currentCommand S i` by blast
      show "program_wellFormed (prog S)"
        using `program_wellFormed (prog S)` .


      show "uniqueIds Op \<subseteq> ps_localKnown PS"
        if c0: "action = ADbOp c Op res"
        for  c Op res
        by (metis Suc.prems(1) Suc.prems(3) \<open>\<And>thesis. (\<And>S1. \<lbrakk>S ~~ (i, action, ok) \<leadsto>\<^sub>S S1; S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> action.distinct(33) action.distinct(53) proof_state_rel_def step_s_to_step that use_invocation_cannot_guess_ids_dbop)

      show "crdt_spec_rel (querySpec (prog S)) querySpec'"
        using `crdt_spec_rel (querySpec (prog S)) querySpec'` by auto


    qed

    from this obtain PS' cmd' 
      where step_io: "step_io (invariant (prog S)) querySpec' PS (currentCommand S i) PS' cmd' ok"
        and step_io2: "(ok \<Longrightarrow> proof_state_rel PS' S1 \<and> currentCommand S1 i = cmd')"
      by auto

    show ?thesis
    proof (cases ok)
      case True
      hence "proof_state_rel PS' S1"
        and "currentCommand S1 i = cmd' \<bind> impl_language_loops.return"
        using step_io2 by auto

      hence "currentCommand S1 i = cmd'"
        by simp

      have "k = length tr'"
        using  `Suc k = length tr` \<open>tr = (action, ok) # tr'\<close> by auto


      have "i = ps_i PS'"
        using Suc.prems(3) step_io step_io_same_i by fastforce

      have "\<not> traceCorrect_s tr'"
        using `\<not> traceCorrect_s tr` True tr_def traceCorrect_s_split by fastforce


      from `prog S1 = prog S` `program_wellFormed (prog S)`
      have "program_wellFormed (prog S1)"
        by simp

      have "cmd' = currentCommand S1 i"
        using `currentCommand S1 i = cmd'`
        by simp

      from `crdt_spec_rel (querySpec (prog S)) querySpec'` `prog S1 = prog S`
      have "crdt_spec_rel (querySpec (prog S1)) querySpec'" by simp


      from Suc.hyps(1)[OF `k = length tr'` `proof_state_rel PS' S1` `S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'` 
          `i = ps_i PS'` `\<not> traceCorrect_s tr'` `program_wellFormed (prog S1)` `cmd' = currentCommand S1 i`
          `crdt_spec_rel (querySpec (prog S1)) querySpec'`]
      obtain PS'' and res
        where steps_tr': "steps_io (invariant (prog S1)) querySpec' PS' cmd'  PS'' res"
          and incorrect_cases: "res = None \<or> \<not> invariant_return (invariant (prog S1)) PS'' res"
        by auto

      have steps_combined: "steps_io (invariant (prog S)) querySpec' PS cmd  PS'' res" 
        using step_io 
      proof (fuzzy_rule steps_io_step)
        show "currentCommand S i = cmd"
          by (simp add: Suc.prems(6))
        show " steps_io (invariant (prog S)) querySpec' PS' cmd' PS'' res"
          using steps_tr'
          by (metis (no_types, lifting) Suc.prems(2) other_steps unchangedProg) 
        show "ok = True"
          using `ok` by simp
      qed



      have "prog S1 = prog S"
        using unchangedProg1[OF first_step]
        by simp

      from incorrect_cases
      show ?thesis
      proof
        assume "res = None"

        with steps_combined
        show ?thesis
          by blast
      next
        assume "\<not> invariant_return (invariant (prog S1)) PS'' res"
        hence "\<not> invariant_return (invariant (prog S)) PS'' res"
          using `prog S1 = prog S` by simp
        with steps_combined
        show ?thesis
          by blast
      qed
    next
      case False

      from \<open>step_io (invariant (prog S)) querySpec' PS (currentCommand S i) PS' cmd' ok\<close>
      have "steps_io (invariant (prog S)) querySpec' PS cmd PS' None"
      proof (fuzzy_rule steps_io_error)
        show "ok = False" using False by simp

        show "currentCommand S i = cmd"
          using ` cmd = currentCommand S i` by simp


      qed
      thus ?thesis
        by auto
    qed
  qed
qed




method subst_all uses r = (subst r | subst(asm) r)+

text "Correctness of execution when executing only a prefix of the trace:"


definition "execution_s_correct_p" where
  "execution_s_correct_p S i ls1 P \<equiv> 
    \<forall>trace S' store lk ls2 store' lk' ls1'. 
          (S ~~ (i, trace) \<leadsto>\<^sub>S* S') 
      \<longrightarrow> (localState S i \<triangleq> (store, lk, bind ls1 ls2))
      \<longrightarrow> (localState S' i \<triangleq> (store', lk', bind ls1' ls2))
      \<longrightarrow> traceCorrect_s trace \<and> (\<forall>res. ls1' = WaitReturn res \<longrightarrow>  P S' res)"

lemmas use_execution_s_correct_p = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

lemmas use_execution_s_correct_p_trace = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct1]

lemmas use_execution_s_correct_p_P = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct2, rule_format]

lemma execution_s_correct_to_p:
  assumes ec_p: "execution_s_correct_p S i ls1 P"
    and S_ls: "localState S i \<triangleq> (store, localKnown, ls1)"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and wf_s: "state_wellFormed_s S i"
    and impl: "currentProc S i \<triangleq> toImpl"
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  have wf: "state_wellFormed S"
    using state_wellFormed_s_to_wf wf_s by blast


  from  steps
  show "traceCorrect_s trace"
  proof (induct rule: step_s_induct)
    case initial
    then show ?case
      by (simp add: traceCorrect_s_def) 
  next
    case (step tr S' a S'')

    hence IH: "(x, False) \<notin> set tr" for x
      by (simp add: traceCorrect_s_def)

    have "S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''"
      using step.hyps step.step steps_s_step by blast

    from `S' ~~ (i, a) \<leadsto>\<^sub>S S''`
    have "localState S' i \<noteq> None"
      apply (auto simp add: step_s.simps)
      by (metis S_ls Un_iff \<open>S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''\<close> list.set_intros(1) local.wf no_more_invoc option.simps(3) set_append)




\<comment> \<open>TODO: move into Lemma\<close>
    from ` S ~~ (i, tr) \<leadsto>\<^sub>S* S'` `localState S' i \<noteq> None`
    have "currentProc S' i \<triangleq> toImpl"
    proof (induct rule: step_s_induct)
      case initial
      then show ?case
        using S_ls impl by blast
    next
      case (step tr S a S')
      then show ?case
        apply (auto simp add: step_s.simps)
        by (metis (no_types, lifting) S_ls has_invocationOp_forever local.wf option.exhaust option.simps(3) wf_localState_needs_invocationOp)
    qed

    have "localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)"
      using S_ls by auto

    show ?case 
    proof (auto simp add: traceCorrect_s_def IH)
      fix x
      assume "a = (x, False)"



      show False
      proof (cases "localState S'' i")
        case None

        from `a = (x, False)` `S' ~~ (i, a) \<leadsto>\<^sub>S S''` `localState S'' i = None` `currentProc S' i \<triangleq> toImpl`
        obtain store'' localKnown'' ls'' res
          where a0: "a = (AReturn res, False)"
            and a1: "x = AReturn res"
            and not_invariant: "\<not> invariant (prog S')             (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S')               (calls S') (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))"
            and a3: "localState S' i \<triangleq> (store'', localKnown'', ls'')"
            and a4: "currentProc S' i \<triangleq> toImpl"
            and a5: "toImpl (store'', localKnown'', ls'') = Return res"
            and a6: "currentTransaction S' i = None"
            and S''_def: "S'' = S'         \<lparr>localState := (localState S')(i := None), currentProc := (currentProc S')(i := None),            visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> res),            knownIds := knownIds S' \<union> uniqueIds res\<rparr>"
          by (auto simp add: step_s.simps)

        from ec_p \<open>S ~~ (i, tr) \<leadsto>\<^sub>S* S'\<close> \<open>localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)\<close> 
        have "P S' res" 
        proof (rule use_execution_s_correct_p_P)
          from `toImpl (store'', localKnown'', ls'') = Return res`
          show "ls'' = impl_language_loops.io.WaitReturn res"
            by (cases ls'', auto split: prod.splits if_splits)

          from `localState S' i \<triangleq> (store'', localKnown'', ls'')`
          show " localState S' i \<triangleq> (store'', localKnown'', ls'' \<bind> impl_language_loops.return)"
            by auto
        qed
        from P[OF this]
        have invariant: "invariant (prog S) (invariantContext.truncate (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))" .

        have "state_wellFormed S'"
          using local.wf state_wellFormed_s_steps step.step by blast

        have "state_wellFormed_s S' i"
          using state_wellFormed_s_def step.step steps_s_append wf_s by blast

        have "currentTransaction S' i = None"
          using a6 by auto


        have no_uncommitted:
          "transactionStatus S' tx \<noteq> Some Uncommitted" for tx
          using \<open>state_wellFormed_s S' i\<close> a6 state_wellFormed_s_currentTransactions_iff_uncommitted by fastforce



        have "prog S' = prog S"
          using step.step unchangedProg by blast



        have allTxnsCommitted: "committedTransactions S' = dom (transactionOrigin S')"
          apply (auto simp add: )
           apply (metis \<open>state_wellFormed S'\<close> option.distinct(1) option.exhaust wf_transactionOrigin_and_status)
          by (metis \<open>state_wellFormed S'\<close> no_uncommitted not_uncommitted_cases option.exhaust state_wellFormed_transactionStatus_transactionOrigin)


        have allCommitted: "committedCalls S' = dom (calls S')"
          apply (auto simp add: committedCallsH_def isCommittedH_def)
           apply (metis \<open>state_wellFormed S'\<close> no_uncommitted option.exhaust wellFormed_currentTransactionUncommitted wf_callOrigin_and_calls)
          by (metis (no_types, hide_lams) \<open>state_wellFormed S'\<close> exists_optionI no_uncommitted not_uncommitted_cases option.distinct(1) wf_callOrigin_and_calls wf_no_transactionStatus_origin_for_nothing)


        have invContextSame:
          "(invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S')
                (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))
            = (invariantContext.truncate (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                                             knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
          apply (auto simp add: invContextH_def invariantContext.defs allCommitted allTxnsCommitted restrict_relation_def)
            apply (simp add: \<open>state_wellFormed S'\<close> domD happensBefore_in_calls_left)
           apply (simp add: \<open>state_wellFormed S'\<close> domD happensBefore_in_calls_right)
          apply (metis \<open>state_wellFormed S'\<close> restrict_map_noop2 wellFormed_callOrigin_dom)
          done

        with invariant
        have "invariant (prog S')
        (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S')
          (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))"
          by (simp add: \<open>prog S' = prog S\<close>)


        with not_invariant P
        show False
          by auto


      next
        case (Some S''_ls)



        from ec_p 
        have "traceCorrect_s (tr @ [a]) \<and> (\<forall>res. snd (snd S''_ls) = impl_language_loops.io.WaitReturn res \<longrightarrow> P S'' res)"
          using \<open>S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''\<close> \<open>localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)\<close>
        proof (rule use_execution_s_correct_p)
          show "localState S'' i \<triangleq> (fst S''_ls, fst (snd S''_ls), snd (snd S''_ls) \<bind> impl_language_loops.return)"
            by (simp add: Some)
        qed

        thus False
          by (metis \<open>a = (x, False)\<close> append_is_Nil_conv last_in_set last_snoc list.simps(3) traceCorrect_s_def)


      qed
    qed
  qed
qed


lemma steps_io_same_i:
  assumes "steps_io progInv qrySpec S cmd S' res"
  shows "ps_i S' = ps_i S"
  using assms proof (induct rule: steps_io.induct)
  case (steps_io_final S  res)
  then show ?case
    by simp
next
  case (steps_io_error  S cmd S' cmd')
  then show ?case
    by (auto simp add: step_io_same_i)
next
  case (steps_io_step  S cmd S' cmd' S'' res)
  then show ?case 
    by (auto simp add: step_io_same_i)
qed


definition 
  "execution_s_check progInv qrySpec S cmd P \<equiv>
  \<forall>S' res. steps_io progInv qrySpec S cmd  S' res
    \<longrightarrow> proof_state_wellFormed S
    \<longrightarrow> (case res of Some r \<Rightarrow> P S' r | None \<Rightarrow> False)
  "

lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

definition
  "finalCheck Inv i S res \<equiv>
Inv (invariantContext.truncate (S\<lparr>invocationRes := invocationRes S(i \<mapsto> res), knownIds := knownIds S \<union> uniqueIds res\<rparr>))
\<and> uniqueIds res \<subseteq> ps_localKnown S"

lemmas show_finalCheck = finalCheck_def[THEN meta_eq_to_obj_eq, THEN iffD2, rule_format]


text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"


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
    and qry_rel: "crdt_spec_rel (querySpec progr) querySpec'"
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
    and c: "execution_s_check (invariant progr) querySpec' PS ls P"
    \<comment> \<open>The execution check ensures that executing statement s only produces valid traces ending in a state 
   satisfying P.\<close>
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  text "We can simulate this execution with @{term steps_io}:"

  have "i = ps_i PS"
    by (simp add: PS_def)

  have "proof_state_rel PS S"
    unfolding proof_state_rel_def 
  proof (intro conjI)
    show "state_wellFormed S"
      by (simp add: S_wf)

    show "sorted_by (happensBefore S) (ps_localCalls PS)"
      by (simp add: PS_def sorted_by_empty)

    show "\<forall>c. i_callOriginI PS c \<triangleq> ps_i PS \<longrightarrow> c \<in> ps_vis PS"
      apply (auto simp add: PS_def)
      by (metis (mono_tags, lifting) S_wf assms(2) i_callOriginI_h_def not_None_eq option.case_eq_if option.sel state_wellFormed_ls_visibleCalls_callOrigin)


    show "ps_generatedLocal PS \<subseteq> ps_localKnown PS"
      by (auto simp add: PS_def localKnown)

    show " invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S"
      using PS_def no_guess by force


  qed (insert assms, simp; fail)+


  define cmd where "cmd = currentCommand S i"

  show "traceCorrect_s trace"
  proof (rule ccontr)
    assume "\<not> traceCorrect_s trace"

    from steps_io_simulation[OF `proof_state_rel PS S` steps `i = ps_i PS` `\<not> traceCorrect_s trace` prog_wf `cmd = currentCommand S i`]
    obtain PS' res
      where steps_io: "steps_io (invariant (prog S)) querySpec' PS cmd PS' res"
        and not_correct: "res = None \<or> \<not> invariant_return (invariant (prog S)) PS' res"
      using progr_def qry_rel  by blast


    from c 
    have c1:  "(case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r)"
      if "steps_io (invariant progr) querySpec' PS ls  S' res"
        and "proof_state_wellFormed PS"
      for S' res
      using execution_s_check_def that by blast+

    from steps_io
    have "(case res of None \<Rightarrow> False | Some r \<Rightarrow> P PS' r)"
    proof (fuzzy_rule c1)
      show "cmd = ls"
        by (simp add: cmd_def ls_def)
      show "prog S = progr"
        by (simp add: progr_def)
      show "proof_state_wellFormed PS"
        using S_wf \<open>proof_state_rel PS S\<close> show_proof_state_wellFormed by blast

    qed

    with not_correct
    obtain r
      where c0: "\<not> invariant_return (invariant (prog S)) PS' (Some r)"
        and c1: "res \<triangleq> r"
        and c3: "P PS' r"
      by (auto split: option.splits)

    from `\<not> invariant_return (invariant (prog S)) PS' (Some r)`
    have notInv1: "(\<not> invariant (prog S) (invariantContext.truncate (PS'\<lparr>invocationRes := invocationRes PS'(ps_i PS' \<mapsto> r), knownIds := knownIds PS' \<union> uniqueIds r\<rparr>)))
             \<or> \<not>(uniqueIds r \<subseteq> ps_localKnown PS')"
      unfolding invariant_return_def by (auto simp add: )

    thus False
    proof 
      assume notInv: "(\<not> invariant (prog S) (invariantContext.truncate (PS'\<lparr>invocationRes := invocationRes PS'(ps_i PS' \<mapsto> r), knownIds := knownIds PS' \<union> uniqueIds r\<rparr>)))"

      thus False
        using P_inv \<open>i = ps_i PS\<close> c3 steps_io steps_io_same_i by fastforce
    next
      assume "\<not> uniqueIds r \<subseteq> ps_localKnown PS'"

      thus False
        using P_ids c3 by blast
    qed
  qed
qed



lemma execution_s_check_sound3:
  assumes a1: "localState S i \<triangleq> (Map.empty, uniqueIds op, ls)"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocationOp S i \<triangleq> op"
    and prog_wf: "program_wellFormed (prog S)"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and P_ids: "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
    and inv: "invariant progr (invariantContext.truncate S)"
    and qry_rel: "crdt_spec_rel (querySpec progr) querySpec'"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
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
  execution_s_check (invariant progr) querySpec' \<lparr>
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
      ps_prog = progr\<rparr> ls P" 
  shows "execution_s_correct S i"
  using a1 
proof (rule execution_s_check_sound[where P=P])

  from `S \<in> initialStates' progr i`
  obtain Sa proc a b impl
    where S_def: "S = Sa \<lparr>localState := localState Sa(i \<mapsto> (a, b)), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> proc)\<rparr>"
      and progr_def: "progr = prog Sa"
      and proc: "procedure (prog Sa) proc = ((a, b), impl)"
      and uniqueIds: "uniqueIds proc \<subseteq> knownIds Sa"
      and invAll: "invariant_all' Sa"
      and wf: "state_wellFormed Sa"
      and opNone: "invocationOp Sa i = None"
      and noUncommitted: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"
      and noTxns: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
    by (auto simp add: initialStates'_def)  

  have "op = proc"
    using a4 by (auto simp add: S_def)

  show "visibleCalls S i \<triangleq> {}"
    by (simp add: S_def)

  show "prog S = progr"
    using progr_def  by (simp add: S_def)

  show " currentProc S i \<triangleq> impl_language_loops.toImpl"
    by (simp add: a3)

  show "{} = {x. generatedIds S x \<triangleq> i}"
    by (auto simp add: S_def local.wf opNone wf_generated_ids_invocation_exists)

  show "{} \<subseteq> {}"
    by simp

  show "state_wellFormed S"
    using a2 initialStates'_same initialStates_wellFormed by fastforce

  show "currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted" for tx'
    using a2 initialState_noTxns1 initialStates'_same by fastforce

  show "currentTransaction S i = None"
    using a2 initialState_noTxns2 initialStates'_same by fastforce


  have pcgi: "invocations_cannot_guess_ids progr"
    using \<open>prog S = progr\<close> prog_wf program_wellFormed_def by blast

  then 
  show "invocation_cannot_guess_ids (uniqueIds op) i S"
    using `program_wellFormed (prog S)`
      and `S \<in> initialStates' progr i`
    using invocation_cannot_guess_ids_initialStates a4
    by fastforce

  show "\<And>S' res.
       P S' res \<Longrightarrow>
       invariant (prog S)
        (invariantContext.truncate
          (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    using P by blast

  show "program_wellFormed (prog S)"
    by (simp add: prog_wf)

  show "execution_s_check (invariant progr) querySpec'
     \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S,
        transactionOrigin = transactionOrigin S, knownIds = knownIds S, invocationOp = invocationOp S,
        invocationRes = invocationRes S, ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {},
        ps_localKnown = uniqueIds (the (invocationOp S i)), ps_vis = {}, ps_localCalls = [],
        ps_tx = currentTransaction S i,
        ps_firstTx =
          \<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed,
        ps_store = Map.empty,
        ps_prog = progr\<rparr>
     ls P"
  proof (fuzzy_rule c)
    show "\<And>tx. transactionOrigin S tx \<noteq> Some i"
      by (auto simp add: S_def noTxns)

    show "True = (\<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed)"
      by (auto simp add: S_def noTxns)

    show "None = currentTransaction S i"
      by (auto simp add: S_def local.wf opNone wellFormed_invoc_notStarted(1))


    show " op = the (invocationOp S i)"
      by (auto simp add: S_def  \<open>op = proc\<close>)

    show "(invocationRes S)(i := None) = invocationRes S"
      by (auto simp add: S_def fun_upd_idem local.wf opNone state_wellFormed_invocation_before_result)


    show "(invocationOp S)(i \<mapsto> op) = invocationOp S"
      by (auto simp add: S_def \<open>op = proc\<close>)

    show "invariant progr
       \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S,
          transactionOrigin = transactionOrigin S, knownIds = knownIds S, invocationOp = invocationOp S(i \<mapsto> op),
          invocationRes = (invocationRes S)(i := None)\<rparr>"
      using inv \<open>(invocationRes S)(i := None) = invocationRes S\<close> \<open>invocationOp S(i \<mapsto> op) = invocationOp S\<close> by (auto simp add: invariantContext.defs) 


  qed

  show "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
    using P_ids .


  show "\<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S, transactionOrigin = transactionOrigin S,
       knownIds = knownIds S, invocationOp = invocationOp S, invocationRes = invocationRes S, ps_i = i, ps_generatedLocal = {},
       ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (the (invocationOp S i)), ps_vis = {}, ps_localCalls = [],
       ps_tx = currentTransaction S i,
       ps_firstTx = \<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed,
       ps_store = Map.empty, ps_prog = progr\<rparr> =
    \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S, transactionOrigin = transactionOrigin S,
       knownIds = knownIds S, invocationOp = invocationOp S, invocationRes = invocationRes S, ps_i = i, ps_generatedLocal = {},
       ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds op, ps_vis = {}, ps_localCalls = [],
       ps_tx = currentTransaction S i, ps_firstTx = \<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed, ps_store = Map.empty, ps_prog = prog S\<rparr>"
    by (auto simp add: a4 \<open>prog S = progr\<close>)

  show "crdt_spec_rel (querySpec progr) querySpec'"
    using qry_rel by auto

qed (simp add: a4; fail )+


lemma execution_s_check_sound4:
  fixes S :: "('proc::valueType, 'any store \<times>  uniqueId set \<times> ('any,'operation, 'any) impl_language_loops.io, 'operation::valueType, 'any::valueType) state"
  assumes a1: "localState S i \<triangleq> (Map.empty, uniqueIds op, ls)"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocationOp S i \<triangleq> op"
    and prog_wf: "program_wellFormed (prog S)"
    and inv: "invariant_all' S"
    and qry_rel: "crdt_spec_rel (querySpec progr) querySpec'"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
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
  execution_s_check (invariant progr) querySpec' \<lparr>
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
  shows "execution_s_correct S i"
  using a1 a2 a3 a4 prog_wf inv c
proof (fuzzy_rule execution_s_check_sound3[where P="finalCheck (invariant progr) i"])

  show [simp]: "prog S = progr"
    using a2 initialStates'_same initialStates_reachable_from_initialState prog_initial unchangedProg1 by fastforce


  show "invariant (prog S) (invariantContext.truncate (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    if c0: "finalCheck (invariant progr) i S' res"
    for  S':: "('proc, 'any, 'operation) proof_state" and res::'any
    using that by (auto simp add: finalCheck_def)



  show "uniqueIds res \<subseteq> ps_localKnown S'"
    if c0: "finalCheck (invariant progr) i S' res"
    for S':: "('proc, 'any, 'operation) proof_state" and res::'any
    using that by (auto simp add: finalCheck_def)

  show "invContext' S = invariantContext.truncate S"
    by (simp add: invContext'_truncate)

  show "crdt_spec_rel (querySpec progr) querySpec'"
    by (simp add: qry_rel)


qed auto




lemma traceCorrect_s_empty: "traceCorrect_s  [] "
  by (simp add: traceCorrect_s_def) 

lemma case_trace_not_empty:
  assumes  "\<And>a trace'. trace = a#trace' \<Longrightarrow> traceCorrect_s  (a#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty2:
  assumes  "\<And>action Inv trace'. trace = (action, Inv)#trace' \<Longrightarrow> traceCorrect_s  ((action, Inv)#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty3:
  assumes "S ~~ (i,trace) \<leadsto>\<^sub>S* S''"
    and "\<And>action S' Inv trace'. \<lbrakk>
      trace = (action, Inv)#trace'; 
      S ~~ (i,action,Inv) \<leadsto>\<^sub>S S'; 
      S' ~~ (i,trace') \<leadsto>\<^sub>S* S''\<rbrakk> \<Longrightarrow> Inv \<and> traceCorrect_s (trace')"
  shows "traceCorrect_s  trace"
  by (metis assms(1) assms(2) case_trace_not_empty2 sndI steps_s_cons_simp traceCorrect_s_split)


lemma sorted_by_updateHb:
  assumes "set cs \<inter> vis = {}"
    and "set cs \<inter> Field hb = {}"
    and "distinct cs"
  shows "sorted_by (updateHb hb vis cs) cs"
  using assms proof (induct cs arbitrary: hb vis)
  case Nil
  then show ?case 
    by (simp add: sorted_by_empty)

next
  case (Cons x xs)

  have "distinct xs"
    using Cons.prems(3) by auto


  from this
  have IH: "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) xs"
  proof (fuzzy_rule Cons)

    show " set xs \<inter> insert x vis = {}"
      using Cons by auto
    show " set xs \<inter> Field (hb \<union> vis \<times> {x}) = {}"
      using Cons by (auto simp add: Field_def)
  qed

  show ?case 
  proof (auto simp add: updateHb.simps)
    show "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) (x # xs)"
      apply (auto simp add: sorted_by_cons_iff IH)
      using Cons.prems(1) Cons.prems(2) Cons.prems(3) FieldI1 updateHb_simp2 by fastforce
  qed
qed

lemma no_ainvoc:
  assumes "\<forall>p t. (AInvoc p, t) \<notin> set trace"
    and "trace = (action, Inv) # trace'"
    and "\<lbrakk>\<forall>p t. (AInvoc p, t) \<notin> set trace; \<And>proc. action \<noteq> AInvoc proc\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by auto

method show_proof_rule = 
  (subst  execution_s_check_def, intro allI impI conjI, erule case_trace_not_empty3, erule(1) no_ainvoc, fuzzy_goal_cases Step)

inductive_cases step_s_NewId: "S ~~ (i, ANewId uidv, Inv) \<leadsto>\<^sub>S S'"






lemma execution_s_check_proof_rule:
  assumes noReturn: "\<And>r. cmd \<noteq> WaitReturn r"
    and cont: "
\<And>PS' cmd' ok. \<lbrakk>
  step_io Inv crdtSpec PS cmd PS' cmd' ok;
  proof_state_wellFormed PS
\<rbrakk> \<Longrightarrow> 
  ok
  \<and> (\<exists>res. cmd' = return res
    \<and> P PS' res)"
  shows "execution_s_check Inv crdtSpec PS  (cmd) P"
proof (auto simp add: execution_s_check_def)
  fix S' res
  assume steps_io: "steps_io Inv crdtSpec PS cmd S' res"
    and PS_wf: "proof_state_wellFormed PS"

  from noReturn
  have noReturn: "cmd \<noteq> impl_language_loops.io.WaitReturn r" for r
    by (cases cmd, auto)


  from steps_io noReturn cont PS_wf
  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
  proof (induct)
    case (steps_io_final S res)
    then show ?case by auto
  next
    case (steps_io_error  S cmd S' cmd')
    have False
      using steps_io_error.hyps steps_io_error.prems(2) steps_io_error.prems(3)
      by blast
    thus ?case ..
  next
    case (steps_io_step S cmd S' cmd' S'' res)

    from steps_io_step(5)[OF steps_io_step(1) `proof_state_wellFormed S`]
    obtain r where "cmd' = return r" and "P S' r"
      by auto

    from `proof_state_wellFormed S`
    have "proof_state_wellFormed S'"
      using step_io_wf_maintained steps_io_step.hyps(1) by blast

    have "S'' = S' \<and> res \<triangleq> r"
      by (rule steps_io.cases[OF `steps_io Inv crdtSpec S' cmd' S'' res`],
          auto simp add: `cmd' = return r` return_def step_io_def)

    with `P S' r`
    show ?case
      by auto
  qed
qed





lemma WaitReturn_combined:
  "WaitReturn r = (cmd \<bind> cont)
\<Longrightarrow> (\<exists>ri. cmd = WaitReturn ri \<and> cont ri = WaitReturn r)"
  by (cases cmd) auto

lemma arg_cong_bind: 
  assumes "\<And>x. n x = n' x"
  shows "((a \<bind>io n) = (a \<bind>io n'))"
  by (rule arg_cong[where f="\<lambda>x. a \<bind>io x"], use assms in blast)


lemma step_io_bind_split:
  assumes "step_io progInv qrySpec S (cmd \<bind> cont) S' cmdCont' Inv"
  shows "(\<exists>cmd'. step_io progInv qrySpec S cmd S' cmd' Inv \<and> cmdCont' = cmd' \<bind> cont)
        \<or> (\<exists>r. cmd = WaitReturn r \<and> step_io progInv qrySpec S (cont r) S' cmdCont' Inv)"
proof (cases cmd)
  case (WaitLocalStep x1)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitBeginAtomic x2)
  then show ?thesis using assms  
    by (auto simp add: step_io_def split: prod.splits)
next
  case (WaitEndAtomic x3)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitNewId x41 x42)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitDbOperation x51 x52)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits if_splits) 
next
  case (WaitReturn x6)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (Loop init bdy cnt)
  then show ?thesis using assms  
    by (auto simp add: step_io_def intro!: arg_cong_bind split: prod.splits loopResult.splits) 
qed



lemma steps_io_bind_split1:
  assumes "steps_io Inv crdtSpec S cmdC S' res"
    and "cmdC = (cmd \<bind> cont)"
  shows "(\<exists>ri Si. steps_io Inv crdtSpec S cmd Si (Some ri) \<and> steps_io Inv crdtSpec Si (cont ri) S' res)
          \<or> (steps_io Inv crdtSpec S cmd S' None \<and> res = None)"
  using assms proof (induct arbitrary: cmd)
  case (steps_io_final S res)
  from this obtain ri
    where "cmd = WaitReturn ri" 
      and "cont ri = WaitReturn res"
    by (meson WaitReturn_combined)

  have "steps_io Inv crdtSpec S cmd S (Some ri)"
    by (auto simp add: `cmd = WaitReturn ri`  steps_io.steps_io_final)

  moreover have "steps_io Inv crdtSpec S (cont ri) S (Some res)"
    by (simp add: \<open>cont ri = impl_language_loops.io.WaitReturn res\<close> steps_io.steps_io_final)

  ultimately show ?case
    using \<open>cmd = impl_language_loops.io.WaitReturn ri\<close> steps_io.steps_io_final by fastforce
next
  case (steps_io_error S cmd1 S' cmd2)
  then show ?case
    apply (auto simp add: step_io_bind_split)
    by (metis step_io_bind_split steps_io.steps_io_error steps_io_final)
next
  case (steps_io_step  S cmd S' cmd' S'' res)
  then show ?case 
    apply (auto simp add: step_io_bind_split)
    by (smt step_io_bind_split steps_io.steps_io_step steps_io_final)+
qed

lemma steps_io_bind_split:
  assumes "steps_io Inv crdtSpec S (cmd \<bind> cont) S' res"
  shows "(\<exists>ri Si. steps_io Inv crdtSpec S cmd Si (Some ri) \<and> steps_io Inv crdtSpec Si (cont ri) S' res)
          \<or> (steps_io Inv crdtSpec S cmd S' None \<and> res = None)"
  using assms steps_io_bind_split1 by blast

lemma steps_io_bind_split':
  assumes "steps_io Inv crdtSpec S (cmd \<bind> cont) S' res"
  shows "(\<exists>ri Si. steps_io Inv crdtSpec S cmd Si ri \<and> 
        (case ri of Some r \<Rightarrow> steps_io Inv crdtSpec Si (cont r) S' res
                 |  None \<Rightarrow> res = None))"
  using assms option.distinct(1) steps_io_bind_split by fastforce

lemma step_io_combine:
  assumes "step_io progInv qrySpec S cmd S' cmd' ok"
  shows "step_io progInv qrySpec S (cmd\<bind>cont) S' (cmd'\<bind>cont) ok"
proof (cases cmd)
  case (WaitLocalStep x1)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitBeginAtomic x2)
  then show ?thesis using assms by (auto simp add: step_io_def; force)
next
  case (WaitEndAtomic x3)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitNewId x41 x42)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitDbOperation Op cmdCont)
  then show ?thesis using assms apply (auto simp add: step_io_def)
    subgoal for c y res
      by (auto intro: exI[where x=c])
    done
next
  case (WaitReturn x6)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (Loop init bdy cnt)
  then show ?thesis using assms 
    by (auto simp add: step_io_def intro!: arg_cong_bind split: prod.splits loopResult.splits) 
qed

lemma steps_io_combine_ok:
  assumes steps1: "steps_io Inv crdtSpec S cmd1 S' res1"
    and res1_def: "res1 = Some r"
    and steps2: "steps_io Inv crdtSpec S' (cmd2 r) S'' res2"
  shows "steps_io Inv crdtSpec S (cmd1 \<bind> cmd2) S'' res2"
  using steps1 res1_def steps2 
proof (induct)
  case (steps_io_final S res)
  then show ?case
    by auto
next
  case (steps_io_error  S cmd S' cmd')
  then show ?case
    by auto
next
  case (steps_io_step S cmd S' cmd' S''' res)
  show ?case
  proof (rule steps_io.steps_io_step)
    from `step_io Inv crdtSpec S cmd S' cmd' True`
    show "step_io Inv crdtSpec S (cmd \<bind> cmd2) S' (cmd' \<bind> cmd2) True"
      by (simp add: step_io_combine)

    show "steps_io Inv crdtSpec S' (cmd' \<bind> cmd2) S'' res2"
      by (simp add: steps_io_step.hyps(3) steps_io_step.prems(1) steps_io_step.prems(2))
  qed
qed


lemma execution_s_check_split:
  assumes ec: "execution_s_check Inv crdtSpec S (cmd \<bind> cont) P"
    and steps: "steps_io Inv crdtSpec S cmd S' (Some res)"
    and wf: "proof_state_wellFormed S"
  shows "execution_s_check Inv crdtSpec S' (cont res) P"
  unfolding execution_s_check_def proof (intro allI impI)

  fix S'a res'
  assume a0: "steps_io Inv crdtSpec S' (cont res) S'a res'"
    and a1: "proof_state_wellFormed S'"


  from ec
  have ec': "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r" 
    if "steps_io Inv crdtSpec S (cmd \<bind> cont) S' res"
      and "proof_state_wellFormed S"
    for S' res
    using execution_s_check_def that by blast



  show "case res' of None \<Rightarrow> False | Some r \<Rightarrow> P S'a r"
  proof (rule ec')
    show "steps_io Inv crdtSpec S (cmd \<bind> cont) S'a res'"
      by (meson a0 steps steps_io_combine_ok)
    show "proof_state_wellFormed S"
      using wf .
  qed
qed

(*
lemma steps_io_loop_unroll:
  shows "steps_io progInv qrySpec S (loop body) S' res
     \<longleftrightarrow> steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then return () else loop body)) S' res" (is "?left \<longleftrightarrow> ?right")
proof
  assume "steps_io progInv qrySpec S (loop body) S' res"

  from this
  show "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then return () else loop body)) S' res"
  proof cases
    case (steps_io_final res)
    then show ?thesis
      by (simp add: loop_def)
  next
    case (steps_io_error cmd')
    then show ?thesis
      by (simp add: step_io_def loop_def)
  next
    case (steps_io_step Si cmd')

    from `step_io progInv qrySpec S (loop body) Si cmd' True`
    have cmd': "cmd' = body \<bind>io (\<lambda>r. if r then return () else loop body)"
     and "Si = S"
      by (auto simp add: loop_def step_io_def from_V_rev intro!: arg_cong_bind)

    show ?thesis
    proof (fuzzy_rule `steps_io progInv qrySpec Si cmd' S' res`)
      show "Si = S" using `Si = S` .
      show "cmd' = body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)"
        using cmd' by auto
    qed
  qed
next
  assume a: "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) S' res"

  show "steps_io progInv qrySpec S (loop body) S' res"
  proof (rule steps_io_step)
    show "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) S' res"
      using a.
    show "step_io progInv qrySpec S (loop body) S
     (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) True"
      by (auto simp add: loop_def  step_io_def  intro!: arg_cong_bind)

  qed
qed
*)
lemma steps_io_return:
  assumes "steps_io progInv qrySpec S (return r) S' res"
  shows "S = S' \<and> res \<triangleq> r"
  using assms by cases (auto simp add: return_def step_io_def)


lemma steps_io_return_iff:
  shows "steps_io progInv qrySpec S (return r) S' res \<longleftrightarrow> S = S' \<and> res \<triangleq> r"
proof 
  show "steps_io progInv qrySpec S (impl_language_loops.return r) S' res \<Longrightarrow> S = S' \<and> res \<triangleq> r"
    by (erule steps_io_return)

  show "S = S' \<and> res \<triangleq> r \<Longrightarrow> steps_io progInv qrySpec S (impl_language_loops.return r) S' res"
    by (simp add: return_def steps_io_final)
qed

\<comment> \<open>TODO utils\<close>
lemma if_distrib_bind:
  "((if c then A else B) \<bind>io cont) = (if c then A \<bind>io cont else B \<bind>io cont)"
  by auto


subsection "Check With Bind"

lemma execution_s_check_bind:
  assumes "execution_s_check progInv qrySpec S cmd (\<lambda>S' r. 
    execution_s_check progInv qrySpec S' (cont r) P)"
  shows "execution_s_check progInv qrySpec S (cmd \<bind> cont) P"
proof (auto simp add: execution_s_check_def)
  fix S' res
  assume steps: "steps_io progInv qrySpec S (cmd \<bind> cont) S' res"
    and wf: "proof_state_wellFormed S"

  from steps_io_bind_split'[OF steps]
  obtain ri Si
    where steps_cmd: "steps_io progInv qrySpec S cmd Si ri"
      and ri_cases: "case ri of None \<Rightarrow> res = None | Some r \<Rightarrow> steps_io progInv qrySpec Si (cont r) S' res"
    by blast

  from use_execution_s_check[OF assms steps_cmd wf]
  have ri_cases2: "case ri of None \<Rightarrow> False | Some r \<Rightarrow> execution_s_check progInv qrySpec Si (cont r) P" .

  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
  proof (cases ri)
    case None
    then show ?thesis
      using ri_cases2 by auto
  next
    case (Some r)
    from Some and ri_cases
    have steps_cont: "steps_io progInv qrySpec Si (cont r) S' res" by auto

    from Some and ri_cases2
    have check_cont: "execution_s_check progInv qrySpec Si (cont r) P" by auto

    have wf2: "proof_state_wellFormed Si"
      using Some local.wf steps_cmd steps_io_wf_maintained by fastforce


    from use_execution_s_check[OF check_cont steps_cont wf2]
    show ?thesis
      by auto
  qed
qed

subsection "Strengthen Postcondition"


lemma execution_s_check_strengthen:
  assumes "execution_s_check Inv crdtSpec PS cmd P"
    and "\<And>S r. \<lbrakk>proof_state_wellFormed S;  P S r\<rbrakk> \<Longrightarrow> Q S r"
  shows "execution_s_check Inv crdtSpec PS cmd Q"
  by (smt assms execution_s_check_def option.case_eq_if steps_io_wf_maintained)


subsection "Return Rule"

lemma show_execution_s_check_return:
  assumes "P PS r"
  shows "execution_s_check Inv crdtSpec PS (return r) P"
  using assms execution_s_check_def steps_io_return by fastforce


lemma execution_s_check_return:
  assumes finalCheck: "proof_state_wellFormed PS \<Longrightarrow> P PS r"
  shows "execution_s_check Inv crdtSpec PS (return r) P"
  using finalCheck
  unfolding execution_s_check_def steps_io_return_iff by auto


lemma execution_s_check_return_iff:
  shows "execution_s_check Inv crdtSpec PS (return r) P \<longleftrightarrow> (proof_state_wellFormed PS \<longrightarrow> P PS r)"
proof (intro iffI impI)
  assume " execution_s_check Inv crdtSpec PS (impl_language_loops.return r) P"
    and " proof_state_wellFormed PS"
  thus "P PS r"
    by (metis option.simps(5) steps_io_return_iff use_execution_s_check)
next
  assume " proof_state_wellFormed PS \<longrightarrow> P PS r "
  thus "execution_s_check Inv crdtSpec PS (impl_language_loops.return r) P"
    by (simp add: execution_s_check_return)
qed


subsection "Loop Rule"

lemma Loop_steps:
  fixes bdy :: "'any \<Rightarrow> (('any,'any) loopResult, 'operation::{embeddable,valueType}, 'any::{small,valueType}) io"
    and res :: "'a option"
    and init :: 'any
    and f :: "'any \<Rightarrow> 'a"
  assumes steps: "steps_io progInv qrySpec S (Loop init (loop_body_to_V bdy) (return \<circ> f)) S' res"
    and inv_initial: "LoopInv init S"
    and loop_iteration: "\<And>init S Sb br. \<lbrakk>LoopInv init S; steps_io progInv qrySpec S (bdy init) Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some (Break res) \<Rightarrow> P Sb (f res) | Some (Continue x) \<Rightarrow> LoopInv x Sb "
  shows "\<exists>r. res = Some r \<and>  P S' r"
proof -

  define cmd :: "('a, 'operation, 'any) impl_language_loops.io" 
    where "cmd = Loop init (loop_body_to_V bdy) (return \<circ> f)"

  define nextIteration :: "('any,'any) loopResult \<Rightarrow> ('a, 'operation, 'any) impl_language_loops.io"  where
    "nextIteration \<equiv> \<lambda>r. case r of Break x \<Rightarrow> return (f x) | Continue x \<Rightarrow> Loop x (loop_body_to_V bdy) (return \<circ> f)"

  obtain bdyCont 
    where "bdyCont = return (Continue init)"
      and cmd: "cmd = bdyCont \<bind> nextIteration"
    by (auto simp add: cmd_def nextIteration_def)

  have p1: "\<And>Sb br. \<lbrakk>steps_io progInv qrySpec S bdyCont Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some (Break res) \<Rightarrow> P Sb (f res) | Some (Continue acc) \<Rightarrow> LoopInv acc Sb"
    using \<open>bdyCont = impl_language_loops.return (Continue init)\<close> inv_initial steps_io_return by fastforce


  have p2: "steps_io progInv qrySpec S cmd S' res"
    using cmd_def steps by blast

  have "\<exists>r. res = Some r \<and>  P S' r"
    if "steps_io progInv qrySpec S cmd S' res"
      and "cmd = bdyCont \<bind> nextIteration"
      and "\<And>Sb br. \<lbrakk>steps_io progInv qrySpec S bdyCont Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some (Break r) \<Rightarrow> P Sb (f r) | Some (Continue x) \<Rightarrow> LoopInv x Sb"
    using that proof (induct arbitrary: bdyCont )
    case (steps_io_final S res)
    from WaitReturn_combined[OF `WaitReturn res = bdyCont \<bind> nextIteration`]
    obtain res' where "bdyCont = return (Break res')" and "res = f res'"
      by (cases bdyCont, auto simp add: return_def nextIteration_def split: loopResult.splits)

    hence "steps_io progInv qrySpec S bdyCont S (Some (Break res'))"
      by (simp add: steps_io_return_iff)

    thus ?case
      using \<open>res = f res'\<close> steps_io_final.prems(2) by fastforce
  next
    case (steps_io_error S cmd S' cmd')
    from `step_io progInv qrySpec S cmd S' cmd' False`
    have "\<exists>cmd'. step_io progInv qrySpec S bdyCont S' cmd' False"
      unfolding `cmd = bdyCont \<bind> nextIteration`
      by (cases bdyCont, auto simp add: step_io_def return_def while_def nextIteration_def split: prod.splits if_splits loopResult.splits)


    hence "steps_io progInv qrySpec S bdyCont S' None"
      using steps_io.steps_io_error by blast
    hence False
      using steps_io_error.prems(2) by force
    thus ?case ..
  next
    case (steps_io_step Sx cmd1 Sx' cmd' Sx'' res bdyCont )


    show ?case
    proof (cases "\<exists>r. bdyCont = return r")
      case True \<comment> \<open>Loop iteration done\<close>
      from this
      obtain bdyR where "bdyCont = return bdyR"
        by blast
      show "?thesis"
      proof (cases bdyR)
        case (Break res) \<comment> \<open>Loop done\<close>
        hence "bdyCont = return (Break res)"
          using `bdyCont = return bdyR` by simp


        with `cmd1 = bdyCont \<bind> nextIteration`
        have "cmd1 = return (f res)"
          using nextIteration_def by auto

        with `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
        have False \<comment> \<open>Actually this case is handled in steps-io-final as no step is done.\<close>
          by (auto simp add: step_io_def return_def)

        thus ?thesis ..
      next
        case (Continue acc) \<comment> \<open>Start loop again.\<close>
        hence "bdyCont = return (Continue acc)"
          using `bdyCont = return bdyR` by simp

        with `cmd1 = bdyCont \<bind> nextIteration`
        have "cmd1 = Loop acc (loop_body_to_V bdy) (return \<circ> f)"
          using nextIteration_def by auto

        with `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
        have "cmd' = bdy acc \<bind> nextIteration"
          and "Sx' = Sx"
          by (auto simp add: while_def step_io_def nextIteration_def intro!: arg_cong_bind split: loopResult.splits)




        show ?thesis
          using `cmd' = bdy acc \<bind> nextIteration`
        proof (rule steps_io_step)  

          show "case br of None \<Rightarrow> False | Some (Continue x) \<Rightarrow> LoopInv x Sb | Some (Break b) \<Rightarrow> P Sb (f b) "
            if c0: "steps_io progInv qrySpec Sx' (bdy acc) Sb br"
            for  Sb br
          proof (rule loop_iteration)
            show "steps_io progInv qrySpec Sx' (bdy acc) Sb br" using c0 .

            have fstep: "steps_io progInv qrySpec Sx (WaitReturn (Continue acc)) Sx (Some (Continue acc))"
              by (rule steps_io_final)

            hence "steps_io progInv qrySpec Sx bdyCont Sx (Some (Continue acc))"
              using `bdyCont = return (Continue acc)` by (simp add: return_def)

            from steps_io_step.prems(2)[OF this, simplified]
            have "LoopInv acc Sx" .

            thus "LoopInv acc Sx'"
              using \<open>Sx' = Sx\<close> by simp 
          qed
        qed
      qed
    next
      case False
      hence "\<nexists>r. bdyCont = impl_language_loops.return r" .

      with `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
        and `cmd1 = bdyCont \<bind> nextIteration`
      obtain bdyCont'
        where "cmd' = bdyCont' \<bind> nextIteration"
          and "step_io progInv qrySpec Sx bdyCont Sx' bdyCont' True"
      proof (atomize_elim)

        show "\<exists>bdyCont'. cmd' = bdyCont' \<bind> nextIteration
          \<and>  step_io progInv qrySpec Sx bdyCont Sx' bdyCont' True"
        proof (cases bdyCont)
          case (Loop Linit Lbdy Lcont)
          with `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
            and `cmd1 = bdyCont \<bind> nextIteration`
          have c0: "cmd1 = Loop Linit Lbdy (\<lambda>x. Lcont x \<bind> nextIteration)"
            and  "bdyCont = Loop Linit Lbdy Lcont"
            and  "proof_state_wellFormed Sx"
            and  cmd'1: "cmd' = loop_body_from_V Lbdy Linit \<bind> (\<lambda>r. 
                      case r of Continue x \<Rightarrow> Loop x Lbdy (\<lambda>x. Lcont x \<bind> nextIteration)
                              | Break x \<Rightarrow> Lcont x \<bind> nextIteration)"
            and  "Sx' = Sx"
            by (auto simp add: step_io_def)

          show ?thesis
          proof (intro exI conjI)
            show "cmd' = (loop_body_from_V Lbdy Linit \<bind> (\<lambda>r. 
                      case r of Continue x \<Rightarrow> Loop x Lbdy (\<lambda>x. Lcont x)
                              | Break x \<Rightarrow> Lcont x))  \<bind> nextIteration"
              using cmd'1 by (auto simp add: intro!: arg_cong_bind  split: loopResult.splits)


            show "step_io progInv qrySpec Sx bdyCont Sx'
                 (loop_body_from_V Lbdy Linit \<bind> (\<lambda>r. case r of Continue x \<Rightarrow> Loop x Lbdy Lcont | Break x \<Rightarrow> Lcont x)) True"
              using `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
                and `cmd1 = Loop Linit Lbdy (\<lambda>x. Lcont x \<bind> nextIteration)`
              by (auto simp add: step_io_def Loop)
          qed

        qed (use `step_io progInv qrySpec Sx cmd1 Sx' cmd' True`
            ` \<nexists>r. bdyCont = impl_language_loops.return r`
            `cmd1 = bdyCont \<bind> nextIteration` 
            in \<open>auto simp add: step_io_def nextIteration_def return_def split: prod.splits\<close>)
      qed

      show ?thesis
        using \<open>cmd' = bdyCont' \<bind> nextIteration\<close> 
      proof (rule steps_io_step.hyps(3)) 

        show "case br of None \<Rightarrow> False | Some (Continue x) \<Rightarrow> LoopInv x Sb | Some (Break b) \<Rightarrow> P Sb (f b)"
          if c0: "steps_io progInv qrySpec Sx' bdyCont' Sb br"
          for  Sb br
        proof (rule steps_io_step)
          show "steps_io progInv qrySpec Sx bdyCont Sb br"
          proof (rule steps_io.steps_io_step)

            show "steps_io progInv qrySpec Sx' bdyCont' Sb br"
              using `steps_io progInv qrySpec Sx' bdyCont' Sb br` .


            show "step_io progInv qrySpec Sx bdyCont Sx' bdyCont' True"
              using `step_io progInv qrySpec Sx bdyCont Sx' bdyCont' True` .
          qed
        qed
      qed
    qed
  qed

  thus "\<exists>r. res \<triangleq> r \<and> P S' r"
    using p1 cmd p2 by blast
qed



lemma steps_io_bind:
  assumes steps: "steps_io progInv qrySpec S cmd Sb br"
    and cmd: "cmd = (cmd1 \<bind> (\<lambda>x. return (f x)))"
  shows "\<exists>x. steps_io progInv qrySpec S cmd1 Sb x \<and> br = (case x of None \<Rightarrow> None | Some r \<Rightarrow> Some (f r))"
  using steps_io_bind_split[OF steps[simplified cmd]] 
  by (auto simp add: dest!: steps_io_return)

lemma steps_io_bind':
  assumes "steps_io progInv qrySpec S (cmd \<bind> (\<lambda>x. return (f x))) Sb br"
  shows "\<exists>x. steps_io progInv qrySpec S cmd Sb x \<and> br = (case x of None \<Rightarrow> None | Some r \<Rightarrow> Some (f r))"
  using assms steps_io_bind by blast


lemma execution_s_check_Loop:
  fixes init :: "'any::valueType"
    and LoopInv :: "('b::valueType, 'any, 'operation::valueType) proof_state \<Rightarrow> 'any \<Rightarrow> ('b, 'any, 'operation) proof_state \<Rightarrow> bool"
    and f :: "'any \<Rightarrow> 'a"
  assumes 
    inv_pre: "LoopInv PS init PS"
    and cont: "
\<And>acc PSl. \<lbrakk>
  LoopInv PS acc PSl
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec PSl (body acc)
    (\<lambda>PS' r. case r of Break res \<Rightarrow> P PS' (f res)
                     | Continue acc' \<Rightarrow> LoopInv PS acc' PS' )"
  shows "execution_s_check Inv crdtSpec PS (Loop init (loop_body_to_V body) (return \<circ> f)) P"
  unfolding execution_s_check_def proof (intro allI impI)
  fix S' :: "('b, 'any, 'operation) proof_state" and res :: "'a option"
  assume steps_io: "steps_io Inv crdtSpec PS (Loop init (loop_body_to_V body) (return \<circ> f)) S' res"
    and PS_wf: "proof_state_wellFormed PS"







  have "\<exists>r::'a. res \<triangleq> r \<and> P S' r"
    using steps_io 
  proof (rule Loop_steps[where LoopInv="\<lambda>a s. LoopInv PS a s \<and> proof_state_wellFormed s"]; use nothing in \<open> (intro conjI)?; (elim conjE)?\<close>)

    show "LoopInv PS init PS"
      by (simp add: inv_pre)

    show "proof_state_wellFormed PS"
      by (simp add: PS_wf )

    show "case br of None \<Rightarrow> False 
            | Some (Continue x) \<Rightarrow> LoopInv PS x Sb \<and> proof_state_wellFormed Sb 
            | Some (Break res) \<Rightarrow> P Sb (f res)"
      if c0: "steps_io Inv crdtSpec S (body init) Sb br"
        and c1: "LoopInv PS init S"
        and c2: "proof_state_wellFormed S"
      for  init S Sb br
    proof -

      from use_execution_s_check[OF cont[OF c1] c0 c2]
      have "case br of None \<Rightarrow> False | Some (Continue acc') \<Rightarrow> LoopInv PS acc' Sb
          | Some (Break res) \<Rightarrow> P Sb (f res)" .

      thus ?thesis
        using c0 c2  
        by (auto split: option.splits loopResult.splits intro: steps_io_wf_maintained_Some)


    qed
  qed


  thus "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
    by auto
qed

text "Loops annotated with loop invariant for easier generation of verification conditions:"

definition loop_a :: "
    'a::countable 
  \<Rightarrow> (('proc, 'any, 'operation) proof_state \<Rightarrow> 'a  \<Rightarrow> ('proc, 'any, 'operation) proof_state \<Rightarrow> bool)
  \<Rightarrow> ('a \<Rightarrow> (('a,'b::countable) loopResult, 'operation::small, 'any::{small,natConvert} ) io) 
  \<Rightarrow> ('b, 'operation, 'any) io" where
  "loop_a init LoopInv body \<equiv> loop init body"

lemma annotate_loop:
  "loop init body = loop_a init LoopInv body"
  unfolding loop_a_def by simp


definition  while_a :: "(('proc, 'any, 'operation) proof_state \<Rightarrow> ('proc, 'any, 'operation) proof_state \<Rightarrow> bool) \<Rightarrow>   (bool, 'operation::small, 'any::small) io \<Rightarrow> (unit, 'operation, 'any) io" where
  "while_a LoopInv body \<equiv> while body"

lemma annotate_while_loop:
  "while bdy = while_a LoopInv bdy"
  unfolding while_a_def by simp

definition  forEach_a :: "
    'e::countable list 
  \<Rightarrow> (('proc, 'any, 'operation) proof_state \<Rightarrow> 'e list \<Rightarrow> 'a list \<Rightarrow> 'e list  \<Rightarrow> ('proc, 'any, 'operation) proof_state \<Rightarrow> bool) 
  \<Rightarrow> ('e \<Rightarrow> ('a::countable, 'operation::small, 'any::{small,natConvert}) io) 
  \<Rightarrow> ('a list, 'operation, 'any) io" where
  "forEach_a coll LoopInv body \<equiv> forEach coll body"

lemma annotate_forEach_loop:
  "forEach elems bdy = forEach_a elems LoopInv bdy"
  unfolding forEach_a_def by simp

lemma loopResult_nested_case_simp:
  "(case (case r of Break x \<Rightarrow> Break (f x) | Continue x \<Rightarrow> Continue (g x)) of Break x \<Rightarrow> f' x | Continue x \<Rightarrow> g' x) = 
(case r of Break x \<Rightarrow> f' (f x) | Continue x \<Rightarrow> g' (g x))"
  by (auto split: loopResult.splits)

lemma execution_s_check_loop:
  fixes PS :: "('proc::valueType, 'any::{small,valueType,natConvert}, 'operation::valueType) proof_state" 
    and init :: "'acc::countable"
    and body ::  "'acc  \<Rightarrow> (('acc, 'a::countable) loopResult, 'operation,  'any) io"
  assumes inv_pre: "LoopInv PS init PS"
    and cont: "
\<And>acc PSl. \<lbrakk>
  LoopInv PS acc PSl
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec PSl (body acc) 
    (\<lambda>PS' r. case r of Break x \<Rightarrow> P PS' x
                     | Continue x \<Rightarrow> LoopInv PS x PS' )"
  shows "execution_s_check Inv crdtSpec PS (loop_a init LoopInv body) P"
  unfolding loop_a_def loop_def
  using inv_pre
proof (fuzzy_rule execution_s_check_Loop[where LoopInv="\<lambda>PS a PS'. LoopInv PS (fromAny a) PS'"])
  show "init = fromAny (intoAny init)"
    by simp

  show "execution_s_check Inv crdtSpec PSl (body (fromAny acc) \<bind> (\<lambda>res. return (
          case res of Continue x \<Rightarrow> (Continue (intoAny x)) 
                     | Break x \<Rightarrow> (Break (intoAny x))))) (\<lambda>PS' r. 
            case r of Continue acc' \<Rightarrow> LoopInv PS (fromAny acc') PS' 
                    | Break res \<Rightarrow> P PS' (fromAny res))"
    if loopInv: "LoopInv PS (fromAny acc) PSl"
    for  acc :: 'any  and  PSl
  proof (auto simp add: execution_s_check_return_iff loopResult_nested_case_simp intro!: execution_s_check_bind )
    from cont[OF loopInv]
    have cont2: "execution_s_check Inv crdtSpec PSl (body (fromAny acc))
                 (\<lambda>PS' r. case r of Continue x \<Rightarrow> LoopInv PS x PS' | Break x \<Rightarrow> P PS' x)" .

    thus "execution_s_check Inv crdtSpec PSl (body (fromAny acc))
     (\<lambda>S' r.
         proof_state_wellFormed S' \<longrightarrow>
         (case r of Continue acc' \<Rightarrow> LoopInv PS (fromAny (intoAny acc')) S'
          | Break acc' \<Rightarrow> P S' (fromAny (intoAny acc'))))"
      by (rule execution_s_check_strengthen, (auto split: loopResult.splits))
  qed
qed


lemma execution_s_check_while:
  assumes inv_pre: "LoopInv PS PS"
    and cont: "
\<And>PSl. \<lbrakk>
  LoopInv PS PSl
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec  PSl body 
    (\<lambda>PS' r. if r then P PS' ()
             else LoopInv PS PS' )"
  shows "execution_s_check Inv crdtSpec PS (while_a LoopInv body) P"
  unfolding while_a_def while_def
  using inv_pre
proof (fuzzy_rule execution_s_check_Loop[where LoopInv="\<lambda>PS a PS'. LoopInv PS PS'"])

  show "execution_s_check Inv crdtSpec PSl
        (body \<bind> (\<lambda>x. impl_language_loops.return ((if x then Break else Continue) ???)))
        (\<lambda>PS' r. case r of Continue acc' \<Rightarrow> LoopInv PS PS' | Break res \<Rightarrow> P PS' ())"
    if loopInv: "LoopInv PS PSl"
    for  acc::unit and PSl
  proof (auto simp add: execution_s_check_return_iff loopResult_nested_case_simp intro!: execution_s_check_bind )
    show "execution_s_check Inv crdtSpec PSl body
     (\<lambda>S' r. (r \<longrightarrow> proof_state_wellFormed S' \<longrightarrow> P S' ()) \<and> (\<not> r \<longrightarrow> proof_state_wellFormed S' \<longrightarrow> LoopInv PS S'))"
      using cont[OF loopInv]
      by (rule execution_s_check_strengthen, auto)
  qed
qed



lemma execution_s_check_forEach:
  assumes inv_pre: "LoopInv PS [] [] elems PS"
    and iter: "
\<And>done results t todo PSl. \<lbrakk>
  LoopInv PS done results (t#todo) PSl;
  length done = length results;
  elems = done@t#todo
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec PSl (body t) (\<lambda>PS' r. LoopInv PS (done@[t]) (results@[r]) todo PS')"
    and cont:
    "\<And>results PSl. \<lbrakk>
  LoopInv PS elems results [] PSl;
  length elems = length results
\<rbrakk> \<Longrightarrow> P PSl results"
  shows "execution_s_check Inv crdtSpec PS (forEach_a elems LoopInv body) P"
proof -

  define LI where "LI \<equiv> \<lambda>S0 acc S. 
  let n = length (snd acc);
      done = take n elems;
      todo = drop n elems
  in LoopInv S0 done (rev (snd acc)) todo S
   \<and> fst acc = todo 
   \<and> length (fst acc) + length (snd acc) = length elems"

  show ?thesis
    unfolding forEach_a_def forEach_def annotate_loop[where LoopInv=LI]
  proof (fuzzy_rule execution_s_check_loop)

    show "LI PS (elems, []) PS"
      using inv_pre by (auto simp add:  LI_def Let_def)


    show "execution_s_check Inv crdtSpec PSl
        (case acc of ([], acc) \<Rightarrow> impl_language_loops.return (Break (rev acc))
         | (x # xs, acc) \<Rightarrow> body x \<bind> (\<lambda>r. impl_language_loops.return (Continue (xs, r # acc))))
        (\<lambda>PS' r. case r of Continue x \<Rightarrow> LI PS x PS' | Break x \<Rightarrow> P PS' x)"
      if LI: "LI PS acc PSl"
      for  acc PSl
    proof (cases "fst acc = []")
      case True

      with LI
      have "LoopInv PS elems (rev (snd acc)) [] PSl"
        and "length (snd acc) = length elems"
        by (auto simp add: LI_def Let_def)

      show ?thesis
        using True
        apply (auto simp add:  split: prod.splits intro!: show_execution_s_check_return)
        using \<open>LoopInv PS elems (rev (snd acc)) [] PSl\<close> \<open>length (snd acc) = length elems\<close> cont by auto
    next
      case False
      obtain todo resultsR where acc_def: "acc = (todo, resultsR)" by force

      obtain t todoRest where todo_def: "todo = t#todoRest"
        using False acc_def list.exhaust by auto 


      define "done" where "done \<equiv> take (length resultsR) elems"

      from LI 
      have LI1: "LoopInv PS (take (length resultsR) elems) (rev resultsR) (drop (length resultsR) elems) PSl"
        and LI2: "length elems - length resultsR + length resultsR = length elems"
        and LI3: "todo = drop (length resultsR) elems"
        by (auto simp add: LI_def Let_def acc_def)

      from LI1
      have LoopInv: "LoopInv PS done (rev resultsR) (t # todoRest) PSl"
        using LI3 done_def todo_def by auto

      have length_done: "length done = length (rev resultsR)"
        using LI2 done_def by auto

      have elems: "elems = done @ t # todoRest"
        using todo_def LI3 done_def split_take by blast

      from iter[OF LoopInv length_done elems]
      show ?thesis
        \<comment> \<open>Could simplify this with execution-s-check bind simplification lemma\<close>
        by (auto simp add: acc_def todo_def execution_s_check_def LI_def Let_def elems length_done split: option.splits dest!: steps_io_bind', blast)
    qed
  qed
qed



subsection "References"


lemma execution_s_check_makeRef:
  assumes cont: "
\<And>ref. \<lbrakk>
  ref = freshRef (dom (ps_store PS))
\<rbrakk> \<Longrightarrow> P  
    (PS\<lparr>
      ps_store := (ps_store PS)(ref \<mapsto> intoAny a)
     \<rparr>) 
    (Ref ref)
    "
  shows "execution_s_check Inv crdtSpec PS  (makeRef a) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>r. makeRef a \<noteq> WaitReturn r"
    by (simp add: makeRef_def)

  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if step: "step_io Inv crdtSpec PS (makeRef a) PS' cmd' ok"
      and PS_wf: "proof_state_wellFormed PS"
    for  PS' cmd' ok
  proof
    have [simp]: "finite (dom (ps_store PS))"
      by (simp add: PS_wf proof_state_wellFormed'_finite_store proof_state_wellFormed_implies)

    from step
    have  c1: "ok"
      and c2: "PS' = PS\<lparr>ps_store := ps_store PS(freshRef (dom (ps_store PS)) \<mapsto> intoAny a)\<rparr>"
      and c3: "cmd' = return (Ref (freshRef (dom (ps_store PS))))"
      by (auto simp add: makeRef_def step_io_def Let_def return_def)

    show "ok" using `ok` .

    show "\<exists>res. cmd' = impl_language_loops.return res \<and> P PS' res"
      using c2 c3 cont by blast
  qed
qed


lemma execution_s_check_read:
  assumes validRef: "iref r \<in> dom (ps_store PS)"
    and cont: "P PS (s_read (ps_store PS) r)"
  shows "execution_s_check Inv crdtSpec PS  (read r) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>ra. read r \<noteq> impl_language_loops.io.WaitReturn ra"
    by (simp add: read_def)

  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if c0: "step_io Inv crdtSpec PS (read r) PS' cmd' ok"
      and c1: "proof_state_wellFormed PS"
    for  PS' cmd' ok
    using that validRef cont[simplified s_read_def] 
      proof_state_wellFormed'_finite_store[OF proof_state_wellFormed_implies[OF c1]]
    by (auto simp add:  step_io_def read_def return_def intro!: exI)
qed

lemma execution_s_check_assign:
  assumes validRef: "iref r \<in> dom (ps_store PS)"
    and cont: "
    P (PS\<lparr>ps_store := ps_store PS(iref r \<mapsto> intoAny v)\<rparr>) ()"
  shows "execution_s_check Inv crdtSpec PS  (assign r v) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>ra. r :\<leftarrow> v \<noteq> impl_language_loops.io.WaitReturn ra"
    by (simp add: assign_def)

  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if c0: "step_io Inv crdtSpec PS (r :\<leftarrow> v) PS' cmd' ok"
      and c1: "proof_state_wellFormed PS"
    for  PS' cmd' ok
    using that validRef cont proof_state_wellFormed_finite_store by (auto simp add:  step_io_def assign_def return_def, blast+ )

qed

lemma execution_s_check_newId:
  assumes infPred: "infinite (Collect tc)"
    and cont: "\<And>v vn. \<lbrakk>
    tc v;
    vn \<notin> knownIds PS;
    vn \<notin> ps_generatedLocal PS;
    uniqueIds v = {vn};
    uid_is_private_S (ps_i PS) PS vn
\<rbrakk> \<Longrightarrow>
    P 
      (PS\<lparr> ps_localKnown := ps_localKnown PS \<union> {vn},
          ps_generatedLocal := ps_generatedLocal PS \<union> {vn}, 
           ps_generatedLocalPrivate  := ps_generatedLocalPrivate PS \<union> {vn}
           \<rparr>)
      v"
  shows "execution_s_check Inv crdtSpec PS  (newId tc) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>r. impl_language_loops.newId tc \<noteq> impl_language_loops.io.WaitReturn r"
    by (simp add: newId_def)

  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if c0: "step_io Inv crdtSpec PS (impl_language_loops.newId tc) PS' cmd' ok"
      and c1: "proof_state_wellFormed PS"
    for PS' cmd' ok
    using that 
  proof (auto simp add:  step_io_def newId_def, intro exI conjI)
    show "impl_language_loops.io.WaitReturn uidv = impl_language_loops.return uidv" for uidv 
      by (simp add: return_def)

    show "P (PS\<lparr>ps_localKnown := insert uid (ps_localKnown PS), ps_generatedLocal := insert uid (ps_generatedLocal PS), ps_generatedLocalPrivate := insert uid (ps_generatedLocalPrivate PS)\<rparr>) uidv"
      if c0: "proof_state_wellFormed PS"
        and c1: "cmd' = impl_language_loops.io.WaitReturn uidv"
        and c2: "ok"
        and c3: "proof_state_wellFormed (PS\<lparr>ps_localKnown := insert uid (ps_localKnown PS), ps_generatedLocal := insert uid (ps_generatedLocal PS), ps_generatedLocalPrivate := insert uid (ps_generatedLocalPrivate PS)\<rparr>)"
        and c4: "uniqueIds uidv = {uid}"
        and c5: "uid \<notin> ps_generatedLocal PS"
        and c6: "uid_fresh uid PS"
        and c7: "tc uidv"
        and c8: "PS' = PS \<lparr>ps_localKnown := insert uid (ps_localKnown PS), ps_generatedLocal := insert uid (ps_generatedLocal PS), ps_generatedLocalPrivate := insert uid (ps_generatedLocalPrivate PS)\<rparr>"
        and c9: "step_io Inv crdtSpec PS (impl_language_loops.newId tc) PS' cmd' ok"
        and c10: "proof_state_wellFormed PS"
      for  uidv uid
    proof (fuzzy_rule cont)
      show "tc uidv" using c7 .

      show "uid \<notin> ps_generatedLocal PS"
        using c5 by simp
      from `uid_fresh uid PS`
      show "uid \<notin> knownIds PS"
        by (auto simp add: uid_fresh_def uid_is_private'_def)
      show "uniqueIds uidv = {uid}"
        by (simp add: c4)

      show "uid_is_private_S (ps_i PS) PS uid"
        using c6 uid_fresh_def by blast

    qed auto
  qed
qed

lemma ps_growing_to_proof_state_wellFormed:
  assumes "ps_growing PS PS' tx"
  shows "proof_state_wellFormed PS'"
  using assms 
  unfolding ps_growing_def proof_state_wellFormed_def
  by auto

lemma ps_growing_causallyConsistent:
  assumes "ps_growing PS PS' tx"
  shows "causallyConsistent (happensBefore PS') (ps_vis PS')"
  using assms
  by (clarsimp simp add: ps_growing_def proof_state_wellFormed_def proof_state_rel_def)
    (metis wellFormed_state_causality(1))

lemma ps_growing_transactionConsistent_atomic:
  assumes "ps_growing PS PS' tx"
  shows "transactionConsistent_atomic (callOrigin PS') (ps_vis PS')"
  using assms
  by (clarsimp simp add: ps_growing_def proof_state_wellFormed_def proof_state_rel_def transactionConsistent_atomic_def)
    (metis (no_types, lifting) wellFormed_state_transaction_consistent(2))

lemma ps_growing_invocationOp:
  assumes "ps_growing PS PS' tx"
  shows "\<And>i op. invocationOp PS i \<triangleq> op \<Longrightarrow> invocationOp PS' i \<triangleq> op"
  using assms 
  unfolding ps_growing_def proof_state_wellFormed_def
proof (clarsimp, fuzzy_goal_cases A)
  case (A i op CS CS')

  have "invocationOp CS i \<triangleq> op"
    using A.invocationOp_eq A.proof_state_rel proof_state_rel_invocationOp by fastforce

  from state_monotonicGrowth_invocationOp[OF A.state_monotonicGrowth `invocationOp CS i \<triangleq> op`]
  have "invocationOp CS' i \<triangleq> op"
    by simp


  then show ?case
    using A.proof_state_rel2 proof_state_rel_invocationOp by force 
qed




lemma execution_s_check_beginAtomic:
  assumes cont: "\<And>tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis'
 s_invocationOp' s_invocationRes' PS'. \<lbrakk>
Inv (invariantContext.truncate PS');
s_transactionOrigin' tx = None;
\<And>i op. invocationOp PS i \<triangleq> op \<Longrightarrow> s_invocationOp' i \<triangleq> op;
\<And>c. s_callOrigin' c \<noteq> Some tx;
ps_vis PS \<subseteq> vis';
vis' \<subseteq> dom s_calls';
ps_firstTx PS \<Longrightarrow> (\<And>c tx. s_callOrigin' c \<triangleq> tx \<Longrightarrow> s_transactionOrigin' tx \<noteq> Some (ps_i PS));
\<comment> \<open>consistency: \<close>
causallyConsistent s_happensBefore' vis';
transactionConsistent_atomic s_callOrigin' vis';
\<forall>v\<in>ps_generatedLocalPrivate PS. uid_is_private' (ps_i PS) s_calls' s_invocationOp' s_invocationRes' s_knownIds' v;
PS' = (PS\<lparr>calls := s_calls',
          happensBefore := s_happensBefore',
          callOrigin := s_callOrigin',
          transactionOrigin := s_transactionOrigin',
          knownIds := s_knownIds',
          invocationOp := s_invocationOp'(ps_i PS := invocationOp PS (ps_i PS)),
          invocationRes := s_invocationRes'(ps_i PS := None),
          ps_vis := vis',
          ps_localCalls := [],
          ps_tx := Some tx
        \<rparr>);   
proof_state_wellFormed PS';
ps_growing PS PS' tx
\<rbrakk> \<Longrightarrow>
    P PS' ()"
  shows "execution_s_check Inv crdtSpec PS beginAtomic P"
proof (rule execution_s_check_proof_rule)

  show "\<And>r. beginAtomic \<noteq> WaitReturn r"
    by (simp add: beginAtomic_def)

  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if steo_io: "step_io Inv crdtSpec PS beginAtomic PS' cmd' ok"
      and wf: "proof_state_wellFormed PS"
    for  PS' cmd' ok
    using steo_io 
  proof (auto simp add:  step_io_def beginAtomic_def, fuzzy_goal_cases Step)
    case (Step t vis' calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes')

    find_theorems name: "Step."

    from Step.ps_growing
    obtain CS CS'
      where CS_rel: "proof_state_rel PS CS"
        and CS'_rel: "proof_state_rel
      (PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
            transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',
            invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr>)
      CS'" 
        and growth: "state_monotonicGrowth (ps_i PS) CS
      (CS'\<lparr>transactionStatus := (transactionStatus CS')(t := None),
             transactionOrigin := (transactionOrigin CS')(t := None),
             currentTransaction := (currentTransaction CS')(ps_i PS := None),
             localState := (localState CS')(ps_i PS := localState CS (ps_i PS)),
             visibleCalls := (visibleCalls CS')(ps_i PS := visibleCalls CS (ps_i PS))\<rparr>)"
      unfolding ps_growing_def
      by auto

    show "P (PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',                   transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',                   invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr>) ()"
    proof (fuzzy_rule cont[where s_transactionOrigin'="transactionOrigin'(t := None)"])

      have "invocationOp CS' = invocationOp'"
        using CS'_rel by (auto simp add: proof_state_rel_def)

      have "invocationRes CS' = invocationRes'"
        using CS'_rel by (auto simp add: proof_state_rel_def)

      have "invocationOp CS = invocationOp PS"
        using CS_rel by (auto simp add: proof_state_rel_def)

      have "invocationRes CS = invocationRes PS"
        using CS_rel by (auto simp add: proof_state_rel_def)

      show "(transactionOrigin'(t := None)) t = None"
        by simp

      show "PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
          transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',
          invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr> 
          = PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
              transactionOrigin := transactionOrigin'(t := None),
              knownIds := knownIds',
              invocationOp := invocationOp'(ps_i PS := invocationOp PS (ps_i PS)),
              invocationRes := invocationRes'(ps_i PS := None), ps_vis := vis', ps_localCalls := [], ps_tx := Some t\<rparr>"
      proof (auto simp add: proof_state_ext)
        show "ps_localCalls PS = []"
          using wf
        proof (rule proof_state_wellFormed_localCalls)
          show "ps_tx PS = None"
            using \<open>ps_tx PS = None\<close> by auto
        qed

        show " transactionOrigin' = transactionOrigin'(t := None)"
          using Step.transactionOrigin'_eq by auto




        have "invocationOp' (ps_i PS) = invocationOp PS (ps_i PS)"
          using state_monotonicGrowth_invocationOp_i[OF growth]
          by (auto simp add: \<open>invocationOp CS = invocationOp PS\<close> \<open>invocationOp CS' = invocationOp'\<close>)

        thus "invocationOp' = invocationOp'(ps_i PS := invocationOp PS (ps_i PS))"
          by auto
        show "invocationRes' = invocationRes'(ps_i PS := None)"
          using growth
          by (metis CS'_rel Step.PS'___def \<open>invocationRes CS' = invocationRes'\<close> fun_upd_idem_iff proof_state_rel_facts(1) proof_state_rel_facts(10) state_wellFormed_no_result_when_running steo_io step_io_same_i)
      qed

      from show_proof_state_wellFormed[OF CS_rel]
      have "proof_state_wellFormed PS" .

      from proof_state_wellFormed_to_state_wellFormed[OF `proof_state_wellFormed PS`]
      obtain s_prog s_transactionStatus s_generatedIds s_localState s_currentProc s_visibleCalls s_currentTransaction
        where "(\<forall>tx'. ps_tx PS \<noteq> Some tx' \<longrightarrow> s_transactionStatus tx' \<noteq> Some Uncommitted)"
          and "ps_generatedLocal PS = {x. s_generatedIds x \<triangleq> ps_i PS}"
          and "(\<exists>ps_ls. s_localState (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ps_ls))"
          and "s_currentProc (ps_i PS) \<triangleq> impl_language_loops.toImpl"
          and "s_visibleCalls (ps_i PS) \<triangleq> (ps_vis PS \<union> set (ps_localCalls PS))"
          and "s_currentTransaction (ps_i PS) = ps_tx PS"
          and wf: "state_wellFormed
                \<lparr>calls = calls PS, happensBefore = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
                   callOrigin = map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
                   transactionOrigin = (case ps_tx PS of Some t \<Rightarrow> transactionOrigin PS(t \<mapsto> ps_i PS) | None \<Rightarrow> transactionOrigin PS), 
                   knownIds = knownIds PS, invocationOp = invocationOp PS,
                   invocationRes = invocationRes PS, prog = s_prog, transactionStatus = s_transactionStatus,
                   generatedIds = s_generatedIds, localState = s_localState, currentProc = s_currentProc,
                   visibleCalls = s_visibleCalls, currentTransaction = s_currentTransaction\<rparr>"
        by blast

      from proof_state_wellFormed_to_state_wellFormed[OF Step.proof_state_wellFormed]
      obtain s_prog' s_transactionStatus' s_generatedIds' s_localState' ps_ls' s_currentProc' s_visibleCalls' s_currentTransaction'
        where "\<forall>tx'. t \<noteq> tx' \<longrightarrow> s_transactionStatus' tx' \<noteq> Some Uncommitted"
          and "ps_generatedLocal PS = {x. s_generatedIds' x \<triangleq> ps_i PS}"
          and  "s_localState' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ps_ls')"
          and  "s_currentProc' (ps_i PS) \<triangleq> impl_language_loops.toImpl"
          and  "s_visibleCalls' (ps_i PS) \<triangleq> (vis' \<union> set (ps_localCalls PS))"
          and  "s_currentTransaction' (ps_i PS) \<triangleq> t"
          and wf': "state_wellFormed \<lparr>
                      calls = calls', 
                      happensBefore = updateHb happensBefore' vis' (ps_localCalls PS),             
                      callOrigin = map_update_all callOrigin' (ps_localCalls PS) t, 
                      transactionOrigin = transactionOrigin'(t \<mapsto> ps_i PS),             
                      knownIds = knownIds', 
                      invocationOp = invocationOp', 
                      invocationRes = invocationRes', 
                      prog = s_prog',             
                      transactionStatus = s_transactionStatus', 
                      generatedIds = s_generatedIds', 
                      localState = s_localState',             
                      currentProc = s_currentProc', 
                      visibleCalls = s_visibleCalls', 
                      currentTransaction = s_currentTransaction'\<rparr>"
        by auto


      from show_proof_state_wellFormed[OF CS'_rel]
      show "proof_state_wellFormed
      (PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
            transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',
            invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr>)"
        by auto


      show "\<And>i op. invocationOp PS i \<triangleq> op \<Longrightarrow> invocationOp' i \<triangleq> op"
        using state_monotonicGrowth_invocationOp[OF growth, simplified]
        by (simp add: \<open>invocationOp CS = invocationOp PS\<close> \<open>invocationOp CS' = invocationOp'\<close>)

      have "Inv \<lparr>calls = calls', happensBefore = happensBefore', callOrigin = callOrigin',
           transactionOrigin = (transactionOrigin'(t := None)), knownIds = knownIds',
           invocationOp = invocationOp'(ps_i PS := invocationOp PS (ps_i PS)),
           invocationRes = invocationRes'(ps_i PS := None)\<rparr>"
      proof (fuzzy_rule Step.Inv, auto simp add: invariantContext.defs)
        show "invocationOp' = invocationOp'(ps_i PS := invocationOp PS (ps_i PS))"
          using state_monotonicGrowth_invocationOp_i[OF growth]
          using \<open>invocationOp CS = invocationOp PS\<close> \<open>invocationOp CS' = invocationOp'\<close> by auto

        have "invocationRes PS (ps_i PS) = None"
          using wf_localState_noReturn
          using CS_rel \<open>invocationRes CS = invocationRes PS\<close> proof_state_rel_facts(10) proof_state_rel_wf by fastforce

        hence "invocationRes' (ps_i PS) = None"
          using state_monotonicGrowth_invocationRes_i[OF growth]
          by (metis CS'_rel Step.PS'___def \<open>invocationRes CS' = invocationRes'\<close> proof_state_rel_facts(1) proof_state_rel_facts(10) state_wellFormed_no_result_when_running steo_io step_io_same_i)

        thus "invocationRes' = invocationRes'(ps_i PS := None)"
          by auto

        show "transactionOrigin' = transactionOrigin'(t := None)"
          using Step.transactionOrigin'_eq by auto


      qed
      thus "Inv (invariantContext.truncate
          (PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin', transactionOrigin := transactionOrigin',
                knownIds := knownIds', invocationOp := invocationOp', invocationRes := invocationRes', ps_tx := Some t,
                ps_vis := vis'\<rparr>))"
      proof (auto simp add: invariantContext.defs elim!: back_subst[where P=Inv])
        show "transactionOrigin'(t := None) = transactionOrigin'"
          using Step.transactionOrigin'_eq by auto
        show "invocationOp'(ps_i PS := invocationOp PS (ps_i PS)) = invocationOp'"
          by (metis CS_rel \<open>\<And>op ia. invocationOp PS ia \<triangleq> op \<Longrightarrow> invocationOp' ia \<triangleq> op\<close> \<open>invocationOp CS = invocationOp PS\<close> fun_upd_idem option.discI option.exhaust proof_state_rel_impl proof_state_rel_wf wf_localState_currentProc wf_localState_needs_invocationOp)
        show "invocationRes'(ps_i PS := None) = invocationRes'"
          using state_monotonicGrowth_invocationRes[OF growth, simplified]
          using CS'_rel \<open>invocationRes CS' = invocationRes'\<close> proof_state_rel_facts(10) proof_state_rel_wf wf_localState_noReturn by fastforce
      qed


      show "\<And>c. callOrigin' c \<noteq> Some t"
        using Step.All_not_callOrigin'_eq
        by auto


      show "vis' \<subseteq> dom calls'"
        by (meson Step.consistentSnapshotH consistentSnapshotH_def)



      show " causallyConsistent happensBefore' vis'"
        using Step.consistentSnapshotH consistentSnapshotH_def by blast

      show " transactionConsistent_atomic callOrigin' vis'"
        by (meson Step.consistentSnapshotH consistentSnapshotH_def transactionConsistent_def)




      show "ps_growing PS
     (PS\<lparr>calls := calls', happensBefore := happensBefore', callOrigin := callOrigin',
           transactionOrigin := transactionOrigin', knownIds := knownIds', invocationOp := invocationOp',
           invocationRes := invocationRes', ps_tx := Some t, ps_vis := vis'\<rparr>)
     t"
        by (rule Step.ps_growing)


      show "\<And>c tx. \<lbrakk>ps_firstTx PS; callOrigin' c \<triangleq> tx\<rbrakk> \<Longrightarrow> (transactionOrigin'(t := None)) tx \<noteq> Some (ps_i PS)"
      proof (auto simp add: Step.All_implies_transactionOrigin_eq_eq[rule_format,symmetric])
        fix c tx
        assume "ps_firstTx PS"
          and "callOrigin' c \<triangleq> tx"
          and "tx \<noteq> t"
          and "transactionOrigin PS tx \<triangleq> ps_i PS"

        from state_monotonicGrowth_transactionOrigin_i[OF growth] `transactionOrigin PS tx \<triangleq> ps_i PS`
        have "transactionOrigin CS' tx \<triangleq> ps_i PS"
          using Step.ps_tx_eq
          by (auto simp add: `tx \<noteq> t` proof_state_rel_facts[OF CS_rel] dest: meta_spec[where x=tx] split: if_splits)


        from `callOrigin' c \<triangleq> tx` proof_state_rel_callOrigin[OF CS'_rel]
        have "callOrigin CS' c \<triangleq> tx"
          by (auto simp add: Step.ps_tx_eq proof_state_wellFormed_localCalls that(2))

        have "transactionStatus CS' tx \<noteq> Some Committed"
          using `ps_firstTx PS` `transactionOrigin CS' tx \<triangleq> ps_i PS` `callOrigin CS' c \<triangleq> tx`
          by (rule proof_state_rel_facts(21)[OF CS'_rel, simplified, THEN iffD1, rule_format])

        have "transactionStatus CS' tx = Some Uncommitted"
          by (metis (mono_tags, lifting) CS'_rel Step.PS'___def \<open>callOrigin CS' c \<triangleq> tx\<close> \<open>transactionOrigin CS' tx \<triangleq> ps_i PS\<close> \<open>transactionStatus CS' tx \<noteq> Some Committed\<close> proof_state_rel_facts(1) proof_state_rel_facts(12) state_wellFormed_ls_visibleCalls_callOrigin steo_io step_io_same_i wellFormed_currentTransaction_unique_h(2) wellFormed_state_transaction_consistent(1))

        moreover have "transactionStatus CS' tx \<noteq> Some Uncommitted"
          using proof_state_rel_facts(14)[OF CS'_rel] \<open>tx \<noteq> t\<close> by auto

        ultimately show "False"
          by blast
      qed

      show " ps_vis PS \<subseteq> vis'"
        using Step.chooseSnapshot_h chooseSnapshot_h_def by auto


      show "\<forall>v\<in>ps_generatedLocalPrivate PS. uid_is_private' (ps_i PS) calls' invocationOp' invocationRes' knownIds' v"
      proof auto
        fix v
        assume v: "v \<in> ps_generatedLocalPrivate PS"

        thm CS_rel
        thm CS'_rel
        from proof_state_rel_facts(24)[OF CS_rel, simplified]
        have "uid_is_private (ps_i PS) CS v" using v by simp

        from proof_state_rel_facts(24)[OF CS'_rel, simplified]
        have "uid_is_private (ps_i PS) CS' v" using v by simp
        hence a0: "new_unique_not_in_invocationOp invocationOp' v"
          and a1: "new_unique_not_in_calls calls' v"
          and a2: "new_unique_not_in_calls_result calls' v"
          and a3: "new_unique_not_in_invocationRes invocationRes' v"
          and a4: "v \<notin> knownIds'"
          and a5: "generatedIds CS' v \<triangleq> ps_i PS"
          and a6: "new_unique_not_in_other_invocations (ps_i PS) CS' v"
          by (auto simp add: uid_is_private_def proof_state_rel_facts[OF CS'_rel])

        show "uid_is_private' (ps_i PS) calls' invocationOp' invocationRes' knownIds' v"
          by (simp add: a0 a1 a2 a3 a4 uid_is_private'_def)
      qed
    qed
    show "impl_language_loops.io.WaitReturn () = impl_language_loops.return ()" 
      unfolding return_def ..
  qed
qed


lemma execution_s_check_call:
  assumes in_tx: "ps_tx PS \<triangleq> tx"
    and unique_wf: "uniqueIds OP \<subseteq> ps_localKnown PS"
    and cont: "\<And>c res. \<lbrakk>
toplevel_spec crdtSpec \<lparr>
      calls = calls PS, 
      happensBefore=updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)\<rparr>
      (ps_vis PS \<union> set (ps_localCalls PS))
       OP res
\<rbrakk> \<Longrightarrow>
    P
      (PS\<lparr>calls := (calls PS)(c \<mapsto> Call OP res), 
        ps_generatedLocalPrivate := ps_generatedLocalPrivate PS - uniqueIds OP,
        ps_localKnown := ps_localKnown PS \<union> uniqueIds res,
        ps_localCalls := ps_localCalls PS @ [c]
       \<rparr>)  
      res"
  shows "execution_s_check Inv crdtSpec PS (call OP) P"
proof (rule execution_s_check_proof_rule)

  show "\<And>r. impl_language_loops.call OP \<noteq> impl_language_loops.io.WaitReturn r" 
    unfolding call_def by simp


  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if step_io: "step_io Inv crdtSpec PS (call OP) PS' cmd' ok"
      and wf: "proof_state_wellFormed PS"
    for  PS' cmd' ok
  proof 

    from step_io  
    have ???
      apply (auto simp add: step_io_def call_def unique_wf return_def split: if_splits)
      sorry


    from step_io  
    obtain c y res
      where c0: "ok"
        and c1: "calls PS c = None"
        and c2: "ps_tx PS \<triangleq> y"
        and c3: "toplevel_spec crdtSpec (current_operationContext PS) (current_vis PS) OP res"
        and c4: "cmd' = return res"
        and PS'_def: "PS' = PS \<lparr>ps_localKnown := ps_localKnown PS \<union> uniqueIds res, ps_generatedLocalPrivate := ps_generatedLocalPrivate PS - uniqueIds OP, calls := calls PS(c \<mapsto> Call OP res), ps_localCalls := ps_localCalls PS @ [c]\<rparr>"
      by (auto simp add: step_io_def call_def unique_wf return_def split: if_splits)

    show "ok" using `ok` .

    show "\<exists>res. cmd' = impl_language_loops.return res \<and> P PS' res"
    proof (intro conjI exI[where x=res])
      show "cmd' = return res" using c4 .

      show "P PS' res"
      proof (fuzzy_rule cont[where c=c])

        from c3
        show "toplevel_spec crdtSpec \<lparr>calls = calls PS, happensBefore = updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)\<rparr>
           (ps_vis PS \<union> set (ps_localCalls PS)) OP res"
          unfolding current_operationContext_def current_vis_def by auto


        show "PS\<lparr>calls := calls PS(c \<mapsto> Call OP res),
           ps_generatedLocalPrivate := ps_generatedLocalPrivate PS - uniqueIds OP ,
           ps_localKnown := ps_localKnown PS \<union> uniqueIds res,
           ps_localCalls := ps_localCalls PS @ [c]\<rparr> =
          PS'"
          by (auto simp add: proof_state_ext PS'_def)
      qed
    qed
  qed
qed



lemma execution_s_check_endAtomic:
  assumes in_tx: "ps_tx PS \<triangleq> tx"
    and tx_nonempty: "(ps_localCalls PS) \<noteq> []"
    and cont: "\<And>PS'. \<lbrakk>
distinct (ps_localCalls PS);
\<And>c. c\<in>set (ps_localCalls PS) \<Longrightarrow> callOrigin PS c = None;
\<And>c. c\<in>set (ps_localCalls PS) \<Longrightarrow> c \<notin> ps_vis PS;
\<And>c c'. c\<in>set (ps_localCalls PS) \<Longrightarrow> (c,c') \<notin> happensBefore PS;
\<And>c c'. c\<in>set (ps_localCalls PS) \<Longrightarrow> (c',c) \<notin> happensBefore PS;
invocation_happensBeforeH
    (i_callOriginI_h (map_update_all (callOrigin PS) (ps_localCalls PS) tx) (transactionOrigin PS(tx \<mapsto> ps_i PS))) 
    (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
= 
(if ps_firstTx PS then
invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS)
 \<union> {i' | i' c'. c' \<in> ps_vis PS \<and> i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c'' \<triangleq> i' \<longrightarrow> c'' \<in> ps_vis PS ) } \<times> {ps_i PS}
else
invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS)
- {ps_i PS} \<times> {i'. (ps_i PS,i') \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS) });
PS' = PS\<lparr>happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS), 
        callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) tx,
        transactionOrigin := transactionOrigin PS(tx \<mapsto> ps_i PS),
        ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
        ps_localCalls := [],
        ps_firstTx := False,
        ps_tx := None
       \<rparr>

\<rbrakk> \<Longrightarrow>
    Inv (invariantContext.truncate PS')
    \<and> P PS' ()"
  shows "execution_s_check Inv crdtSpec PS endAtomic P"
proof (rule execution_s_check_proof_rule)

  show "\<And>r. impl_language_loops.endAtomic \<noteq> impl_language_loops.io.WaitReturn r"
    unfolding endAtomic_def by simp


  show "ok \<and> (\<exists>res. cmd' = return res \<and> P PS' res)"
    if step_io: "step_io Inv crdtSpec PS endAtomic PS' cmd' ok"
      and wf: "proof_state_wellFormed PS"
    for  PS' cmd' ok
  proof


    from step_io
    have cmd'_def: "cmd' = return ()"
      and PS'_def: "PS' =
     ps_tx_update Map.empty
      (PS\<lparr>happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
            callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
            transactionOrigin := transactionOrigin PS(the (ps_tx PS) \<mapsto> ps_i PS)\<rparr>)
     \<lparr>ps_localCalls := [], ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
        ps_firstTx := ps_firstTx PS \<and> ps_localCalls PS = []\<rparr>"
      and ok_def: "ok \<longleftrightarrow> Inv (invariantContext.truncate
              (ps_tx_update Map.empty
                (PS\<lparr>happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
                      callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
                      transactionOrigin := transactionOrigin PS(the (ps_tx PS) \<mapsto> ps_i PS)\<rparr>)
               \<lparr>ps_localCalls := [], ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
                  ps_firstTx := ps_firstTx PS \<and> ps_localCalls PS = []\<rparr>))"
      by (auto simp add: step_io_def endAtomic_def return_def split: io.splits if_splits)


    have cont2: "Inv (invariantContext.truncate PS')
      \<and> P PS' ()"
    proof (rule cont)


      show " PS' =
         (PS\<lparr>happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
              callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) tx, 
              transactionOrigin := transactionOrigin PS(tx \<mapsto> ps_i PS),
              ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
              ps_localCalls := [], 
              ps_firstTx := False, 
              ps_tx := None\<rparr>)"
        by (auto simp add: PS'_def proof_state_ext in_tx tx_nonempty)

      from `proof_state_wellFormed PS`
      obtain CS where rel: "proof_state_rel PS CS"
        using proof_state_wellFormed_def by blast

      hence "state_wellFormed CS"
        using proof_state_rel_wf by blast



      show "distinct (ps_localCalls PS)"
        using proof_state_rel_localCalls_distinct rel by blast
      show "\<And>c. c \<in> set (ps_localCalls PS) \<Longrightarrow> c \<notin> ps_vis PS"
        by (meson disjoint_iff_not_equal proof_state_rel_vis_localCalls_disjoint rel)
      show "\<And>c c'. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c, c') \<notin> happensBefore PS"
        by (meson FieldI1 disjoint_iff_not_equal proof_state_rel_happensBefore_localCalls_disjoint rel)
      show "\<And>c c'. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c', c) \<notin> happensBefore PS"
        by (meson FieldI2 disjoint_iff_not_equal proof_state_rel_happensBefore_localCalls_disjoint rel)
      show no_callOrigin: "\<And>c. c \<in> set (ps_localCalls PS) \<Longrightarrow> callOrigin PS c = None"
        by (meson disjoint_iff_not_equal domIff proof_state_rel_callOrigin_localCalls_disjoint rel)

      show "invocation_happensBeforeH
              (i_callOriginI_h (map_update_all (callOrigin PS) (ps_localCalls PS) tx) (transactionOrigin PS(tx \<mapsto> ps_i PS))) 
              (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
          = 
          (if ps_firstTx PS then
          invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS)
           \<union> {i' | i' c'. c' \<in> ps_vis PS \<and> i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c' \<triangleq> i' 
             \<and> (\<forall>c''. i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c'' \<triangleq> i' \<longrightarrow> c'' \<in> ps_vis PS ) } \<times> {ps_i PS}
          else
          invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS)
          - {ps_i PS} \<times> {i'. (ps_i PS,i') \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS) })"
      proof (rule if_cases)
        assume "ps_firstTx PS"
        show "invocation_happensBeforeH
          (i_callOriginI_h (map_update_all (callOrigin PS) (ps_localCalls PS) tx) (transactionOrigin PS(tx \<mapsto> ps_i PS))) 
          (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
          = 
          (
          invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS)) (happensBefore PS)
           \<union> {i' | i' c'. c' \<in> ps_vis PS \<and> i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c' \<triangleq> i' 
             \<and> (\<forall>c''. i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c'' \<triangleq> i' \<longrightarrow> c'' \<in> ps_vis PS ) } \<times> {ps_i PS}
          )"
        proof (fuzzy_rule(noabs) invocation_happensBeforeH_one_transaction_simp2[where to="transactionOrigin PS"])
          show "ps_localCalls PS \<noteq> []"
            using tx_nonempty by blast
          show "distinct (ps_localCalls PS)"
            by (simp add: \<open>distinct (ps_localCalls PS)\<close>)
          show "\<forall>c\<in>set (ps_localCalls PS). callOrigin PS c = None"
            using \<open>\<And>c. c \<in> set (ps_localCalls PS) \<Longrightarrow> callOrigin PS c = None\<close> by blast
          show "(transactionOrigin PS) tx = None"
            using in_tx proof_state_rel_transactionOriginNone rel by blast
          show "\<And>c t. callOrigin PS c \<triangleq> t \<Longrightarrow> (transactionOrigin PS) t \<noteq> Some (ps_i PS)"
            using proof_state_rel_firstTx[OF rel] no_callOrigin proof_state_rel_callOrigin[OF rel]
              proof_state_rel_noUncommitted[OF rel] proof_state_rel_txOrigin[OF rel]
              wf_transaction_status_iff_origin_dom[OF \<open>state_wellFormed CS\<close>]
            apply (auto simp add: \<open>ps_firstTx PS\<close> in_tx)
            by (metis (mono_tags, hide_lams) \<open>transactionOrigin PS tx = None\<close> domExists_simp insertCI map_update_all_get not_uncommitted_cases option.distinct(1))

          show "\<And>c. callOrigin PS c \<noteq> Some tx"
            using no_callOrigin in_tx map_update_all_Some_same proof_state_rel_callOrigin proof_state_rel_localCalls rel by fastforce
          show "\<And>c c'. (c, c') \<in> happensBefore PS \<Longrightarrow> \<exists>t. callOrigin PS c \<triangleq> t"
            by (metis (no_types, lifting) \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c', c) \<notin> happensBefore PS\<close> \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c, c') \<notin> happensBefore PS\<close> \<open>state_wellFormed CS\<close> domExists_simp domIff map_update_all_None proof_state_rel_callOrigin proof_state_rel_hb rel updateHb_simp2 wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l)
          show "\<And>c c'. (c, c') \<in> happensBefore PS \<Longrightarrow> \<exists>t. callOrigin PS c' \<triangleq> t"
            by (metis (no_types, lifting) \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c', c) \<notin> happensBefore PS\<close> domExists_simp domIff map_update_all_None proof_state_rel_callOrigin proof_state_rel_hb proof_state_rel_wf rel updateHb_simp2 wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_r)

        qed auto
      next 
        assume "\<not>ps_firstTx PS"
        with proof_state_rel_firstTx[OF rel]
        obtain old_c old_t 
          where "callOrigin CS old_c \<triangleq> old_t"
            and "transactionOrigin CS old_t \<triangleq> ps_i PS"
            and "transactionStatus CS old_t \<triangleq> Committed"
          by auto
        have "old_t \<noteq> tx"
          using \<open>state_wellFormed CS\<close> \<open>transactionStatus CS old_t \<triangleq> Committed\<close> in_tx proof_state_rel_currentTx rel wellFormed_currentTransaction_unique_h(2) by fastforce

        have "callOrigin PS old_c \<triangleq> old_t"
          using \<open>callOrigin CS old_c \<triangleq> old_t\<close> \<open>old_t \<noteq> tx\<close> in_tx map_update_all_Some_other proof_state_rel_callOrigin rel by fastforce
        have "transactionOrigin PS old_t \<triangleq> ps_i PS"
          using \<open>old_t \<noteq> tx\<close> \<open>transactionOrigin CS old_t \<triangleq> ps_i PS\<close> in_tx proof_state_rel_txOrigin rel by fastforce


        show "invocation_happensBeforeH
             (i_callOriginI_h (map_update_all (callOrigin PS) (ps_localCalls PS) tx) (transactionOrigin PS(tx \<mapsto> ps_i PS)))
             (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS)) =
            invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS))
             (happensBefore PS) -
            {ps_i PS} \<times>
            {i'.
             (ps_i PS, i')
             \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin PS) (transactionOrigin PS))
                 (happensBefore PS)}"
        proof (fuzzy_rule invocation_happensBeforeH_more_transactions_simp2)
          show "ps_localCalls PS \<noteq> []"
            using tx_nonempty by blast
          show "\<forall>c\<in>set (ps_localCalls PS). callOrigin PS c = None"
            using \<open>\<And>c. c \<in> set (ps_localCalls PS) \<Longrightarrow> callOrigin PS c = None\<close> by blast
          show "\<And>c. callOrigin PS c \<noteq> Some tx"
            by (metis (mono_tags, lifting) \<open>\<And>thesis. (\<And>CS. proof_state_rel PS CS \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<forall>c\<in>set (ps_localCalls PS). callOrigin PS c = None\<close> domI domIff in_tx map_update_all_Some_same mem_Collect_eq option.case_eq_if option.sel proof_state_rel_callOrigin proof_state_rel_localCalls)
          show "\<And>c c'. (c, c') \<in> happensBefore PS \<Longrightarrow> \<exists>t. callOrigin PS c \<triangleq> t"
            by (metis (no_types, lifting) \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c', c) \<notin> happensBefore PS\<close> \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c, c') \<notin> happensBefore PS\<close> domD domIff map_update_all_None proof_state_rel_callOrigin proof_state_rel_hb proof_state_rel_wf rel updateHb_simp2 wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l)
          show "(transactionOrigin PS) old_t \<triangleq> ps_i PS"
            using \<open>old_t \<noteq> tx\<close> \<open>transactionOrigin PS old_t \<triangleq> ps_i PS\<close> by auto
          show "callOrigin PS old_c \<triangleq> old_t"
            by (simp add: \<open>callOrigin PS old_c \<triangleq> old_t\<close>)
          show " Field (happensBefore PS) \<inter> set (ps_localCalls PS) = {}"
            using local.wf proof_state_wellFormed_disjoint_happensBefore_localCalls by blast

          show "\<And>c. i_callOriginI_h (callOrigin PS) (transactionOrigin PS) c \<triangleq> ps_i PS \<Longrightarrow> c \<in> ps_vis PS"
            using proof_state_rel_see_my_updates[OF rel] by (auto simp add: i_callOriginI_h_def split: option.splits if_splits)

          show "\<And>c c'. \<lbrakk>c' \<in> ps_vis PS; (c, c') \<in> happensBefore PS\<rbrakk> \<Longrightarrow> c \<in> ps_vis PS"
            by (smt Un_iff \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c', c) \<notin> happensBefore PS\<close> \<open>\<And>c' c. c \<in> set (ps_localCalls PS) \<Longrightarrow> (c, c') \<notin> happensBefore PS\<close> \<open>state_wellFormed CS\<close> proof_state_rel_hb proof_state_rel_vis rel updateHb_simp2 wf_vis_downwards_closed2)

        qed 
      qed
    qed

    thus "\<exists>res. cmd' = impl_language_loops.return res \<and> P PS' res"
      using cmd'_def by auto


    show ok unfolding ok_def 
      by (fuzzy_rule cont2[THEN conjunct1], auto simp add: proof_state_ext PS'_def)



  qed
qed

lemmas execution_s_check_endAtomic' = execution_s_check_endAtomic[rotated 2, OF context_conjI]






subsection "Verification Condition Generation Tactics"



lemmas repliss_proof_rules = 
  execution_s_check_makeRef
  execution_s_check_read
  execution_s_check_assign
  execution_s_check_loop
  execution_s_check_while
  execution_s_check_forEach
  execution_s_check_return
  execution_s_check_newId
  execution_s_check_beginAtomic
  execution_s_check_call
  execution_s_check_endAtomic'
  show_finalCheck
  execution_s_check_bind

method repliss_vcg_step1 uses asmUnfold = 
  (rule repliss_proof_rules; 
    ((subst(asm) asmUnfold)+)?; 
     (intro impI conjI)?; 
     clarsimp?; 
     (intro impI conjI)?; 
     (rule refl)?)

method repliss_vcg_step uses asmUnfold = 
  (repliss_vcg_step1 asmUnfold: asmUnfold; 
    (repliss_vcg_step asmUnfold: asmUnfold)?)

method repliss_vcg_l uses impl asmUnfold = 
  ((simp add: impl)?, 
    (unfold atomic_def skip_def)?, 
    simp?, 
    repliss_vcg_step asmUnfold: asmUnfold)




declare newId_def[language_construct_defs] 
  atomic_def[language_construct_defs]  
  beginAtomic_def [language_construct_defs] 
  call_def [language_construct_defs] 
  skip_def [language_construct_defs] 
  endAtomic_def [language_construct_defs] 
  return_def[language_construct_defs] 
  makeRef_def[language_construct_defs] 
  read_def[language_construct_defs] 
  assign_def[language_construct_defs] 
  update_def[language_construct_defs]
  while_a_def[language_construct_defs]
  \<comment> \<open>loop construct is not added here, since unfolding it might diverge.
    the loops added are just syntactic sugar for loop.\<close>





end
