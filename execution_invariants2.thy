theory execution_invariants2
  imports repliss_sem execution_invariants consistency commutativity "fuzzyrule.fuzzyrule"
begin


lemma wf_transaction_status_iff_origin_dom:
  assumes wf: "state_wellFormed S"
  shows "dom (transactionOrigin S) = dom (transactionStatus S)"
  by (smt Collect_cong dom_def local.wf wf_transaction_status_iff_origin)

lemma wf_generated_ids_invocation_exists:
  assumes wf: "state_wellFormed S"
and "invocationOp S i = None"
shows "generatedIds S uid \<noteq> Some i"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case by (simp add: initialState_def)
next
  case (step t a s)
  then show ?case by (auto simp add: initialState_def step.simps wf_localState_to_invocationOp split: if_splits)
qed

text "Every query can be explained with the corresponding query specification.

"


lemma wf_queryspec:
  assumes wf: "state_wellFormed S"
    and "calls S c \<triangleq> Call op r"
    and "prevCalls = {c'. (c',c)\<in>happensBefore S}"
    and "ctxt = getContextH (calls S |` prevCalls) (happensBefore S |r prevCalls) (Some prevCalls)"
  shows "querySpec (prog S) op ctxt r"
  using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case 
    by (simp add: initialState_def)
next
  case (step S1 a S2)
  from ` S1 ~~ a \<leadsto> S2`
  show ?case
  proof (cases rule: step.cases)
    case (local i ls f ls')
    then show ?thesis 
      using step by auto
  next
    case (newId i ls f ls' uid uidv ls'')
    then show ?thesis using step by auto
  next
    case (beginAtomic i ls f ls' t vis snapshot)
    then show ?thesis using step by auto
  next
    case (endAtomic i ls f ls' t)
    then show ?thesis using step by auto
  next
    case (dbop i ls f Op ls' t c' res vis)
    have [simp]: "prog S2 = prog S1"
      using prog_inv step.hyps(3) by blast


    show ?thesis 
    proof (cases "c = c'")
      case True

      have [simp]: "(c', c) \<notin> happensBefore S1" for c
        using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_l by blast
      have [simp]: "(c, c') \<notin> happensBefore S1" for c
        using local.dbop(7) step.hyps(1) wellFormed_happensBefore_calls_r by blast
      have [simp]: "c' \<notin> vis"
        using local.dbop(7) local.dbop(9) step.hyps(1) wellFormed_visibleCallsSubsetCalls2 by blast


      have "ctxt = getContext S1 i"
        by (auto simp add: step dbop True getContextH_def operationContext_ext restrict_map_def
            restrict_relation_def
            intro!: ext
            split: option.splits)


      with `querySpec (prog S1) Op (getContext S1 i) res`
      show ?thesis 
        using `calls S2 c \<triangleq> Call op r`
        by (simp add: dbop True)

    next
      case False
      show ?thesis 
      proof (simp add: step, fuzzy_rule step.hyps; (simp add: step dbop False; fail)?)
        show "calls S1 c \<triangleq> Call op r"
          using `calls S2 c \<triangleq> Call op r`
          by (simp add: dbop False)

        have [simp]: "c' \<notin> prevCalls"
          using False `calls S1 c' = None` wellFormed_happensBefore_calls_l[OF `state_wellFormed S1`]
          by (auto simp add: step dbop, blast)



        have h1: "(calls S2 |` prevCalls) = (calls S1 |` prevCalls)"
          by (auto simp add: restrict_map_def dbop False ) 

        have h2: "happensBefore S2 |r prevCalls = happensBefore S1 |r prevCalls"
          by (auto simp add: restrict_relation_def dbop False) 

        show "ctxt = getContextH (calls S1 |` prevCalls) (happensBefore S1 |r prevCalls) (Some prevCalls)"
          by (simp add: h1 h2 step.prems(3))
      qed
    qed

  next
    case (invocation i proc initialState impl)
    then show ?thesis using step by auto
  next
    case (return i ls f res)
    then show ?thesis using step by auto
  next
    case (fail i ls)
    then show ?thesis using step by auto
  next
    case (invCheck res i)
    then show ?thesis using step by auto
  qed
    
qed


end