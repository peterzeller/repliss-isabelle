theory unique_ids2
  imports unique_ids
    invariant_simps 
    unique_ids
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language
    topological_sort
begin


definition 
  "new_unique_not_in_invocationOp iop uidv \<equiv>
\<forall>i op. iop i \<triangleq> op \<longrightarrow> to_nat uidv \<notin> uniqueIds op "


definition 
  "new_unique_not_in_calls iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> to_nat uidv \<notin> uniqueIds op "

definition 
  "new_unique_not_in_calls_result iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> to_nat uidv \<notin> uniqueIds r "

definition
"new_unique_not_in_invocationRes ires uidv \<equiv> 
\<forall>i r. ires i \<triangleq> r \<longrightarrow> to_nat uidv \<notin> uniqueIds r "


(* TODO hmm, I have the feeling that I already did something similar ... *)
lemma growth_still_hidden:
  assumes g: "state_monotonicGrowth i S S'"
    and prog_wf: "program_wellFormed (prog S)"
    and a1: "new_unique_not_in_invocationOp (invocationOp S) uidv"
    and a2: "new_unique_not_in_calls (calls S) uidv"
    and a3: "new_unique_not_in_calls_result (calls S) uidv"
    and a4: "new_unique_not_in_invocationRes (invocationRes S) uidv"
    and a5: "to_nat uidv \<notin> knownIds S"
    and a6: "generatedIds S (to_nat uidv) \<triangleq> i"
shows "new_unique_not_in_invocationOp (invocationOp S') uidv
\<and> new_unique_not_in_calls (calls S') uidv
\<and> new_unique_not_in_calls_result (calls S') uidv
\<and> new_unique_not_in_invocationRes (invocationRes S') uidv
\<and> to_nat uidv \<notin> knownIds S'"
proof -
  from g obtain tr
    where wf: "state_wellFormed S"
    and steps: "S ~~ tr \<leadsto>* S'"
    and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
    and no_fail: "\<forall>i. (i, AFail) \<notin> set tr"
    by (auto simp add: state_monotonicGrowth_def)


  from steps no_i wf no_fail prog_wf a1 a2 a3 a4 a5 a6
  show ?thesis
  proof (induct rule: steps.induct)
    case (steps_refl S)
    then show ?case
      by auto
  next
    case (steps_step S1 tr S2 a S3)


    have "new_unique_not_in_invocationOp (invocationOp S2) uidv \<and>
        new_unique_not_in_calls (calls S2) uidv \<and>
        new_unique_not_in_calls_result (calls S2) uidv \<and>
        new_unique_not_in_invocationRes (invocationRes S2) uidv \<and> to_nat uidv \<notin> knownIds S2"
      by (rule steps_step, insert `\<forall>i. (i, AFail) \<notin> set (tr @ [a])`,auto simp add: steps_step)

    hence i1: "new_unique_not_in_invocationOp (invocationOp S2) uidv "
      and i2: "new_unique_not_in_calls (calls S2) uidv "
      and i3: "new_unique_not_in_calls_result (calls S2) uidv"
      and i4: "new_unique_not_in_invocationRes (invocationRes S2) uidv"
      and i5: "to_nat uidv \<notin> knownIds S2"
      by (auto simp add: steps_step)

    note invs = i1 i2 i3 i4 i5
   

    from `S2 ~~ a \<leadsto> S3`
    show ?case
    proof (induct rule: step.cases)
      case (local S i ls f ls')
      then show ?case
        using invs by (auto simp add: )
    next
      case (newId S i ls f ls' uid uidv ls'')
      then show ?case 
        using invs by (auto simp add: )
    next
      case (beginAtomic S i ls f ls' t vis snapshot)
      then show ?case using invs by (auto simp add: )
    next
      case (endAtomic S i ls f ls' t)
      then show ?case using invs by (auto simp add: )
    next
      case (dbop S i ls f Op ls' t c res vis)
      from dbop 
      show ?case using invs 
      proof (auto simp add: )

        show "new_unique_not_in_calls (\<lambda>a. if a = c then Some (Call Op res) else calls S a) uidv"
          if c0: "S2 = S"
            and c1: "a = (i, ADbOp c Op res)"
            and c2: "S3 = S \<lparr>localState := localState S(i \<mapsto> ls' res), calls := calls S(c \<mapsto> Call Op res), callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(i \<mapsto> insert c vis), happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>"
            and c3: "localState S i \<triangleq> ls"
            and c4: "currentProc S i \<triangleq> f"
            and c5: "f ls = DbOperation Op ls'"
            and c6: "currentTransaction S i \<triangleq> t"
            and c7: "calls S c = None"
            and c8: "querySpec (prog S) Op (getContextH (calls S) (happensBefore S) (Some vis)) res"
            and c9: "visibleCalls S i \<triangleq> vis"
            and c10: "new_unique_not_in_invocationOp (invocationOp S) uidv"
            and c11: "new_unique_not_in_calls (calls S) uidv"
            and c12: "new_unique_not_in_calls_result (calls S) uidv"
            and c13: "new_unique_not_in_invocationRes (invocationRes S) uidv"
            and c14: "to_nat uidv \<notin> knownIds S"
          sorry

        show "new_unique_not_in_calls_result (\<lambda>a. if a = c then Some (Call Op res) else calls S a) uidv"
          if c0: "S2 = S"
            and c1: "a = (i, ADbOp c Op res)"
            and c2: "S3 = S \<lparr>localState := localState S(i \<mapsto> ls' res), calls := calls S(c \<mapsto> Call Op res), callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(i \<mapsto> insert c vis), happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>"
            and c3: "localState S i \<triangleq> ls"
            and c4: "currentProc S i \<triangleq> f"
            and c5: "f ls = DbOperation Op ls'"
            and c6: "currentTransaction S i \<triangleq> t"
            and c7: "calls S c = None"
            and c8: "querySpec (prog S) Op (getContextH (calls S) (happensBefore S) (Some vis)) res"
            and c9: "visibleCalls S i \<triangleq> vis"
            and c10: "new_unique_not_in_invocationOp (invocationOp S) uidv"
            and c11: "new_unique_not_in_calls (calls S) uidv"
            and c12: "new_unique_not_in_calls_result (calls S) uidv"
            and c13: "new_unique_not_in_invocationRes (invocationRes S) uidv"
            and c14: "to_nat uidv \<notin> knownIds S"
          sorry
      qed





    next
      case (invocation S i proc initialState impl)
      then show ?case using invs apply (auto simp add: )
        by (auto simp add: new_unique_not_in_invocationOp_def)
    next
      case (return S i ls f res)
      then show ?case using invs apply (auto simp add: )
         apply (auto simp add: new_unique_not_in_invocationRes_def)
        sorry

    next
      case (fail S i ls)
      then show ?case using invs by (auto simp add: )
    next
      case (invCheck S res i)
      then show ?case using invs by (auto simp add: )
    qed
  qed
qed



end