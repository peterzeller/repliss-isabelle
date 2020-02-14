section "Unique Identifiers (Part 2)"
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
    unique_ids_procedure_check
begin



definition 
  "new_unique_not_in_invocationOp iop uidv \<equiv>
\<forall>i op. iop i \<triangleq> op \<longrightarrow> uidv \<notin> uniqueIds op "


definition 
  "new_unique_not_in_calls iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> uidv \<notin> uniqueIds op "

definition 
  "new_unique_not_in_calls_result iop uidv \<equiv>
\<forall>i op r. iop i \<triangleq> Call op r \<longrightarrow> uidv \<notin> uniqueIds r "

definition
"new_unique_not_in_invocationRes ires uidv \<equiv> 
\<forall>i r. ires i \<triangleq> r \<longrightarrow> uidv \<notin> uniqueIds r "

definition
"new_unique_not_in_other_invocations i los p uidv \<equiv>
(\<forall>i' ls impl. i' \<noteq> i \<longrightarrow> los i' \<triangleq> ls \<longrightarrow> p i' \<triangleq> impl \<longrightarrow> (\<exists>uids. uidv \<notin> uids \<and> procedure_cannot_guess_ids uids ls impl))"


lemma show_new_unique_not_in_other_invocations:
  assumes a1: "new_unique_not_in_other_invocations i los p uidv"
    and a2: "\<And>i' uids ls ls' impl. \<lbrakk>i' \<noteq> i; los i' \<triangleq> ls; los' i' \<triangleq> ls'; p i' \<triangleq> impl;  procedure_cannot_guess_ids uids ls impl\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
    and a3: "dom los = dom los'"
  shows "new_unique_not_in_other_invocations i los' p uidv"
proof (auto simp add: new_unique_not_in_other_invocations_def)
  fix i' ls impl
  assume b1: "i' \<noteq> i"
    and b2: "los' i' \<triangleq> ls"
    and b3: "p i' \<triangleq> impl"

  obtain ls_pre where b4: "los i' \<triangleq> ls_pre"
    using a3 b2 by force


  from a1 obtain uids where b5: " uidv \<notin> uids" and b6: "procedure_cannot_guess_ids uids ls_pre impl"
    by (meson b1 b3 b4 new_unique_not_in_other_invocations_def)

  have "procedure_cannot_guess_ids uids ls impl"
    using b1 b4 b2 b3 b6 by (rule a2)

  show "\<exists>uids.  uidv \<notin> uids \<and> procedure_cannot_guess_ids uids ls impl"
    using \<open>procedure_cannot_guess_ids uids ls impl\<close> b5 by auto
qed

definition uid_is_private where
"uid_is_private i s_calls s_invocationOp s_invocationRes s_knownIds s_generatedIds s_localState s_currentProc uidv  \<equiv> 
      new_unique_not_in_invocationOp s_invocationOp uidv
    \<and> new_unique_not_in_calls s_calls uidv
    \<and> new_unique_not_in_calls_result s_calls uidv
    \<and> new_unique_not_in_invocationRes s_invocationRes uidv
    \<and> uidv \<notin> s_knownIds
    \<and> s_generatedIds uidv \<triangleq> i
    \<and> new_unique_not_in_other_invocations i s_localState s_currentProc uidv"


definition uid_is_private' where
"uid_is_private' i s_calls s_invocationOp s_invocationRes s_knownIds uidv  \<equiv> 
      new_unique_not_in_invocationOp s_invocationOp uidv
    \<and> new_unique_not_in_calls s_calls uidv
    \<and> new_unique_not_in_calls_result s_calls uidv
    \<and> new_unique_not_in_invocationRes s_invocationRes uidv
    \<and> uidv \<notin> s_knownIds
    "
lemma uid_is_private'_implies:
"uid_is_private i s_calls s_invocationOp s_invocationRes s_knownIds s_generatedIds s_localState s_currentProc uidv
 \<Longrightarrow> uid_is_private' i s_calls s_invocationOp s_invocationRes s_knownIds uidv"
  by (auto simp add: uid_is_private_def uid_is_private'_def)


lemma growth_still_hidden_step_other:
  assumes S_wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and p1: "uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S) (currentProc S) uidv"
    and step: "S ~~ (i', a) \<leadsto> S'"
    and other: "i' \<noteq> i"
  shows "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S') (localState S') (currentProc S') uidv"
proof -


  have priv_S: "uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S)
         (currentProc S) uidv"
    by (simp add: p1)


  have i1: "new_unique_not_in_invocationOp (invocationOp S) uidv "
    by (meson priv_S uid_is_private_def)


  have i2: "new_unique_not_in_calls (calls S) uidv "
    by (meson priv_S uid_is_private_def)
  have i3: "new_unique_not_in_calls_result (calls S) uidv"
    by (meson priv_S uid_is_private_def)
  have i4: "new_unique_not_in_invocationRes (invocationRes S) uidv"
    by (meson priv_S uid_is_private_def)
  have i5: "uidv \<notin> knownIds S"
    by (meson priv_S uid_is_private_def)
  have i6: "new_unique_not_in_other_invocations i (localState S) (currentProc S) uidv"
    by (meson priv_S uid_is_private_def)

  have still_generated: "generatedIds S uidv \<triangleq> i"
    by (meson priv_S uid_is_private_def)


  note invs = i1 i2 i3 i4 i5 i6 still_generated



  have i6': "\<And>ls impl. localState S i' \<triangleq> ls \<Longrightarrow> currentProc S i' \<triangleq> impl \<Longrightarrow> (\<exists>uids.  uidv \<notin> uids \<and> procedure_cannot_guess_ids uids ls impl)"
    using \<open>i' \<noteq> i\<close> i6
    by (meson new_unique_not_in_other_invocations_def) 



  have S'_wf: "state_wellFormed S'" if noFail: "a \<noteq> ACrash"
    using S_wf local.step noFail state_wellFormed_combine1 by blast




  from `S ~~ (i', a) \<leadsto> S'`
  show ?thesis
  proof (induct rule: step.cases)
    case (local S i2 ls f ls')

    obtain uids where  uids1: " uidv \<notin> uids" and uids2: "procedure_cannot_guess_ids uids ls f"
      using \<open>i' \<noteq> i\<close> i6 local i6' by auto 

    from local
    show ?case
      using invs  apply (auto simp add: uid_is_private_def elim!: show_new_unique_not_in_other_invocations split: if_splits)
      by (meson pcgi_local_case uids1 uids2)



  next
    case (newId S i' ls f ls' uid uidv ls'')
    show ?case 
      using invs  apply (auto simp add: uid_is_private_def newId)
      using `uid = to_nat uidv` `generatedIds S uid = None` apply auto[1]
      using `uid = to_nat uidv` `generatedIds S uid = None`  apply (auto simp add: new_unique_not_in_other_invocations_def)
      by (metis (no_types, lifting) Un_insert_right insert_iff newId.hyps(4) newId.hyps(5) newId.hyps(6) newId.hyps(8) newId.hyps(9) option.inject pcgi_newId_case sup_bot.comm_neutral)


  next
    case (beginAtomic S i ls f ls' t vis snapshot)
    then show ?case using invs by (auto simp add: uid_is_private_def pcgi_beginAtomic_case elim!: show_new_unique_not_in_other_invocations split: if_splits)
  next
    case (endAtomic S i ls f ls' t)
    then show ?case using invs 
      by (auto simp add: uid_is_private_def pcgi_endAtomic_case elim!: show_new_unique_not_in_other_invocations split: if_splits)




  next
    case (dbop S i' ls f Op ls' t c res vis)

    obtain uids where  uids1: " uidv \<notin> uids" and uids2: "procedure_cannot_guess_ids uids ls f"
      using dbop.hyps(1) dbop.hyps(2) dbop.hyps(4) dbop.hyps(5) i6' by blast 



    from pcgi_dbop_case1[OF uids2 `f ls = DbOperation Op ls'`]
    have "uniqueIds Op \<subseteq> uids" .

    with uids1 have uids2: " uidv \<notin> uniqueIds Op"
      by auto

    have qcngi: "queries_cannot_guess_ids (querySpec (prog S))"
      using dbop.hyps(1) prog_wf program_wellFormed_def by blast



    have uids3: " uidv \<notin> uniqueIds res"
    proof (rule notI)
      assume " uidv \<in> uniqueIds res "

      from qcngi `querySpec (prog S) Op (getContext S i') res` ` uidv \<in> uniqueIds res` ` uidv \<notin> uniqueIds Op`
      have "\<exists>cId opr res. calls (getContext S i') cId \<triangleq> Call opr res \<and>  uidv \<in> uniqueIds opr"
        by (rule queries_cannot_guess_ids_def2[THEN iffD1, rule_format])

      thus False
        apply (auto simp add: getContextH_def restrict_map_def split: option.splits if_splits)
        using dbop.hyps(1) i2 new_unique_not_in_calls_def by fastforce
    qed




    show ?case 
    proof (auto simp add: uid_is_private_def dbop invs uids2 uids3 )
      show "new_unique_not_in_invocationOp (invocationOp S) uidv"
        using dbop.hyps(1) i1 by blast


      show "new_unique_not_in_calls (calls S(c \<mapsto> Call Op res)) uidv"
        using uids2 i2 by (auto simp add: new_unique_not_in_calls_def dbop )

      show " new_unique_not_in_calls_result (calls S(c \<mapsto> Call Op res)) uidv"
        using uids2 i3 by (auto simp add: new_unique_not_in_calls_result_def dbop uids3)


      show "new_unique_not_in_invocationRes (invocationRes S) uidv"
        using dbop.hyps(1) i4 by blast

      show " uidv \<in> knownIds S \<Longrightarrow> False"
        using dbop.hyps(1) i5 by blast

      show "new_unique_not_in_other_invocations i (localState S(i' \<mapsto> ls' res)) (currentProc S) uidv"
        by (smt UnE \<open>\<And>thesis. (\<And>uids. \<lbrakk>uidv \<notin> uids; procedure_cannot_guess_ids uids ls f\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> dbop.hyps(1) dbop.hyps(5) dbop.hyps(6) fun_upd_other fun_upd_same i6 new_unique_not_in_other_invocations_def option.sel pcgi_dbop_case2 uids3)


      show "generatedIds S uidv \<triangleq> i"
        using dbop.hyps(1) still_generated by blast

    qed





  next
    case (invocation S i proc initialState impl)
    then show ?case using invs apply (auto simp add: uid_is_private_def)
       apply (auto simp add: new_unique_not_in_invocationOp_def)
      apply (auto simp add: new_unique_not_in_other_invocations_def)
      by (metis prog_wf program_wellFormed_def show_procedures_cannot_guess_ids subsetD subset_Un_eq subset_refl)

  next
    case (return S i ls f res)
    then show ?case using invs apply (auto simp add: uid_is_private_def)
        apply (auto simp add: new_unique_not_in_invocationRes_def)
      using i6' pcgi_return_case apply fastforce
      using i6' pcgi_return_case apply fastforce
      by (simp add: new_unique_not_in_other_invocations_def)

  next
    case (fail S i ls)
    then show ?case 
      using invs
      by (auto simp add: uid_is_private_def new_unique_not_in_other_invocations_def)


  next
    case (invCheck S res i)
    then show ?case using invs by (auto simp add: uid_is_private_def)
  qed
qed


lemma growth_still_hidden_steps_other:
  assumes S_wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and p1: "uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S) (currentProc S) uidv"
    and steps: "S ~~ tr \<leadsto>* S'"
    and other: "\<forall>(i',a)\<in>set tr. i' \<noteq> i"
    and no_fail: "\<forall>i. (i, ACrash) \<notin> set tr"
  shows "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S') (localState S') (currentProc S') uidv"
using steps   p1 other no_fail proof (induct rule: steps_induct)
  case initial
  then show ?case by simp
next
  case (step S' tr a S'')
  
  show ?case 
    using  `S' ~~ a \<leadsto> S''`
  proof (fuzzy_rule growth_still_hidden_step_other)
    show "state_wellFormed S'"
      using S_wf state_wellFormed_combine step.prems step.steps by fastforce

    show "a = (get_invoc a, get_action a)" by force
    show "get_invoc a \<noteq> i"
      using local.step by auto
    show "program_wellFormed (prog S')"
      using prog_wf step.steps steps_do_not_change_prog by fastforce
    show "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S') (localState S')
     (currentProc S') uidv"
      using step by auto
  qed
qed



lemma growth_still_hidden:
  assumes g: "state_monotonicGrowth i S S'"
    and prog_wf: "program_wellFormed (prog S)"
    and p1: "uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S) (currentProc S) uidv"
  shows "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S') (localState S') (currentProc S') uidv"
proof -
  from g obtain tr
    where wf: "state_wellFormed S"
      and steps: "S ~~ tr \<leadsto>* S'"
      and no_i: "\<forall>x\<in>set tr. case x of (i', a) \<Rightarrow> i' \<noteq> i"
      and no_fail: "\<forall>i. (i, ACrash) \<notin> set tr"
    by (auto simp add: state_monotonicGrowth_def)


  from steps no_i wf no_fail prog_wf p1
  show ?thesis
    using growth_still_hidden_steps_other by blast
qed



end