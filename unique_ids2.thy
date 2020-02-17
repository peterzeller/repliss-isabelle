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
"new_unique_not_in_other_invocations i S uidv \<equiv>
(\<forall>i'. i' \<noteq> i \<longrightarrow> (\<exists>uids. uidv \<notin> uids \<and> invocation_cannot_guess_ids uids i' S))"


lemmas use_new_unique_not_in_other_invocations = new_unique_not_in_other_invocations_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

(*
lemma show_new_unique_not_in_other_invocations:
  assumes a1: "new_unique_not_in_other_invocations i S uidv"
    and a2: "\<And>i' uids ls ls' impl. \<lbrakk>i' \<noteq> i; los i' \<triangleq> ls; los' i' \<triangleq> ls'; p i' \<triangleq> impl;  invocations_cannot_guess_ids uids ls impl\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
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
*)

definition uid_is_private where
"uid_is_private i S uidv  \<equiv> 
      new_unique_not_in_invocationOp (invocationOp S) uidv
    \<and> new_unique_not_in_calls (calls S) uidv
    \<and> new_unique_not_in_calls_result (calls S) uidv
    \<and> new_unique_not_in_invocationRes (invocationRes S) uidv
    \<and> uidv \<notin> (knownIds S)
    \<and> generatedIds S uidv \<triangleq> i
    \<and> new_unique_not_in_other_invocations i S uidv"


definition uid_is_private' where
"uid_is_private' i s_calls s_invocationOp s_invocationRes s_knownIds uidv  \<equiv> 
      new_unique_not_in_invocationOp s_invocationOp uidv
    \<and> new_unique_not_in_calls s_calls uidv
    \<and> new_unique_not_in_calls_result s_calls uidv
    \<and> new_unique_not_in_invocationRes s_invocationRes uidv
    \<and> uidv \<notin> s_knownIds
    "
lemma uid_is_private'_implies:
"uid_is_private i S uidv
 \<Longrightarrow> uid_is_private' i (calls S) (invocationOp S) (invocationRes S) (knownIds S) uidv"
  by (auto simp add: uid_is_private_def uid_is_private'_def)


lemma growth_still_hidden_step_other:
  assumes S_wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and p1: "uid_is_private i S uidv"
    and step: "S ~~ (i', a) \<leadsto> S'"
    and other: "i' \<noteq> i"
  shows "uid_is_private i S' uidv"
proof -


  have priv_S: "uid_is_private i S uidv"
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
  have i6: "new_unique_not_in_other_invocations i S uidv"
    by (meson priv_S uid_is_private_def)

  have still_generated: "generatedIds S uidv \<triangleq> i"
    by (meson priv_S uid_is_private_def)


  have inv6': "new_unique_not_in_other_invocations i S' uidv"
    if "uidv \<notin> action_inputs a"
    unfolding new_unique_not_in_other_invocations_def 
  proof (intro allI impI)
    fix i''
    assume a0: "i'' \<noteq> i"

    obtain uids where "uidv \<notin> uids" and "invocation_cannot_guess_ids uids i'' S"
      by (metis a0 i6 new_unique_not_in_other_invocations_def)


    show "\<exists>uids. uidv \<notin> uids \<and> invocation_cannot_guess_ids uids i'' S'"
    proof (cases "i'' = i'")
      case True

      from `invocation_cannot_guess_ids uids i'' S`
      have "invocation_cannot_guess_ids (uids \<union> action_inputs a) i'' S'"
      proof (rule show_invocation_cannot_guess_ids_step)
        show "S ~~ (i'', a) \<leadsto> S'"
          by (simp add: True local.step)
      qed

      then show ?thesis
        using UnE \<open>uidv \<notin> uids\<close> that by auto
    next
      case False

      from `invocation_cannot_guess_ids uids i'' S` step
      have "invocation_cannot_guess_ids uids i'' S'"
        by (rule show_invocation_cannot_guess_ids_step_other, use False in simp)

      then show ?thesis
        using \<open>uidv \<notin> uids\<close> by blast
    qed
  qed


  note invs = i1 i2 i3 i4 i5 i6 inv6' still_generated





  have S'_wf: "state_wellFormed S'" if noFail: "a \<noteq> ACrash"
    using S_wf local.step noFail state_wellFormed_combine1 by blast


  


  from `S ~~ (i', a) \<leadsto> S'`
  show ?thesis
  proof (induct rule: step.cases)
    case (local S i2 ls f ls')


    from local
    show ?case
      using invs by (auto simp add: uid_is_private_def  split: if_splits)

  next
    case (newId S i' ls f ls' uid uidv ls'')
    show ?case 
      using invs  `uid = to_nat uidv` `generatedIds S uid = None` newId by (auto simp add: uid_is_private_def)

  next
    case (beginAtomic S i ls f ls' t vis snapshot)
    then show ?case using invs by (auto simp add: uid_is_private_def  split: if_splits)
  next
    case (endAtomic S i ls f ls' t)
    then show ?case using invs 
      by (auto simp add: uid_is_private_def   split: if_splits)

  next
    case (dbop S i' ls f Op ls' t c res vis)

    have "i' \<noteq> i"
      using dbop.hyps(2) other by blast


    obtain uids where  uids1: " uidv \<notin> uids" and uids2: "invocation_cannot_guess_ids uids i' S"
      by (metis \<open>i' \<noteq> i\<close> dbop.hyps(1) i6 new_unique_not_in_other_invocations_def)


    from uids2 step
    have "uniqueIds Op \<subseteq> uids" 
      by (fuzzy_rule use_invocation_cannot_guess_ids_dbop, use dbop in auto)




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
      unfolding uid_is_private_def
    proof (intro conjI)
      show "new_unique_not_in_invocationOp (invocationOp S') uidv"
        using dbop.hyps(1) i1 by (auto simp add: dbop)
      show "new_unique_not_in_calls (calls S') uidv"
        using dbop.hyps(1) i2 by (auto simp add: dbop new_unique_not_in_calls_def uids2)
      show "new_unique_not_in_calls_result (calls S') uidv"
        using dbop.hyps(1) i3 by (auto simp add: dbop new_unique_not_in_calls_result_def uids3)
      show "new_unique_not_in_invocationRes (invocationRes S') uidv"
       using dbop.hyps(1) i4 by (auto simp add: dbop)
      show "uidv \<notin> knownIds S'"
        using dbop.hyps(1) i5  by (auto simp add: dbop)
      show "generatedIds S' uidv \<triangleq> i"
        using dbop.hyps(1) still_generated by (auto simp add: dbop)
      show "new_unique_not_in_other_invocations i S' uidv "
        using dbop.hyps(2) inv6' uids3 by auto
    qed

  next
    case (invocation S i proc initialState impl)
    then show ?case using invs by (auto simp add: uid_is_private_def new_unique_not_in_invocationOp_def)

  next
    case (return S i ls f res)
    then show ?case using invs apply (auto simp add: uid_is_private_def)
       apply (auto simp add: new_unique_not_in_invocationRes_def)
      apply (metis action_outputs.simps(7) i6 invocation_cannot_guess_ids_step local.step new_unique_not_in_other_invocations_def other )
      by (metis action_outputs.simps(7) i6 invocation_cannot_guess_ids_step local.step new_unique_not_in_other_invocations_def other)

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
    and p1: "uid_is_private i S uidv"
    and steps: "S ~~ tr \<leadsto>* S'"
    and other: "\<forall>(i',a)\<in>set tr. i' \<noteq> i"
    and no_fail: "\<forall>i. (i, ACrash) \<notin> set tr"
  shows "uid_is_private i S' uidv"
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
    show "uid_is_private i S' uidv"
      using step by auto
  qed
qed



lemma growth_still_hidden:
  assumes g: "state_monotonicGrowth i S S'"
    and prog_wf: "program_wellFormed (prog S)"
    and p1: "uid_is_private i S uidv"
  shows "uid_is_private i S' uidv"
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

lemma step_to_steps:
  assumes "S ~~ a \<leadsto> S'"
  shows " S ~~ [a] \<leadsto>* S'"
  by (simp add: assms steps_single)


lemma step_to_steps_ex:
  assumes "S ~~ a \<leadsto> S'"
  shows "\<exists>tr. S ~~ tr \<leadsto>* S'"
  by (rule exI[where x="[a]"], simp add: assms steps_single)

lemma step_s_to_step:
  assumes steps_s: "S ~~ (i, a, ok) \<leadsto>\<^sub>S S'"
    and no_AInvoc: "\<And>p. a \<noteq> AInvoc p"
    and no_beginAtomic: "\<And>t txns. a \<noteq> ABeginAtomic t txns"
  shows steps: " S ~~ (i, a) \<leadsto> S'"
  using steps_s proof cases
  case (local ls f ls')
  thus "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step.simps)
next
  case (newId ls f ls' uid uidv ls'')
  thus "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step.simps)
next
  case (beginAtomic ls f ls' t S'a vis vis')
  thus ?thesis using no_beginAtomic by auto
next
  case (endAtomic ls f ls' t)
  thus "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step.simps)
next
  case (dbop ls f Op ls' t c res vis)
  thus "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step.simps)
next
  case (invocation proc initState impl S')
  with no_AInvoc have False by auto
  thus ?thesis
    ..
next
  case (return ls f res)
  thus "S ~~ (i, a) \<leadsto> S'"
    by (auto simp add: step.simps)
qed

lemma step_s_beginAtomic_to_steps:
  assumes step_s: "S ~~ (i, ABeginAtomic t txns, ok) \<leadsto>\<^sub>S S'"
  shows "\<exists>Sx tr. (S ~~ tr \<leadsto>* Sx) \<and> (\<forall>(i',a)\<in>set tr.  i' \<noteq> i) \<and> (\<forall>i. (i, ACrash) \<notin> set tr)  \<and>  Sx ~~ (i, ABeginAtomic t txns) \<leadsto> S'"
  using assms proof cases
  case (beginAtomic ls f ls' S'a vis)

  from `state_monotonicGrowth i S S'a`
  obtain tr where x1: "S ~~ tr \<leadsto>* S'a"
    and x2: "\<forall>(i',a)\<in>set tr.  i' \<noteq> i"
    and x3: "\<forall>i. (i, ACrash) \<notin> set tr"
    by (auto simp add: state_monotonicGrowth_def)

  have "S'a ~~ (i, ABeginAtomic t txns) \<leadsto> S'"
    using beginAtomic by (auto simp add: step.simps)



  with x1 x2 x3
  show ?thesis 
    using steps_step by blast
qed

lemma  show_invocation_cannot_guess_ids_steps_other: 
  assumes icgi: "invocation_cannot_guess_ids uids i S" 
    and steps: "S ~~ tr \<leadsto>* S'"
    and other: "\<forall>(i',a)\<in>set tr. i' \<noteq> i"
  shows "invocation_cannot_guess_ids uids i S'" 
  using steps icgi other 
proof (induct rule: steps_induct)
case initial
  then show ?case
    by simp
next
  case (step S' tr a S'')
  then show ?case
    using show_invocation_cannot_guess_ids_step_other
    by (smt Un_iff case_prodE insert_iff list.set(1) list.set(2) prod.sel(1) set_append )
qed


lemma  show_invocation_cannot_guess_ids_step_s_other: 
  assumes "invocation_cannot_guess_ids uids i S" 
    and step: "S ~~ (i', a) \<leadsto>\<^sub>S S'"
    and "i' \<noteq> i"
    and no_beginAtomic: "\<And>t txns. fst a \<noteq> ABeginAtomic t txns"
    and no_AInvoc: "\<And>p. fst a \<noteq> AInvoc p"
  shows "invocation_cannot_guess_ids uids i S'" 
proof -
  have "S ~~ (i', fst a) \<leadsto> S'"
  proof (rule step_s_to_step)
    show "S ~~ (i', fst a, snd a) \<leadsto>\<^sub>S S'"
      using step by simp
  qed (simp add: no_AInvoc no_beginAtomic)+

  with `invocation_cannot_guess_ids uids i S`
  show "invocation_cannot_guess_ids uids i S'"
    using `i' \<noteq> i` show_invocation_cannot_guess_ids_step_other by blast
qed


lemma invocation_cannot_guess_ids_steps:
  assumes "invocation_cannot_guess_ids uids i S"
    and "S ~~ tr \<leadsto>* S'"
  shows "invocation_cannot_guess_ids (uids \<union> trace_inputs tr i) i S'"
proof (rule show_invocation_cannot_guess_ids)
  fix x tra a S'a
  assume a0: "S' ~~ tra @ [(i, a)] \<leadsto>* S'a"
    and a1: "x \<in> action_outputs a"
    and a2: "x \<notin> uids \<union> trace_inputs tr i"

  have "S ~~ ((tr@tra) @ [(i,a)]) \<leadsto>* S'a"
    using a0 assms(2) steps_append2 by force


  from use_invocation_cannot_guess_ids[OF  `invocation_cannot_guess_ids uids i S` `S ~~ ((tr@tra) @ [(i,a)]) \<leadsto>* S'a`]
  have "trace_outputs ((tr @ tra) @ [(i, a)]) i \<subseteq> trace_inputs (tr @ tra) i \<union> uids" .
  hence "action_outputs a \<subseteq> trace_inputs (tr @ tra) i \<union> uids"
    by (auto simp add: trace_outputs_def)

  with `x \<in> action_outputs a` `x \<notin> uids \<union> trace_inputs tr i`
  show "x \<in> trace_inputs tra i"
    by (auto simp add: trace_inputs_append)
qed

lemma new_unique_not_in_other_invocations_maintained:
  assumes "new_unique_not_in_other_invocations i S x"
    and "S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'"
    and no_AInvoc: "\<And>p. action \<noteq> AInvoc p"
    and no_beginAtomic: "\<And>t txns. action \<noteq> ABeginAtomic t txns"
  shows "new_unique_not_in_other_invocations i S' x"
  unfolding new_unique_not_in_other_invocations_def
proof (intro allI impI)
  fix i'
  assume a0: "i' \<noteq> i"

  obtain uids where "x \<notin> uids" and "invocation_cannot_guess_ids uids i' S"
    by (meson a0 assms(1) new_unique_not_in_other_invocations_def)


  from `S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'`
  have "S ~~ (i, action) \<leadsto> S'"
    by (simp add: no_AInvoc no_beginAtomic step_s_to_step)


  have "invocation_cannot_guess_ids uids i' S'"

    using \<open>S ~~ (i, action) \<leadsto> S'\<close> \<open>invocation_cannot_guess_ids uids i' S\<close> a0 show_invocation_cannot_guess_ids_step_other by blast


  thus "\<exists>uids. x \<notin> uids \<and> invocation_cannot_guess_ids uids i' S'"
    using \<open>x \<notin> uids\<close> by blast
qed

end