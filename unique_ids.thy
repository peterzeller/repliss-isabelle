section "Unique Identifiers"
theory unique_ids
  imports execution_invariants
    "fuzzyrule.fuzzyrule"
begin


text \<open>In this section we prove some general properties about unique identifiers.

In general, we assume that procedure implementations are well behaved and cannot produce unique
identifiers out of thin air (i.e. ``guess'' them).
We define this property inductively:
\<close>

fun action_inputs where
  "action_inputs (ALocal ls) = {}"
| "action_inputs (ANewId i) = uniqueIds i"
| "action_inputs (ABeginAtomic t c) =  {}"
| "action_inputs AEndAtomic = {}"
| "action_inputs (ADbOp c opr res) = uniqueIds res"
| "action_inputs (AInvoc proc) = uniqueIds proc"
| "action_inputs (AReturn r) = {}"
| "action_inputs ACrash   = {}"
| "action_inputs (AInvcheck b) = {}"

lemma action_inputs_cases:
 "x \<in> action_inputs a \<longleftrightarrow> 
(case a of 
    ANewId i \<Rightarrow> x \<in> uniqueIds i 
  | ADbOp c opr res \<Rightarrow> x \<in> uniqueIds res
  | AInvoc proc \<Rightarrow> x \<in> uniqueIds proc
  | _ \<Rightarrow> False)"
  by (auto split: action.splits)

fun action_outputs where
  "action_outputs (ALocal ls) = {}"
| "action_outputs (ANewId i) = {}"
| "action_outputs (ABeginAtomic t c) =  {}"
| "action_outputs AEndAtomic = {}"
| "action_outputs (ADbOp c opr res) = uniqueIds opr"
| "action_outputs (AInvoc proc) = {}"
| "action_outputs (AReturn r) = uniqueIds r"
| "action_outputs ACrash   = {}"
| "action_outputs (AInvcheck b) = {}"

definition trace_inputs :: "('proc::valueType, 'operation, 'any::valueType) trace \<Rightarrow> invocId \<Rightarrow> uniqueId set" where
"trace_inputs trace i \<equiv> \<Union>((action_inputs \<circ> snd) ` (Set.filter (\<lambda>a. fst a = i) (set trace)))"

definition trace_outputs :: "('proc, 'operation::valueType, 'any::valueType) trace \<Rightarrow>  invocId \<Rightarrow> uniqueId set" where
"trace_outputs trace i \<equiv> \<Union>((action_outputs \<circ> snd) ` (Set.filter (\<lambda>a. fst a = i) (set trace)))"


lemma trace_inputs_empty: "trace_inputs [] i = {}"
  by (simp add: trace_inputs_def)

lemma trace_outputs_empty: "trace_outputs [] i = {}"
  by (simp add: trace_outputs_def)

lemma trace_inputs_append: "trace_inputs (a@b) i = trace_inputs a i \<union> trace_inputs b i"
  by (auto simp add: trace_inputs_def Set.filter_def)


lemma trace_outputs_append: "trace_outputs (a@b) i = trace_outputs a i \<union> trace_outputs b i"
  by (auto simp add: trace_outputs_def Set.filter_def)


lemma trace_inputs_cons: "trace_inputs (a#b) i = (if get_invoc a = i then action_inputs (get_action a) else {}) \<union> trace_inputs b i"
  by (auto simp add: trace_inputs_def Set.filter_def)


lemma trace_outputs_cons: "trace_outputs (a#b) i = (if get_invoc a = i then action_outputs (get_action a) else {}) \<union> trace_outputs b i"
  by (auto simp add: trace_outputs_def Set.filter_def)

\<comment> \<open>uids are the ids that are already known in invocation i.
The property states that no further unique ids may be produced in the output
of invocation i without obtaining them as input first.\<close>
definition 
"invocation_cannot_guess_ids uids i S \<equiv>
 \<forall>tr a S'. (S ~~ tr@[a] \<leadsto>* S')
  \<longrightarrow> trace_outputs (tr@[a]) i \<subseteq> trace_inputs tr i \<union> uids"

definition 
"invocations_cannot_guess_ids progr \<equiv>
  \<forall>i. invocation_cannot_guess_ids {} i (initialState progr)"

lemmas use_invocation_cannot_guess_ids = invocation_cannot_guess_ids_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

lemma show_invocation_cannot_guess_ids:
  assumes a: "\<And>x tr a S'. S ~~ tr@[(i, a)] \<leadsto>* S'
      \<Longrightarrow> x \<in> action_outputs a
      \<Longrightarrow> x \<notin> uids
      \<Longrightarrow> x \<in> trace_inputs tr i"
  shows "invocation_cannot_guess_ids uids i S"
  unfolding invocation_cannot_guess_ids_def
proof auto
  fix tr i' action x S''
  assume a0: "x \<in> trace_outputs (tr @ [(i', action)]) i"
    and a1: "x \<notin> uids"
    and steps: "S ~~ tr @ [(i', action)] \<leadsto>* S''"

  

  show "x \<in> trace_inputs tr i"
    using a0
  proof (auto simp add: trace_outputs_def split: if_splits)

    show "x \<in> trace_inputs tr i"
      if c0: "i' = i"
        and c1: "x \<in> action_outputs action"
      using steps
    proof (fuzzy_rule a)
      show "i'=i" using `i' = i` .
      show "x \<in> action_outputs action" 
        using `x \<in> action_outputs action` by simp
      show "x \<notin> uids" using a1 by simp
    qed

    fix action
    assume  "x \<in> action_outputs action"
      and  "(i, action) \<in> set tr"

    from `(i, action) \<in> set tr`
    obtain k where "k < length tr" and "tr!k = (i,action)"
      by (meson in_set_conv_nth)

    obtain S1
      where "S ~~ take (Suc k) tr \<leadsto>* S1"
      by (metis split_take steps steps_append)



    have "x \<in> trace_inputs (take k tr) i"
    proof (rule a)
      show "S ~~ take k tr @ [(i,action)] \<leadsto>* S1"
        using \<open>S ~~ take (Suc k) tr \<leadsto>* S1\<close> \<open>k < length tr\<close> \<open>tr ! k = (i, action)\<close> take_Suc_conv_app_nth by fastforce

      show "x \<in> action_outputs action"
        by (simp add: \<open>x \<in> action_outputs action\<close>)

      show "x \<notin> uids"
        by (simp add: a1)
    qed

    thus "x \<in> trace_inputs tr i"
      by (auto simp add: trace_inputs_def Set.filter_def dest: in_set_takeD)
    thus "x \<in> trace_inputs tr i" .
  qed
qed



lemma invocation_cannot_guess_ids_step:
  assumes "invocation_cannot_guess_ids uids i S" 
    and step: "S ~~ (i, a) \<leadsto> S'"
    and "x \<in> action_outputs a"
  shows "x \<in> uids"
proof -
  from step have steps: "S ~~ []@[(i, a)] \<leadsto>* S'"
    by (simp add: steps_single)
  from use_invocation_cannot_guess_ids[OF `invocation_cannot_guess_ids uids i S` steps]
  have "trace_outputs [(i, a)] i \<subseteq> uids"
    by (auto simp add: trace_inputs_def)
  hence "action_outputs a \<subseteq>  uids"
    by (auto simp add: trace_outputs_def trace_inputs_def)
  with `x \<in> action_outputs a`
  show  ?thesis
    by auto
qed

lemma  show_invocation_cannot_guess_ids_step: 
 assumes "invocation_cannot_guess_ids uids i S" 
    and step: "S ~~ (i, a) \<leadsto> S'"
  shows "invocation_cannot_guess_ids (uids \<union> action_inputs a) i S'" 
  unfolding invocation_cannot_guess_ids_def 
proof (intro allI impI)
  fix tr aa S'a
  assume a0: "S' ~~ tr @ [aa] \<leadsto>* S'a"

  with step
  have S_steps: "S ~~ ((i,a)#tr) @ [aa] \<leadsto>* S'a"
    using steps_appendFront by fastforce

  from use_invocation_cannot_guess_ids[OF `invocation_cannot_guess_ids uids i S` S_steps]
  show "trace_outputs (tr @ [aa]) i \<subseteq> trace_inputs tr i \<union> (uids \<union> action_inputs a)"
    by (auto simp add: trace_outputs_def trace_inputs_def)
qed

lemma  show_invocation_cannot_guess_ids_step_other: 
  assumes "invocation_cannot_guess_ids uids i S" 
    and step: "S ~~ (i', a) \<leadsto> S'"
    and "i' \<noteq> i"
  shows "invocation_cannot_guess_ids uids i S'" 
  unfolding invocation_cannot_guess_ids_def 
proof (intro allI impI)
  fix tr aa S'a
  assume a0: "S' ~~ tr @ [aa] \<leadsto>* S'a"

  with step
  have S_steps: "S ~~ ((i',a)#tr) @ [aa] \<leadsto>* S'a"
    using steps_appendFront by fastforce

  from use_invocation_cannot_guess_ids[OF `invocation_cannot_guess_ids uids i S` S_steps]
  show "trace_outputs (tr @ [aa]) i \<subseteq> trace_inputs tr i \<union> uids"
    using `i' \<noteq> i`
    by (auto simp add: trace_outputs_def trace_inputs_def)
qed


(* TODO transfer this to local states, procedures, programs  *)
(* TODO show procedure_cannot_guess_ids implies the semantic property *)
(* TODO show that syntactic property for toImpl with loops implies semantic property *)
   

definition query_cannot_guess_ids :: "uniqueId set \<Rightarrow> (('operation::valueType, 'any::valueType) operationContext \<Rightarrow> 'any \<Rightarrow> bool) \<Rightarrow> bool"  where
  "query_cannot_guess_ids oprUids spec \<equiv> 
  \<forall>ctxt res. 
   spec ctxt res \<longrightarrow> uniqueIds res \<subseteq> oprUids \<union> \<Union>{uniqueIds (call_operation c) | cId c. calls ctxt cId \<triangleq> c}"

lemma exists_call_expand:
"(\<exists>c. P c) \<longleftrightarrow> (\<exists>op r. P (Call op r))"
  by (auto, metis call.collapse)

lemma query_cannot_guess_ids_def2:
  "query_cannot_guess_ids oprUids spec =
  (\<forall>ctxt res x. 
   spec ctxt res 
 \<longrightarrow> x \<in> uniqueIds res 
 \<longrightarrow> x \<notin> oprUids
 \<longrightarrow> (\<exists>cId opr res. calls ctxt cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr))"
  by (auto simp add: query_cannot_guess_ids_def subset_iff exists_call_expand, blast+)

definition queries_cannot_guess_ids :: "('operation \<Rightarrow> ('operation::valueType, 'any::valueType) operationContext \<Rightarrow> 'any \<Rightarrow> bool) \<Rightarrow> bool"  where
  "queries_cannot_guess_ids spec \<equiv> 
  \<forall>opr. query_cannot_guess_ids (uniqueIds opr) (spec opr)"


lemma queries_cannot_guess_ids_def2:
  "queries_cannot_guess_ids qry =
  (\<forall>opr ctxt res x. 
   qry opr ctxt res 
 \<longrightarrow> x \<in> uniqueIds res 
 \<longrightarrow> x \<notin> uniqueIds opr
 \<longrightarrow> (\<exists>cId opr res. calls ctxt cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr))"
  by (auto simp add: queries_cannot_guess_ids_def query_cannot_guess_ids_def2)


definition program_wellFormed :: " ('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) prog \<Rightarrow> bool" where
  "program_wellFormed progr \<equiv> 
   invocations_cannot_guess_ids progr
 \<and> queries_cannot_guess_ids (querySpec progr)
"

lemma exists_elim_h: "\<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> \<exists>x. P x \<and> Q x" for P Q x
  by auto



lemma wf_knownIds_subset_generatedIds_h:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
  shows "\<And>i. \<exists>uids\<subseteq>dom (generatedIds S). invocation_cannot_guess_ids uids i S"
    and "knownIds S \<subseteq> dom (generatedIds S)"
    and "\<And>c opr r. calls S c \<triangleq> Call opr r \<Longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S)"
    and "\<And>c opr r. calls S c \<triangleq> Call opr r \<Longrightarrow> uniqueIds r \<subseteq> dom (generatedIds S)"

  using wf prog_wf
proof -


  from wf prog_wf
  have H: "(\<forall>i. (\<exists>uids. uids \<subseteq> dom (generatedIds S) \<and> invocation_cannot_guess_ids uids i S))
       \<and> (knownIds S \<subseteq> dom (generatedIds S))
       \<and> (\<forall>c opr r. calls S c \<triangleq> Call opr r \<longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S) \<and> uniqueIds r \<subseteq> dom (generatedIds S))"
  proof (induct rule: wellFormed_induct)
    case initial
    then show ?case 
      by (auto simp add: invocations_cannot_guess_ids_def program_wellFormed_def initialState_def)
  next
    case (step S1 a S2)

    obtain progr where [simp]: "prog S1 = progr"
      by auto

    have [simp]: "prog S2 = progr"
      using \<open>prog S1 = progr\<close> prog_inv step.hyps(3) by blast

    have  prog_wf: "program_wellFormed progr"
      using \<open>prog S2 = progr\<close> step.prems by blast


    from prog_wf
    have "invocations_cannot_guess_ids progr"
      and "queries_cannot_guess_ids (querySpec progr)"
      using program_wellFormed_def by auto





    have inv1: "(\<exists>uids\<subseteq>dom (generatedIds S1). invocation_cannot_guess_ids uids i S1)" for i
      using \<open>prog S1 = progr\<close> step.hyps(2) step.prems  by auto


    



    have inv2: "knownIds S1 \<subseteq> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> prog_wf step.hyps(2) by blast


    have inv3: "uniqueIds opr \<subseteq> dom (generatedIds S1)" 
      if "calls S1 c \<triangleq> Call opr r"
      for c opr r
      using \<open>prog S1 = progr\<close> prog_wf step.hyps(2) that by blast

    have inv4r: "x \<in> dom (generatedIds S1)"
      if "calls S1 c \<triangleq> Call opr r"
        and "x \<in> uniqueIds r"
      for c opr r x
      using \<open>prog S1 = progr\<close> prog_wf step.hyps(2) that(1) that(2) by blast


    have inv4o: "x \<in> dom (generatedIds S1)"
      if "calls S1 c \<triangleq> Call opr r"
        and "x \<in> uniqueIds opr"
      for c opr r x
      using inv3 that(1) that(2) by blast



    obtain action i where a_def: "a = (i, action)"
      using surjective_pairing by blast

    obtain uids_i 
      where inv1_i1: "uids_i \<subseteq>  dom (generatedIds S1)"
        and inv1_i: "invocation_cannot_guess_ids uids_i i S1"
      using inv1 by auto

    from `S1 ~~ a \<leadsto> S2`[simplified a_def]
    have "S1 ~~ (i, action) \<leadsto> S2" .

    show "?case"
    proof (intro allI conjI impI)


      have i_in_out: "x \<in> uids_i"
        if "x \<in> action_outputs action" 
        for x
        using that invocation_cannot_guess_ids_step[OF `invocation_cannot_guess_ids uids_i i S1` `S1 ~~ (i, action) \<leadsto> S2`] 
        by auto


      show "knownIds S2 \<subseteq> dom (generatedIds S2)"
        using i_in_out `S1 ~~ (i, action) \<leadsto> S2` inv2 inv1_i1 
        by (auto simp add: step.simps, blast+)

      from queries_cannot_guess_ids_def2[THEN iffD1, rule_format, OF `queries_cannot_guess_ids (querySpec progr)`]
      have qry_wf: "\<exists>cId opr res. calls ctxt cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr"
        if c0: "querySpec progr opr ctxt res"
          and c2: "x \<notin> uniqueIds opr"
          and c1: "x \<in> uniqueIds res"
        for ctxt opr res x
        using that by auto



      have qryOk: "x \<notin> uniqueIds res"
        if q: "querySpec progr Op (getContextH (calls S1) (happensBefore S1) (Some vis)) res"
          and no: "x \<notin> uniqueIds Op"
          and noG: "x \<notin> dom (generatedIds S1)"
        for Op vis res x
      proof 
        assume " x \<in> uniqueIds res"
        from qry_wf[OF q no `x \<in> uniqueIds res`]
        obtain cId opr res where "cId \<in> vis" and  "x \<in> uniqueIds opr" and "calls S1 cId \<triangleq> Call opr res"
          by (auto simp add: getContextH_def restrict_map_def split: if_splits)
        thus False
          using inv4o noG by blast
      qed


      have qryOk': "\<exists>i. generatedIds S1 x \<triangleq> i"
        if q: "querySpec progr Op (getContextH (calls S1) (happensBefore S1) (Some vis)) res"
          and no: "x \<notin> uniqueIds Op"
          and noG: "x \<in> uniqueIds res"
        for Op vis res x
        by (meson domD no noG q qryOk)


      have "x \<in> dom (generatedIds S2)"
        if "x \<in> action_outputs action"
        for x
        using `S1 ~~ (i, action) \<leadsto> S2` that
        by (meson domIff generatedIds_mono2_rev inv1_i inv1_i1 invocation_cannot_guess_ids_step subsetD)


      show "\<exists>uids\<subseteq>dom (generatedIds S2). invocation_cannot_guess_ids uids i' S2"
        for i'
      proof (cases "i' = i")
        case True
        have "uids_i \<union> action_inputs action \<subseteq> dom (generatedIds S2)"
          using `S1 ~~ (i, action) \<leadsto> S2` inv1_i1 i_in_out 
          apply (auto simp add: step.simps)
          apply (meson in_dom qryOk')
          using inv2 by blast

        moreover 
        have "invocation_cannot_guess_ids (uids_i \<union> action_inputs action) i S2"
          using \<open>S1 ~~ (i, action) \<leadsto> S2\<close> inv1_i show_invocation_cannot_guess_ids_step by blast


        ultimately
        show ?thesis
          using True by blast 
      next
        case False
        obtain uids where "uids\<subseteq>dom (generatedIds S1)" and "invocation_cannot_guess_ids uids i' S1"
          using inv1 by auto


        show ?thesis 
        proof (intro exI conjI)
          show "uids \<subseteq> dom (generatedIds S2)"
            using \<open>S1 ~~ (i, action) \<leadsto> S2\<close> \<open>uids \<subseteq> dom (generatedIds S1)\<close> generatedIds_mono map_le_implies_dom_le by blast
          show "invocation_cannot_guess_ids uids i' S2"
            using False \<open>S1 ~~ (i, action) \<leadsto> S2\<close> \<open>invocation_cannot_guess_ids uids i' S1\<close> show_invocation_cannot_guess_ids_step_other by blast
        qed
      qed

      show "uniqueIds opr \<subseteq> dom (generatedIds S2)"
        if c0: "calls S2 c \<triangleq> Call opr r"
        for  c opr r
        using `S1 ~~ a \<leadsto> S2` that inv3 a_def action_outputs.simps(5) i_in_out inv1_i1
        by (auto simp add: step.simps split: if_splits) blast+

      show "uniqueIds r \<subseteq> dom (generatedIds S2)"
        if c0: "calls S2 c \<triangleq> Call opr r"
        for  c opr r
        using `S1 ~~ a \<leadsto> S2` that
        apply (auto simp add: step.simps domD inv4r split: if_splits)
        by (metis (mono_tags, hide_lams) action_outputs.simps(5) in_dom inv1 invocation_cannot_guess_ids_step qryOk' step.hyps(3))

    qed
  qed


  from H
  show "\<And>i. \<lbrakk>state_wellFormed S; program_wellFormed (prog S)\<rbrakk>
         \<Longrightarrow> \<exists>uids\<subseteq>dom (generatedIds S). invocation_cannot_guess_ids uids i S"
    by blast
  from H
  show "\<lbrakk>state_wellFormed S; program_wellFormed (prog S)\<rbrakk> \<Longrightarrow> knownIds S \<subseteq> dom (generatedIds S)"
    by blast
  from H
  show "\<And>c opr r.
       \<lbrakk>calls S c \<triangleq> Call opr r; state_wellFormed S; program_wellFormed (prog S)\<rbrakk>
       \<Longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S)"
    by blast
  from  H
  show "\<And>c opr r.
       \<lbrakk>calls S c \<triangleq> Call opr r; state_wellFormed S; program_wellFormed (prog S)\<rbrakk> \<Longrightarrow> uniqueIds r \<subseteq> dom (generatedIds S)"
    by blast

qed

lemmas wf_knownIds_subset_generatedIds = wf_knownIds_subset_generatedIds_h(2)

lemma wf_knownIds_subset_generatedIds2:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and "x \<in> knownIds S"
  shows "x \<in> dom (generatedIds S)"
  using assms
  by (meson domExists_simp in_dom wf_knownIds_subset_generatedIds)




lemma wf_onlyGeneratedIdsInKnownIds:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "uid \<notin> knownIds S"
  by (meson domIff local.wf not_generated prog_wf wf_knownIds_subset_generatedIds2)




lemma wf_onlyGeneratedIdsInCalls:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "calls S c \<triangleq> Call opr r \<Longrightarrow> uid \<notin> uniqueIds opr"
  by (meson domIff in_mono local.wf not_generated prog_wf wf_knownIds_subset_generatedIds_h(3))


lemma wf_onlyGeneratedIdsInCallResults:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "calls S c \<triangleq> Call opr r \<Longrightarrow> uid \<notin> uniqueIds r"
  by (meson domIff in_mono local.wf not_generated prog_wf wf_knownIds_subset_generatedIds_h(4))

lemma wf_onlyGeneratedIdsInInvocationOps:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "invocationOp S c \<triangleq> opr \<Longrightarrow> uid \<notin> uniqueIds opr"
  using wf prog_wf not_generated proof (induct rule: wellFormed_induct)
  case initial
  then show ?case 
    by (auto simp add: initialState_def)

next
  case (step t a s)
  then show ?case 
    using wf_onlyGeneratedIdsInKnownIds by (auto simp add: step.simps split: if_splits, goal_cases "new_invoc", blast)
qed

lemma wf_onlyGeneratedIdsInInvocationRes:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "invocationRes S c \<triangleq> res \<Longrightarrow> uid \<notin> uniqueIds res"

  using wf prog_wf not_generated proof (induct rule: wellFormed_induct)
  case initial
  then show ?case 
    by (auto simp add: initialState_def)

next
  case (step t a s)
  then show ?case 
    by (auto simp add: step.simps split: if_splits,
        metis (mono_tags, hide_lams) action_outputs.simps(7) domIff invocation_cannot_guess_ids_step step.hyps(1) step.hyps(3) subsetD wf_knownIds_subset_generatedIds_h(1))
qed


lemma use_invocation_cannot_guess_ids_dbop:
  assumes "invocation_cannot_guess_ids uids i S"
and "S ~~ (i, ADbOp c Op res) \<leadsto> S'"
  shows "uniqueIds Op \<subseteq> uids"
  using action_outputs.simps(5) assms(1) assms(2) invocation_cannot_guess_ids_step by blast

lemma use_invocation_cannot_guess_ids_return:
  assumes "invocation_cannot_guess_ids uids i S"
and "S ~~ (i, AReturn res) \<leadsto> S'"
shows "uniqueIds res \<subseteq> uids"
  using action_outputs.simps(7) assms(1) assms(2) invocation_cannot_guess_ids_step by blast


(*
text "We restrict the definition invocation_cannot_guess_ids to a 
specific local state and procedure implementation:"



definition procedure_cannot_guess_ids :: "('proc::valueType) itself \<Rightarrow> uniqueId set \<Rightarrow> 'ls \<Rightarrow> ('ls, 'operation::valueType, 'any::valueType) procedureImpl \<Rightarrow> bool" where
"procedure_cannot_guess_ids _ uids ls impl \<equiv>
\<forall>(S::('proc, 'ls, 'operation, 'any) state) (i::invocId). 
      localState S i \<triangleq> ls 
  \<longrightarrow> currentProc S i \<triangleq> impl 
  \<longrightarrow> invocation_cannot_guess_ids uids i S"

lemmas use_procedure_cannot_guess_ids = procedure_cannot_guess_ids_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]


definition procedures_cannot_guess_ids :: "('proc::valueType \<Rightarrow> ('ls \<times> ('ls, 'operation::valueType, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
  "procedures_cannot_guess_ids proc = 
(\<forall>p ls impl uids. proc p = (ls, impl) \<longrightarrow>  procedure_cannot_guess_ids (TYPE('proc)) (uids\<union>uniqueIds p) ls impl)"

lemmas use_procedures_cannot_guess_ids = procedures_cannot_guess_ids_def[THEN iffD1, rule_format]


text "Show: if all procedures cannot guess ids, then program is also wellformed."


lemma invocations_cannot_guess_ids_if_procedures:
  assumes "procedures_cannot_guess_ids (procedure progr)"
  shows "invocations_cannot_guess_ids progr"
  unfolding invocations_cannot_guess_ids_def 
proof (rule, rule show_invocation_cannot_guess_ids)
  fix i x tr a S'
  assume a0: "initialState progr ~~ tr @ [(i,a)] \<leadsto>* S'"
    and a1: "x \<in> action_outputs a"
    and a2: "x \<notin> {}"

 
  

  have s: "invocation_cannot_guess_ids (trace_inputs tr i) i S"
    if "initialState progr ~~ tr \<leadsto>* S"
      and "invocationOp S i \<noteq> None"
    for S
    using that  proof (induct rule: steps_induct)
    case initial
    then show ?case
      by (simp add: initialState_def)
  next
    case (step S' tr a S'')

    have [simp]: "prog S' = progr"
      by (metis (no_types, lifting) distributed_state.simps(1) initialState_def step.steps steps_do_not_change_prog)


    show ?case 
    proof (cases "invocationOp S' i = None")
      case True

      have [simp]: "localState S' i = None"
        using True invocation_ops_if_localstate_nonempty step.steps by blast


      from step.step
      obtain proc initialState impl
        where c0: "a = (i, AInvoc proc)"
          and S''_def: "S'' = S' \<lparr>localState := localState S'(i \<mapsto> initialState), currentProc := currentProc S'(i \<mapsto> impl), visibleCalls := visibleCalls S'(i \<mapsto> {}), invocationOp := invocationOp S'(i \<mapsto> proc)\<rparr>"
          and c2: "procedure progr proc = (initialState, impl)"
          and c3: "uniqueIds proc \<subseteq> knownIds S'"
          and c4: "invocationOp S' i = None"
        apply atomize_elim
        using `invocationOp S' i = None` `invocationOp S'' i \<noteq> None`
        by (auto simp add: step.simps split: if_splits)


      from use_procedures_cannot_guess_ids[OF `procedures_cannot_guess_ids (procedure progr)`
          `procedure progr proc = (initialState, impl)`]
      have t: "procedure_cannot_guess_ids TYPE('a) ({} \<union> uniqueIds proc) initialState impl" .
      
      
      hence "invocation_cannot_guess_ids (uniqueIds proc) i S''"
      proof (fuzzy_rule use_procedure_cannot_guess_ids)
        show "{} \<union> uniqueIds proc = uniqueIds proc" by simp
        show " localState S'' i \<triangleq> initialState" by (simp add: S''_def)
        show "currentProc S'' i \<triangleq> impl"  by (simp add: S''_def)
      qed

      have "(i,a) \<notin> set tr" if " \<And>t. a \<noteq> AInvcheck t" for a
        using step.steps `invocationOp S' i = None` that
        by (rule no_steps_in_i')

      hence "trace_inputs (tr @ [a]) i = uniqueIds proc"
        using `a = (i, AInvoc proc)`
        by (auto simp add: trace_inputs_def action_inputs_cases split: action.splits)


      show ?thesis
        by (simp add: \<open>invocation_cannot_guess_ids (uniqueIds proc) i S''\<close> \<open>trace_inputs (tr @ [a]) i = uniqueIds proc\<close>)
    next
      case False
      hence " invocation_cannot_guess_ids (trace_inputs tr i) i S'"
        by (simp add: step.IH)

      show ?thesis
      proof (cases "get_invoc a = i")
        case True
        show ?thesis
          using `invocation_cannot_guess_ids (trace_inputs tr i) i S'`
        proof (fuzzy_rule show_invocation_cannot_guess_ids_step) 
          show  "S' ~~ (i, snd a) \<leadsto> S''"
            using `get_invoc a = i` step.step by auto
          show "trace_inputs tr i \<union> action_inputs (get_action a) = trace_inputs (tr @ [a]) i"
            by (auto simp add: trace_inputs_def `get_invoc a = i`)
        qed
      next
        case False
        show ?thesis
        proof (fuzzy_rule show_invocation_cannot_guess_ids_step_other)
          from `invocation_cannot_guess_ids (trace_inputs tr i) i S'`
          show "invocation_cannot_guess_ids (trace_inputs (tr @ [a]) i) i S'"
            using `get_invoc a \<noteq> i`
            by (auto simp add: trace_inputs_def)
          show "S' ~~ (get_invoc a, get_action a) \<leadsto> S''"
            by (simp add: step.step)
          show "get_invoc a \<noteq> i" using False.
        qed
      qed
    qed
  qed

  from `initialState progr ~~ tr @ [(i,a)] \<leadsto>* S'`
  obtain S1 where "initialState progr ~~ tr \<leadsto>* S1"
    and "S1 ~~ (i,a) \<leadsto> S'"
    using steps_appendBack by blast

  show "x \<in> trace_inputs tr i"
  proof (cases "invocationOp S1 i")
    case None

    have [simp]: "localState S1 i = None"
      using None \<open>initialState progr ~~ tr \<leadsto>* S1\<close> invocation_ops_if_localstate_nonempty by blast

    from `S1 ~~ (i,a) \<leadsto> S'` a1
    show ?thesis
      by (auto simp add: step.simps)
  next
    case (Some proc)
    from s[OF `initialState progr ~~ tr \<leadsto>* S1`]
    have t: "invocation_cannot_guess_ids (trace_inputs tr i) i S1"
      using Some by blast

    thus ?thesis 
      using `S1 ~~ (i,a) \<leadsto> S'` a1
      by (rule invocation_cannot_guess_ids_step)
  qed
qed

*)

end
