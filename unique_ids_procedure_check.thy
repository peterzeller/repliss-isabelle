theory unique_ids_procedure_check
  imports unique_ids
begin

inductive procedure_cannot_guess_ids :: "uniqueId set \<Rightarrow> 'ls \<Rightarrow> ('ls, 'op::valueType, 'any::valueType) procedureImpl \<Rightarrow> bool"  where
  pcgi_local:  "\<lbrakk>impl ls = LocalStep ok ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_beginAtomic: "\<lbrakk>impl ls = BeginAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_endAtomic:"\<lbrakk>impl ls = EndAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_newId:"\<lbrakk>impl ls = NewId f; \<And>uid ls'. f uid \<triangleq> ls' \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds uid) ls' impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_dbop: "\<lbrakk>impl ls = DbOperation opr f;  uniqueIds opr \<subseteq> uids; 
    \<And>res. procedure_cannot_guess_ids (uids \<union> uniqueIds res) (f res) impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_return: "\<lbrakk>impl ls = Return r; uniqueIds r \<subseteq> uids\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls impl"


lemma pcgi_local_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = LocalStep ok ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_beginAtomic_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = BeginAtomic ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_endAtomic_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = EndAtomic ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_newId_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = NewId f\<rbrakk> \<Longrightarrow> f uid \<triangleq> ls' \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds uid) ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_dbop_case1:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = DbOperation opr f\<rbrakk> \<Longrightarrow> uniqueIds opr \<subseteq> uids"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_dbop_case2:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = DbOperation opr f\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds res) (f res) impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_return_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = Return r\<rbrakk> \<Longrightarrow> uniqueIds r \<subseteq> uids"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)






definition procedures_cannot_guess_ids :: "('proc::valueType \<Rightarrow> ('ls \<times> ('ls, 'op::valueType, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
  "procedures_cannot_guess_ids proc = 
(\<forall>p ls impl uids. proc p = (ls, impl) \<longrightarrow>  procedure_cannot_guess_ids (uids\<union>uniqueIds p) ls impl)"

lemmas show_procedures_cannot_guess_ids = procedures_cannot_guess_ids_def[THEN iffD1, rule_format]


lemma pscgi_to_iscgi:
  assumes "procedures_cannot_guess_ids (procedure progr)"
  shows "invocations_cannot_guess_ids progr"
  unfolding invocations_cannot_guess_ids_def invocation_cannot_guess_ids_def
proof (intro allI impI)

  fix i1 tr1 a S'
  assume steps: "initialState progr ~~ tr1 @ [a] \<leadsto>* S'"

  define tr1a where "tr1a = tr1@[a]"

  from steps
  have "initialState progr ~~ tr1a \<leadsto>* S'"
    using tr1a_def by blast

  value "butlast [1,2,3::nat]"

  from this 
  have "trace_outputs tr1a i1 \<subseteq> trace_inputs (butlast tr1a) i1
    \<and> (\<forall>ls impl. localState S' i1 \<triangleq> ls 
        \<longrightarrow>  currentProc S' i1 \<triangleq> impl 
        \<longrightarrow> procedure_cannot_guess_ids (trace_inputs tr1a i1) ls impl)"
  proof (induct rule: steps_induct)
    case initial
    then show ?case
      by (auto simp add: initialState_def trace_outputs_def)

  next
    case (step S' tr a S'')

    have IH1: "trace_outputs tr i1 \<subseteq> trace_inputs (butlast tr) i1"
      using step by auto

    hence IH1': "trace_outputs tr i1 \<subseteq> trace_inputs tr i1"
      by (induct tr rule: rev_induct, auto simp add:  trace_inputs_append)

    have IH2: "procedure_cannot_guess_ids (trace_inputs tr i1) ls impl "
      if "localState S' i1 \<triangleq> ls"
        and "currentProc S' i1 \<triangleq> impl"
      for ls impl
      using step that by blast



    show ?case
    proof (cases "get_invoc a = i1")
      case False
      have [simp]: "trace_inputs (tr @ [a]) i1 = trace_inputs tr i1"
        by (simp add: False trace_inputs_def)
      have [simp]: "trace_outputs (tr @ [a]) i1 = trace_outputs tr i1"
        by (simp add: False trace_outputs_def)

      show ?thesis
        using IH1' IH2 apply (auto simp add: step)
        by (metis False IH2 prod.collapse step.step unchangedInTransaction(1) unchangedInTransaction(2))
    next
      case True



      from `S' ~~ a \<leadsto> S''`
      have "action_outputs (get_action a) \<subseteq> trace_inputs tr i1" 
      proof cases
        case (dbop i ls f Op ls' t c res vis)
        have pcgi: "procedure_cannot_guess_ids (trace_inputs tr i1) ls f"
          using True local.dbop(1) local.dbop(3) local.dbop(4) step.IH by auto

        from pcgi_dbop_case1[OF pcgi `f ls = DbOperation Op ls'`]
        have " uniqueIds Op \<subseteq> trace_inputs tr i1" .
        then show ?thesis 
          by (auto simp add: `a = (i, ADbOp c Op res)` trace_outputs_empty)
      next
        case (return i ls f res)
        have pcgi: "procedure_cannot_guess_ids (trace_inputs tr i1) ls f"
          using IH2 True local.return(1) local.return(3) local.return(4) by auto

        from pcgi_return_case[OF pcgi]
        show ?thesis
          by (auto simp add: return)
      qed auto

      have [simp]: "(trace_inputs (tr @ [(i, action)]) i1)
          = trace_inputs tr i1 \<union> (if i = i1 then action_inputs action else {})" for i action
        by (auto simp add: trace_inputs_append trace_inputs_cons trace_inputs_empty)

      from `S' ~~ a \<leadsto> S''`
      have "procedure_cannot_guess_ids (trace_inputs (tr @ [a]) i1) ls impl"
        if l1: "localState S'' i1 \<triangleq> ls"
        and l2: "currentProc S'' i1 \<triangleq> impl"
      for ls impl
      proof cases
        case (local i ls f ok ls')
        then show ?thesis
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          by (meson pcgi_local_case)
      next
        case (newId i ls f ls' uid uidv ls'')
        then show ?thesis 
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          using pcgi_newId_case by fastforce
      next
        case (beginAtomic i ls f ls' t vis snapshot)
        then show ?thesis 
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          by (meson pcgi_beginAtomic_case)
      next
        case (endAtomic i ls f ls' t)
        then show ?thesis 
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          by (meson pcgi_endAtomic_case)
      next
        case (dbop i ls f Op ls' t c res vis)
        then show ?thesis 
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          by (meson pcgi_dbop_case2)
      next
        case (invocation i proc initialState impl)
        from  `procedures_cannot_guess_ids (procedure progr)`
        have "procedure_cannot_guess_ids (uniqueIds proc) initialState impl"
          apply (auto simp add: procedures_cannot_guess_ids_def)
          by (metis (no_types, lifting) state.select_convs(1) initialState_def local.invocation(4) step.steps steps_do_not_change_prog sup.idem)

        from invocation
        show ?thesis 
          using IH2 l1 l2 apply (auto simp add:  split: if_splits)
          by (metis (no_types, lifting) assms state.select_convs(1) initialState_def show_procedures_cannot_guess_ids step.steps steps_do_not_change_prog)
      next
        case (return i ls f res)
        then show ?thesis 
          using IH2 l1 l2 by (auto simp add:  split: if_splits)
      next
        case (crash i ls)
        then show ?thesis 
          using IH2 l1 l2 by (auto simp add:  split: if_splits)
      next
        case (invCheck res i)
        then show ?thesis 
          using IH2 l1 l2 by (auto simp add:  split: if_splits)
      qed

      thus ?thesis
        using  IH1' \<open>action_outputs (get_action a) \<subseteq> trace_inputs tr i1\<close> by (auto simp add: trace_outputs_append True subsetD trace_outputs_cons trace_outputs_empty)
    qed
  qed
  thus "trace_outputs (tr1 @ [a]) i1 \<subseteq> trace_inputs tr1 i1 \<union> {}"
    by (simp add: tr1a_def)
qed


end