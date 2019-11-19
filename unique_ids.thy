theory unique_ids
  imports execution_invariants
begin

inductive procedure_cannot_guess_ids :: "uniqueId set \<Rightarrow> 'ls \<Rightarrow> ('ls, 'operation::valueType, 'any::valueType) procedureImpl \<Rightarrow> bool"  where
pcgi_local:  "\<lbrakk>impl ls = LocalStep ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_beginAtomic: "\<lbrakk>impl ls = BeginAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_endAtomic:"\<lbrakk>impl ls = EndAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_newId:"\<lbrakk>impl ls = NewId f; \<And>uid ls'. f uid \<triangleq> ls' \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds uid) ls' impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_dbop: "\<lbrakk>impl ls = DbOperation opr f;  uniqueIds opr \<subseteq> uids; 
    \<And>res. procedure_cannot_guess_ids (uids \<union> uniqueIds res) (f res) impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_return: "\<lbrakk>impl ls = Return r; uniqueIds r \<subseteq> uids\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls impl"

find_theorems procedure_cannot_guess_ids

lemma pcgi_local_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = LocalStep ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
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


lemma procedure_cannot_guess_ids_mono:
  assumes "procedure_cannot_guess_ids uids ls impl"
and "uids \<subseteq> uids'"
shows "procedure_cannot_guess_ids uids' ls impl"
  using assms apply (induct  arbitrary: uids uids' rule: procedure_cannot_guess_ids.induct)
       apply (auto simp add: procedure_cannot_guess_ids.intros)
    apply (meson procedure_cannot_guess_ids.intros(4) sup.cobounded1)
   apply (rule  procedure_cannot_guess_ids.intros, assumption )
    apply auto
    defer
    apply blast

  oops  




definition procedures_cannot_guess_ids :: "('proc::valueType \<rightharpoonup> ('ls \<times> ('ls, 'operation::valueType, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
"procedures_cannot_guess_ids proc = 
(\<forall>p ls impl uids. proc p \<triangleq> (ls, impl) \<longrightarrow>  procedure_cannot_guess_ids (uids\<union>uniqueIds p) ls impl)"

lemmas show_procedures_cannot_guess_ids = procedures_cannot_guess_ids_def[THEN iffD1, rule_format]

definition queries_cannot_guess_ids :: "('operation \<Rightarrow> ('operation::valueType, 'any::valueType) operationContext \<Rightarrow> 'any \<Rightarrow> bool) \<Rightarrow> bool"  where
"queries_cannot_guess_ids qry \<equiv> 
  \<forall>opr ctxt res. 
   qry opr ctxt res \<longrightarrow> uniqueIds res \<subseteq> uniqueIds opr \<union> \<Union>{uniqueIds (call_operation c) | cId c. calls ctxt cId \<triangleq> c}"


lemma queries_cannot_guess_ids_def2:
"queries_cannot_guess_ids qry =
  (\<forall>opr ctxt res x. 
   qry opr ctxt res 
 \<longrightarrow> x \<in> uniqueIds res 
 \<longrightarrow> x \<notin> uniqueIds opr
 \<longrightarrow> (\<exists>cId opr res. calls ctxt cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr))"
  apply (auto simp add: queries_cannot_guess_ids_def)
   apply ((drule spec)+,drule(1) mp) 
   apply (drule(1) subsetD)
   apply auto
   apply (metis call.collapse)
  by force


definition program_wellFormed :: " ('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) prog \<Rightarrow> bool" where
"program_wellFormed progr \<equiv> 
   procedures_cannot_guess_ids (procedure progr)
 \<and> queries_cannot_guess_ids (querySpec progr)
"

lemma exists_elim_h: "\<lbrakk>P x; Q x\<rbrakk> \<Longrightarrow> \<exists>x. P x \<and> Q x" for P Q x
    by auto



lemma wf_knownIds_subset_generatedIds_h:
  fixes S :: "('proc::valueType, 'ls, 'operation::valueType, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
  shows "\<And>i ls impl. localState S i \<triangleq> ls \<Longrightarrow> currentProc S i \<triangleq> impl \<Longrightarrow> \<exists>uids\<subseteq>dom (generatedIds S). procedure_cannot_guess_ids uids ls impl"
    and "knownIds S \<subseteq> dom (generatedIds S)"
    and "\<And>c opr r. calls S c \<triangleq> Call opr r \<Longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S)"

  using wf prog_wf
proof -


  from wf prog_wf
  have H: "(\<forall>i ls impl. localState S i \<triangleq> ls \<and> currentProc S i \<triangleq> impl
      \<longrightarrow> (\<exists>uids. uids \<subseteq> dom (generatedIds S) \<and> procedure_cannot_guess_ids uids ls impl))
       \<and> (knownIds S \<subseteq> dom (generatedIds S))
       \<and> (\<forall>c opr r. calls S c \<triangleq> Call opr r \<longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S))"
  proof (induct rule: wellFormed_induct)
    case initial
    then show ?case by (simp add: initialState_def)
  next
    case (step S1 a S2)

    obtain progr where [simp]: "prog S1 = progr"
      by auto

    have [simp]: "prog S2 = progr"
      using \<open>prog S1 = progr\<close> prog_inv step.hyps(3) by blast

    have  prog_wf: "program_wellFormed progr"
      using \<open>prog S2 = progr\<close> step.prems by blast


    from prog_wf
    have "procedures_cannot_guess_ids (procedure progr)"
      and "queries_cannot_guess_ids (querySpec progr)"
      using program_wellFormed_def by auto





    have inv1: "(\<exists>uids\<subseteq>dom (generatedIds S). procedure_cannot_guess_ids uids ls impl)"
      if "localState S i \<triangleq> ls" 
        and "currentProc S i \<triangleq> impl"
        and "S1 = S"
      for S i ls impl
      using \<open>prog S1 = progr\<close> step.hyps(2) step.prems that by auto


    have inv2: "knownIds S1 \<subseteq> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> prog_wf step.hyps(2) by blast


    have inv3: "uniqueIds opr \<subseteq> dom (generatedIds S1)" 
      if "calls S1 c \<triangleq> Call opr r"
      for c opr r
      using \<open>prog S1 = progr\<close> prog_wf step.hyps(2) that by blast




    obtain action i where a_def: "a = (i, action)"
      using surjective_pairing by blast



    show "?case"
    proof (intro allI conjI impI, elim conjE)

      show "knownIds S2 \<subseteq> dom (generatedIds S2)"
        using `S1 ~~ a \<leadsto> S2` inv2
        apply (auto simp add: step.simps)
         apply blast
        by (meson in_dom inv1 pcgi_return_case subsetD) 



      show "\<exists>uids\<subseteq>dom (generatedIds S2). procedure_cannot_guess_ids uids ls' impl'"
        if c0: "localState S2 i' \<triangleq> ls'" and c1: "currentProc S2 i' \<triangleq> impl'"
        for  i' ls' impl'
        using `S1 ~~ a \<leadsto> S2` 
      proof (cases rule: step.cases)
        case (local i ls f ls')
        then show ?thesis
          using c0 c1
          apply (auto simp add: inv1 split: if_splits)
          apply (meson inv1 pcgi_local_case)
          done
      next
        case (newId i ls f ls' uid uidv ls'')
        then show ?thesis using c0 c1
          apply (auto simp add: inv1 split: if_splits)
           apply (smt Un_insert_right insertI1 insert_subset inv1 pcgi_newId_case subset_insertI2 sup_bot.right_neutral)
          by (meson inv1 subset_insertI2)
      next
        case (beginAtomic i ls f ls' t vis snapshot)
        then show ?thesis using c0 c1
          apply (auto simp add: inv1 split: if_splits)
          by (meson inv1 pcgi_beginAtomic_case)
      next
        case (endAtomic i ls f ls' t)
        then show ?thesis using c0 c1
          apply (auto simp add: inv1 split: if_splits)
          by (meson inv1 pcgi_endAtomic_case)
      next
        case (dbop i'' ls1 f Op ls2 t c res vis)
        then show ?thesis using c0 c1
          apply (auto simp add: inv1 a_def split: if_splits)
        proof -

          show "\<exists>uids\<subseteq>dom (generatedIds S1). procedure_cannot_guess_ids uids (ls2 res) impl'"
            if c0: "f = impl'"
              and c1: "S2 = S1 \<lparr>localState := localState S1(i'' \<mapsto> ls2 res), calls := calls S1(c \<mapsto> Call Op res), callOrigin := callOrigin S1(c \<mapsto> t), visibleCalls := visibleCalls S1(i'' \<mapsto> insert c vis), happensBefore := happensBefore S1 \<union> vis \<times> {c}\<rparr>"
              and c2: "localState S1 i'' \<triangleq> ls1"
              and c3: "currentProc S1 i'' \<triangleq> impl'"
              and c4: "impl' ls1 = DbOperation Op ls2"
              and c5: "currentTransaction S1 i'' \<triangleq> t"
              and c6: "calls S1 c = None"
              and c7: "querySpec progr Op (getContextH (calls S1) (happensBefore S1) (Some vis)) res"
              and c8: "visibleCalls S1 i'' \<triangleq> vis"
              and c9: "i' = i''"
              and c10: "i = i''"
              and c11: "action = ADbOp c Op res"
              and c12: "ls' = ls2 res"


          proof -
            from  inv1[OF c2 c3]
            obtain uids
              where uids_dom: "uids\<subseteq>dom (generatedIds S1)"
                and uids_cannot_guess: " procedure_cannot_guess_ids uids ls1 impl'"
              by auto



            show "\<exists>uids\<subseteq>dom (generatedIds S1). procedure_cannot_guess_ids uids (ls2 res) impl'"
            proof (intro exI conjI)

              from pcgi_dbop_case2[OF `procedure_cannot_guess_ids uids ls1 impl'` c4, where res=res]
              show "procedure_cannot_guess_ids (uids \<union> uniqueIds res) (ls2 res) impl'"
                by simp


              have ids_from_call: "x \<in> uniqueIds Op \<or> (\<exists>cId opr res. calls (getContextH (calls S1) (happensBefore S1) (Some vis)) cId \<triangleq> Call opr res \<and> x \<in> uniqueIds opr)"
                if "x \<in> uniqueIds res" 
                for x
                using queries_cannot_guess_ids_def2[THEN iffD1, rule_format, OF `queries_cannot_guess_ids (querySpec progr)` c7 that] 
                by auto

              have "\<exists>y. generatedIds S1 x \<triangleq> y"
                if  "x \<in> uniqueIds res"
                for  x
                using ids_from_call[OF that] proof auto

                show "\<exists>y. generatedIds S1 x \<triangleq> y"
                  if c0: "x \<in> uniqueIds Op"
                  by (meson \<open>S1 = S1 \<Longrightarrow> \<exists>uids\<subseteq>dom (generatedIds S1). procedure_cannot_guess_ids uids ls1 impl'\<close> c4 domD pcgi_dbop_case1 subset_h1 that)


                show "\<exists>y. generatedIds S1 x \<triangleq> y"
                  if c0: "x \<in> uniqueIds opr"
                    and c1: "calls (getContextH (calls S1) (happensBefore S1) (Some vis)) cId \<triangleq> Call opr res"
                  for  cId opr res
                  using that
                  apply (auto simp add: getContextH_def restrict_map_def split: if_splits)
                  by (meson domD in_mono inv3)
              qed

              with this
              show "uids \<union> uniqueIds res \<subseteq> dom (generatedIds S1)"
                apply auto
                using \<open>uids \<subseteq> dom (generatedIds S1)\<close> by blast
            qed
          qed
        qed
      next
        case (invocation i proc initialState impl)
        then show ?thesis using c0 c1
          apply (auto simp add: inv1 split: if_splits)
          by (metis (no_types, lifting) \<open>procedures_cannot_guess_ids (procedure progr)\<close> inv2 show_procedures_cannot_guess_ids subset_Un_eq subset_refl subset_trans)
      next
        case (return i ls f res)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits)
      next
        case (fail i ls)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits)
      next
        case (invCheck res i)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits)
      qed

      show "uniqueIds opr \<subseteq> dom (generatedIds S2)"
        if c0: "calls S2 c \<triangleq> Call opr r"
        for  c opr r
        using `S1 ~~ a \<leadsto> S2` that inv3
        by (auto simp add: step.simps split: if_splits;
            meson domD in_mono inv1 pcgi_dbop_case1 | blast
            )
    qed
  qed


  from H
  show "knownIds S \<subseteq> dom (generatedIds S)"
    "\<And>i ls impl.
       \<lbrakk>localState S i \<triangleq> ls; currentProc S i \<triangleq> impl; state_wellFormed S; program_wellFormed (prog S)\<rbrakk>
       \<Longrightarrow> \<exists>uids\<subseteq>dom (generatedIds S). procedure_cannot_guess_ids uids ls impl"
    "\<And>c opr r. \<lbrakk>calls S c \<triangleq> Call opr r; state_wellFormed S; program_wellFormed (prog S)\<rbrakk> \<Longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S)"
    by blast+

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




end
