section "Unique Identifiers"
theory unique_ids
  imports execution_invariants
begin


text \<open>In this section we prove some general properties about unique identifiers.

In general, we assume that procedure implementations are well behaved and cannot produce unique
identifiers out of thin air (i.e. ``guess'' them).
We define this property inductively:
\<close>


inductive procedure_cannot_guess_ids :: "uniqueId set \<Rightarrow> 'ls \<Rightarrow> ('ls, 'operation::valueType, 'any::valueType) procedureImpl \<Rightarrow> bool"  where
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






definition procedures_cannot_guess_ids :: "('proc::valueType \<Rightarrow> ('ls \<times> ('ls, 'operation::valueType, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
  "procedures_cannot_guess_ids proc = 
(\<forall>p ls impl uids. proc p = (ls, impl) \<longrightarrow>  procedure_cannot_guess_ids (uids\<union>uniqueIds p) ls impl)"

lemmas show_procedures_cannot_guess_ids = procedures_cannot_guess_ids_def[THEN iffD1, rule_format]

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
    and "\<And>c opr r. calls S c \<triangleq> Call opr r \<Longrightarrow> uniqueIds r \<subseteq> dom (generatedIds S)"

  using wf prog_wf
proof -


  from wf prog_wf
  have H: "(\<forall>i ls impl. localState S i \<triangleq> ls \<and> currentProc S i \<triangleq> impl
      \<longrightarrow> (\<exists>uids. uids \<subseteq> dom (generatedIds S) \<and> procedure_cannot_guess_ids uids ls impl))
       \<and> (knownIds S \<subseteq> dom (generatedIds S))
       \<and> (\<forall>c opr r. calls S c \<triangleq> Call opr r \<longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S) \<and> uniqueIds r \<subseteq> dom (generatedIds S))"
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
        by (auto simp add: step.simps dest!: pcgi_return_case inv1 split: if_splits, blast+ )




      show "\<exists>uids\<subseteq>dom (generatedIds S2). procedure_cannot_guess_ids uids ls' impl'"
        if c0: "localState S2 i' \<triangleq> ls'" and c1: "currentProc S2 i' \<triangleq> impl'"
        for  i' ls' impl'
        using `S1 ~~ a \<leadsto> S2` 
      proof (cases rule: step.cases)
        case (local i ls f ls')
        then show ?thesis
          using c0 c1
          by (auto simp add: inv1 split: if_splits, meson inv1 pcgi_local_case)
      next
        case (newId i ls f ls' uid uidv ls'')
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits,
           smt Un_insert_right insertI1 insert_subset inv1 pcgi_newId_case subset_insertI2 sup_bot.right_neutral,
           meson inv1 subset_insertI2)
      next
        case (beginAtomic i ls f ls' t vis snapshot)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits, 
              meson inv1 pcgi_beginAtomic_case)
      next
        case (endAtomic i ls f ls' t)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits,
             meson inv1 pcgi_endAtomic_case)
      next
        case (dbop i'' ls1 f Op ls2 t c res vis)
        then show ?thesis using c0 c1
        proof (auto simp add: inv1 a_def split: if_splits)

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
                  by (auto simp add: getContextH_def restrict_map_def split: if_splits,
                      meson domD in_mono inv3)
              qed

              with this
              show "uids \<union> uniqueIds res \<subseteq> dom (generatedIds S1)"
                using \<open>uids \<subseteq> dom (generatedIds S1)\<close> by auto
            qed
          qed
        qed
      next
        case (invocation i proc initialState impl)
        then show ?thesis using c0 c1
          by (auto simp add: inv1 split: if_splits, metis (no_types, lifting) \<open>procedures_cannot_guess_ids (procedure progr)\<close> inv2 show_procedures_cannot_guess_ids subset_Un_eq subset_refl subset_trans)
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
      hence call_ops_unique: "x\<in>dom(generatedIds S2)"
        if "x\<in>uniqueIds opr" and "calls S2 c \<triangleq> Call opr r"
        for  c opr r x
        using that by blast

      have query_no_guess: " query_cannot_guess_ids (uniqueIds opr) (querySpec progr opr)" for opr
        using \<open>queries_cannot_guess_ids (querySpec progr)\<close>
        by (auto simp add:  queries_cannot_guess_ids_def)

      have query_no_guess2: "\<exists>cId opr r. x \<in> uniqueIds opr \<and> calls ctxt cId \<triangleq> Call opr r"
        if "x\<in>uniqueIds res" 
          and " querySpec progr opr ctxt res "
          and "x\<notin> uniqueIds opr"
        for x res opr ctxt
        using that 
        by (metis (no_types, lifting) \<open>queries_cannot_guess_ids (querySpec progr)\<close> queries_cannot_guess_ids_def2) 

      have "x \<in> dom (generatedIds S2)"
        if c0: "calls S2 c \<triangleq> Call opr r"
          and c1: "x\<in>uniqueIds r"
        for  c opr r x

        using `S1 ~~ a \<leadsto> S2` that
      proof (cases rule: step.cases)
        case (dbop i ls f Op ls' t c' res vis)

        have "generatedIds S1 = generatedIds S2"
          using dbop by auto

        have "calls S2 c' \<triangleq> Call Op res"
          using dbop by auto

        from dbop show ?thesis
          using c0 c1 proof (auto split: if_splits, goal_cases "A" "B")
          case A
          have "calls S2 c \<triangleq> Call opr r"
            using A by auto


          have "x \<in> dom (generatedIds S2)" if "x \<in> uniqueIds opr"
            using call_ops_unique[OF `x \<in> uniqueIds opr` `calls S2 c \<triangleq> Call opr r`] by simp
          hence "x \<in> dom (generatedIds S1)" if "x \<in> uniqueIds opr"
            using \<open>generatedIds S1 = generatedIds S2\<close> that by auto



          show ?case
          proof (rule ccontr, auto)
            assume "generatedIds S1 x = None"
            hence "x \<notin> uniqueIds opr"
              using \<open>generatedIds S1 = generatedIds S2\<close> \<open>x \<in> uniqueIds opr \<Longrightarrow> x \<in> dom (generatedIds S2)\<close> by auto

            from query_no_guess2[OF `x \<in> uniqueIds r` `querySpec progr opr (getContextH (calls S1) (happensBefore S1) (Some vis)) r` `x \<notin> uniqueIds opr`]
            obtain cId opr' r'
              where "x \<in> uniqueIds opr'"
                and c: "calls S1 cId \<triangleq> Call opr' r'"
              by (auto simp add: getContextH_def restrict_map_def split: if_splits)




            from inv3[OF c]
            have "uniqueIds opr' \<subseteq> dom (generatedIds S1)"
              by blast


            show False
              using \<open>generatedIds S1 x = None\<close> \<open>uniqueIds opr' \<subseteq> dom (generatedIds S1)\<close> \<open>x \<in> uniqueIds opr'\<close> by blast
          qed
        next
          case B
          show ?case
            using B(12) \<open>prog S1 = progr\<close> c1 prog_wf step.hyps(2) by blast
        qed
      qed (insert c0 c1  \<open>prog S1 = progr\<close> prog_wf step.hyps(2), auto simp add: step.simps split: if_splits; blast)+

      thus "uniqueIds r \<subseteq> dom (generatedIds S2)"
        if c0: "calls S2 c \<triangleq> Call opr r"
        for  c opr r
        using that by blast
    qed
  qed


  from H
  show "knownIds S \<subseteq> dom (generatedIds S)"
    "\<And>i ls impl.
       \<lbrakk>localState S i \<triangleq> ls; currentProc S i \<triangleq> impl; state_wellFormed S; program_wellFormed (prog S)\<rbrakk>
       \<Longrightarrow> \<exists>uids\<subseteq>dom (generatedIds S). procedure_cannot_guess_ids uids ls impl"
    "\<And>c opr r. \<lbrakk>calls S c \<triangleq> Call opr r; state_wellFormed S; program_wellFormed (prog S)\<rbrakk> \<Longrightarrow> uniqueIds opr \<subseteq> dom (generatedIds S)"
    "\<And>c opr r.
       \<lbrakk>calls S c \<triangleq> Call opr r; state_wellFormed S; program_wellFormed (prog S)\<rbrakk>
       \<Longrightarrow> uniqueIds r \<subseteq> dom (generatedIds S)"
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
    by (auto simp add: step.simps split: if_splits, goal_cases "new_invoc",
       smt domIff pcgi_return_case subset_iff wf_knownIds_subset_generatedIds_h(1))

qed



end
