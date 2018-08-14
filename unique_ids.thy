theory unique_ids
  imports execution_invariants
begin



definition procedures_cannot_guess_ids :: "(procedureName \<Rightarrow> 'any list \<rightharpoonup> ('localState \<times> ('localState, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
"procedures_cannot_guess_ids proc \<equiv> 
 (* procedures produce no new ids *)
 (\<exists>uids. 
  \<forall>p args lsInit impl. proc p args \<triangleq> (lsInit, impl)
    \<longrightarrow> uids lsInit \<subseteq> uniqueIdsInList args
     \<and> (\<forall>ls. case impl ls of
             LocalStep ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | BeginAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | EndAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | NewId f \<Rightarrow> (\<forall>uid ls'. f uid \<triangleq> ls' \<longrightarrow> uids ls' \<subseteq> uids ls \<union> {uid})
           | DbOperation opr args f \<Rightarrow> 
                     uniqueIdsInList args \<subseteq> uids ls
                   \<and> (\<forall>res. uids (f res) \<subseteq> uids ls \<union> uniqueIds res)
           | Return r => uniqueIds r \<subseteq> uids ls
           ))"

schematic_goal show_procedures_cannot_guess_ids:
  fixes  procs  :: "(procedureName \<Rightarrow> 'any list \<rightharpoonup> ('localState \<times> ('localState, 'any::valueType) procedureImpl))"
    and uids :: " 'localState \<Rightarrow> 'any set"
  shows "?X uids \<Longrightarrow> procedures_cannot_guess_ids procs"
  apply (subst procedures_cannot_guess_ids_def)
  apply (rule_tac x=uids in exI)
  by assumption

definition queries_cannot_guess_ids :: "(operation \<Rightarrow> 'any::valueType list \<Rightarrow> 'any operationContext \<Rightarrow> 'any \<Rightarrow> bool) \<Rightarrow> bool"  where
"queries_cannot_guess_ids qry \<equiv> 
  \<forall>opr args ctxt res. 
   qry opr args ctxt res \<longrightarrow> uniqueIds res \<subseteq> uniqueIdsInList args \<union> \<Union>{uniqueIdsInList (call_args c) | cId c. calls ctxt cId \<triangleq> c}"


lemma queries_cannot_guess_ids_def2:
"queries_cannot_guess_ids qry =
  (\<forall>opr args ctxt res x. 
   qry opr args ctxt res 
 \<longrightarrow> x \<in> uniqueIds res 
 \<longrightarrow> x \<notin> uniqueIdsInList args
 \<longrightarrow> (\<exists>cId opr args res. calls ctxt cId \<triangleq> Call opr args res \<and> x \<in> uniqueIdsInList args))"
  apply (auto simp add: queries_cannot_guess_ids_def)
   apply ((drule spec)+,drule(1) mp) 
   apply (drule(1) subsetD)
   apply auto
   apply (metis call.collapse)
  by (metis call.sel(2))


definition program_wellFormed :: "('localState, 'any::valueType) prog \<Rightarrow> bool" where
"program_wellFormed progr \<equiv> 
   procedures_cannot_guess_ids (procedure progr)
 \<and> queries_cannot_guess_ids (querySpec progr)
"

lemma domExists_simp: "x \<in> dom f \<longleftrightarrow> (\<exists>y. f x \<triangleq> y)"
  by (auto)

lemma wf_knownIds_subset_generatedIds:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
  shows "knownIds S \<subseteq> dom (generatedIds S)"
proof -

  define progr where "progr \<equiv> prog S"

  from prog_wf
  have "procedures_cannot_guess_ids (procedure progr)"
   and "queries_cannot_guess_ids (querySpec progr)"
    using progr_def program_wellFormed_def by auto


  from `procedures_cannot_guess_ids (procedure progr)`
  obtain uids where cannotGuessLs: 
        "case impl ls of
             LocalStep ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | BeginAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | EndAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | NewId f \<Rightarrow> (\<forall>uid ls'. f uid \<triangleq> ls' \<longrightarrow> uids ls' \<subseteq> uids ls \<union> {uid})
           | DbOperation opr args f \<Rightarrow> 
                     uniqueIdsInList args \<subseteq> uids ls
                   \<and> (\<forall>res. uids (f res) \<subseteq> uids ls \<union> uniqueIds res)
           | Return r => uniqueIds r \<subseteq> uids ls
           " 
        and cannotGuessLs': "uids lsInit \<subseteq> uniqueIdsInList args"
      if "procedure progr' p args \<triangleq> (lsInit, impl)" 
        and "progr' = progr" 
      for progr' p args lsInit impl ls
    apply (auto simp add: procedures_cannot_guess_ids_def)
    by blast


  have cannotGuessLs2: 
        "case impl ls of
             LocalStep ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | BeginAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | EndAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | NewId f \<Rightarrow> (\<forall>uid ls'. f uid \<triangleq> ls' \<longrightarrow> uids ls' \<subseteq> uids ls \<union> {uid})
           | DbOperation opr args f \<Rightarrow> 
                     uniqueIdsInList args \<subseteq> uids ls
                   \<and> (\<forall>res. uids (f res) \<subseteq> uids ls \<union> uniqueIds res)
           | Return r => uniqueIds r \<subseteq> uids ls
           " if "currentProc S i \<triangleq> impl" for S :: "('localState, 'any::valueType) state" and i impl ls
  proof -
    from `currentProc S i \<triangleq> impl`
    obtain p args lsInit where  "procedure progr p args \<triangleq> (lsInit, impl)"
      sorry

    thus ?thesis
      by (rule cannotGuessLs, simp)
  qed

  from `queries_cannot_guess_ids (querySpec progr)`
  have cannotGuessQ: "x \<in> uniqueIdsInList args \<or> (\<exists>cId c. calls ctxt cId \<triangleq> c \<and>  x \<in> uniqueIdsInList (call_args c))" 
    if "querySpec progr' opr args ctxt res" 
      and "progr' = progr" 
      and "x \<in> uniqueIds res"
    for progr' opr args ctxt res x
    using that apply (auto simp add: queries_cannot_guess_ids_def)
    by blast



  have "(\<forall>i ls. localState S i \<triangleq> ls \<longrightarrow> uids ls \<subseteq> dom (generatedIds S)) 
       \<and> (\<forall>cId c. calls S cId \<triangleq> c \<longrightarrow> uniqueIdsInList (call_args c) \<subseteq> dom (generatedIds S))
       \<and> knownIds S \<subseteq> dom (generatedIds S)" 
    if "prog S = progr"
    using wf that proof (induct rule: wellFormed_induct)
    case initial
    then show ?case by (auto simp add: initialState_def)
  next
    case (step S1 a S2)

    from  ` S1 ~~ a \<leadsto> S2` `prog S2 = progr`
    have [simp]: "prog S1 = progr"
      by (auto simp add: step.simps)

    have [simp]: "prog S2 = progr" using `prog S2 = progr` .

    have IH1: "\<And>i ls x. localState S1 i \<triangleq> ls \<Longrightarrow> x \<in> uids ls  \<Longrightarrow> x \<in> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    have IH2: "\<And>cId c x. calls S1 cId \<triangleq> c \<Longrightarrow> x \<in> uniqueIdsInList (call_args c) \<Longrightarrow> x \<in> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    have IH3: "x \<in> knownIds S1 \<Longrightarrow> x \<in> dom (generatedIds S1)" for  x
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    from `S1 ~~ a \<leadsto> S2`
    show ?case
    proof (induct rule: step.cases)
      case (local C s ls f ls')
      thus ?case using step.hyps cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] IH1 IH2 IH3 by (auto simp add: domExists_simp)

    next
      case (newId C s ls f ls' uid)
      thus ?case using step.hyps cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] IH1 IH2  IH3
        apply auto
        by blast+
    next
      case (beginAtomic C s ls f ls' t vis newTxns newCalls snapshot)
      thus ?case using step.hyps cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] IH1 IH2 IH3 
        by (auto simp add: domExists_simp)
    next
      case (endAtomic C s ls f ls' t)
      thus ?case using step.hyps cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] IH1 IH2 IH3 
        by (auto simp add: domExists_simp)
    next
      case (dbop C s ls f Op args ls' t c res vis)

      show ?case
      proof (auto simp add: dbop)

        have "prog C = progr"
          using \<open>prog S1 = progr\<close> dbop.hyps(1) by blast 


        show "\<exists>y. generatedIds C x \<triangleq> y"
          if c0: "x \<in> uids (ls' res)"
          for  x
        proof -
          from `x \<in> uids (ls' res)`
          have "x \<in> uids ls \<or> x \<in> uniqueIds res"
            using  cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] by (auto simp add: `f ls = DbOperation Op args ls'`)
          show "\<exists>y. generatedIds C x \<triangleq> y"
          proof (cases "x \<in> uids ls")
            assume "x \<in> uids ls"
            show "\<exists>y. generatedIds C x \<triangleq> y"
              using IH1 \<open>x \<in> uids ls\<close> dbop.hyps(1) dbop.hyps(4) by blast
          next
            assume "x \<notin> uids ls"
            hence "x \<in> uniqueIds res"
              using \<open>x \<in> uids ls \<or> x \<in> uniqueIds res\<close> by blast

            have "x \<notin> uniqueIdsInList args"
              using  cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] by (auto simp add: `f ls = DbOperation Op args ls'` \<open>x \<notin> uids ls\<close> contra_subsetD)

            obtain c cId 
              where "calls (getContext C s) cId \<triangleq> c" and "x\<in>uniqueIdsInList (call_args c)"
              using cannotGuessQ[OF `querySpec (prog C) Op args (getContext C s) res` `prog C = progr` `x \<in> uniqueIds res`]
              apply auto
              using \<open>x \<notin> uniqueIdsInList args\<close> by blast

            have "x \<in> dom (generatedIds S1)"
            proof (rule IH2)
              show "calls S1 cId \<triangleq> c"
                using `calls (getContext C s) cId \<triangleq> c`
                by (auto simp add: getContextH_def restrict_map_def dbop.hyps(1) split: option.splits if_splits)
              show "x \<in> uniqueIdsInList (call_args c)"
                using `x\<in>uniqueIdsInList (call_args c)` .
            qed

            thus "\<exists>y. generatedIds C x \<triangleq> y"
              by (auto simp add: dbop.hyps(1))
          qed
        qed


        show " \<exists>y. generatedIds C x \<triangleq> y"
          if c0: "i \<noteq> s"
            and c1: "localState C i \<triangleq> ls"
            and c2: "x \<in> uids ls"
          for  i ls x
          using IH1 c1 c2 dbop.hyps(1) by blast


        show "\<exists>y. generatedIds C x \<triangleq> y"
          if c0: "x \<in> uniqueIdsInList args"
          for  x
          sorry


        show "\<exists>y. generatedIds C x \<triangleq> y"
          if c0: "cId \<noteq> c"
            and c1: "calls C cId \<triangleq> ca"
            and c2: "x \<in> uniqueIdsInList (call_args ca)"
          for  cId ca x
          using IH2 c1 c2 dbop.hyps(1) by blast

        show "\<And>x. x \<in> knownIds C \<Longrightarrow>  \<exists>y. generatedIds C x \<triangleq> y"
          using IH3 dbop.hyps(1) by blast


      qed

    next
      case (invocation C s procName args initialState impl)
      have [simp]: "prog C = progr"
        using \<open>prog S1 = progr\<close> invocation.hyps(1) by blast


      from invocation 
      show ?case using step.hyps cannotGuessLs[OF `procedure (prog C) procName args \<triangleq> (initialState, impl)`] 
        apply (auto simp add:  step_simps)
        using cannotGuessLs' by blast

    next
      case (return C s ls f res)
      thus ?case using step.hyps cannotGuessLs2[OF `currentProc C s \<triangleq> f`, where ls=ls] IH1 IH2 IH3
        by (auto simp add: domExists_simp)
    next
      case (fail C s ls)
      thus ?case using  IH1 IH2 IH3
        by (auto simp add: domExists_simp)
    next
      case (invCheck C res s)
      thus ?case using IH1 IH2 IH3
        by (auto simp add: domExists_simp)
    qed
  qed

  thus ?thesis
    using progr_def by auto
qed


lemma wf_knownIds_subset_generatedIds2:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed (prog S)"
    and "x \<in> knownIds S"
  shows "x \<in> dom (generatedIds S)"
  using assms
  by (meson subsetCE wf_knownIds_subset_generatedIds) 


end
