theory unique_ids
  imports execution_invariants
begin



definition procedures_cannot_guess_ids :: "('localState \<Rightarrow> 'any set) \<Rightarrow> (procedureName \<Rightarrow> 'any list \<rightharpoonup> ('localState \<times> ('localState, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
"procedures_cannot_guess_ids uids proc \<equiv> 
 \<comment> \<open> procedures produce no new ids \<close>
 ( 
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
  shows "?X uids \<Longrightarrow> procedures_cannot_guess_ids uid procs"
  apply (subst procedures_cannot_guess_ids_def)
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


definition program_wellFormed :: "('localState \<Rightarrow> 'any set) \<Rightarrow> ('localState, 'any::valueType) prog \<Rightarrow> bool" where
"program_wellFormed uids progr \<equiv> 
   procedures_cannot_guess_ids uids (procedure progr)
 \<and> queries_cannot_guess_ids (querySpec progr)
"

lemma program_wellFormed_procedures_cannot_guess_ids_init:
  assumes "program_wellFormed uids progr"
    and "procedure progr p args \<triangleq> (lsInit, impl)"
  shows "uids lsInit \<subseteq> uniqueIdsInList args"
  using assms  by (auto simp add: program_wellFormed_def procedures_cannot_guess_ids_def)



lemma program_wellFormed_queries_cannot_guess_ids:
  assumes "program_wellFormed uids progr"
    and "querySpec progr opr args ctxt res"
    and "x \<in> uniqueIds res"
    and "x \<notin> uniqueIdsInList args"
  shows "\<exists>cId c. calls ctxt cId \<triangleq> c \<and> x \<in> uniqueIdsInList (call_args c)"
  using assms  apply (auto simp add: program_wellFormed_def queries_cannot_guess_ids_def)
  by blast

lemma program_wellFormed_queries_cannot_guess_ids_getContextH:
  assumes "program_wellFormed uids progr"
    and "querySpec progr opr args (getContextH S_calls hb vis) res"
    and "x \<in> uniqueIds res"
    and "x \<notin> uniqueIdsInList args"
  shows "\<exists>cId c. S_calls cId \<triangleq> c \<and> x \<in> uniqueIdsInList (call_args c)"
  using assms  apply (auto simp add: program_wellFormed_def queries_cannot_guess_ids_def getContextH_def restrict_map_def restrict_relation_def split: option.splits if_splits)
  apply fastforce
  by (smt assms(1) operationContext.select_convs(1) option.simps(3) program_wellFormed_queries_cannot_guess_ids)



lemma program_wellFormed_procedures_cannot_guess_ids_step:
  assumes "program_wellFormed uids (prog S)"
    and "currentProc S i \<triangleq> impl"
    and "state_wellFormed S"
  shows "case impl ls of
             LocalStep ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | BeginAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | EndAtomic ls' \<Rightarrow> uids ls' \<subseteq> uids ls
           | NewId f \<Rightarrow> (\<forall>uid ls'. f uid \<triangleq> ls' \<longrightarrow> uids ls' \<subseteq> uids ls \<union> {uid})
           | DbOperation opr args f \<Rightarrow> 
                     uniqueIdsInList args \<subseteq> uids ls
                   \<and> (\<forall>res. uids (f res) \<subseteq> uids ls \<union> uniqueIds res)
           | Return r => uniqueIds r \<subseteq> uids ls"
proof -
  obtain p args lsInit where "procedure (prog S) p args \<triangleq> (lsInit, impl)"
    using exists_implementation[OF \<open>state_wellFormed S\<close> \<open>currentProc S i \<triangleq> impl\<close>] by blast
  with \<open>program_wellFormed uids (prog S)\<close>
  show ?thesis
    by (auto simp add: program_wellFormed_def procedures_cannot_guess_ids_def)
qed

lemma program_wellFormed_procedures_cannot_guess_ids_LocalStep:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = LocalStep ls'"
  shows "x \<in> uids ls' \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto

lemma program_wellFormed_procedures_cannot_guess_ids_BeginAtomic:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = BeginAtomic ls'"
  shows "x \<in> uids ls' \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto

lemma program_wellFormed_procedures_cannot_guess_ids_EndAtomic:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = EndAtomic ls'"
  shows "x \<in> uids ls' \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto

lemma program_wellFormed_procedures_cannot_guess_ids_NewId:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = NewId f"
    and f: "f uid \<triangleq> ls'"
  shows "x \<in> uids ls' \<Longrightarrow> x \<noteq> uid \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf f by auto

lemma program_wellFormed_procedures_cannot_guess_ids_DbOperation:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = DbOperation opr args f"
  shows "x \<in> uids (f res) \<Longrightarrow> x \<notin> uniqueIds res \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto

lemma program_wellFormed_procedures_cannot_guess_ids_DbOperation2:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = DbOperation opr args f"
  shows "x \<in> uniqueIdsInList args \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto

lemma program_wellFormed_procedures_cannot_guess_ids_Return:
  assumes wf: "program_wellFormed uids (prog S)"
    and proc: "currentProc S i \<triangleq> impl"
    and S_wf: "state_wellFormed S"
    and impl: "impl ls = Return r"
  shows "x \<in> uniqueIds r \<Longrightarrow> x \<in> uids ls"
  using program_wellFormed_procedures_cannot_guess_ids_step[OF wf proc, where ls=ls] impl S_wf by auto


lemma domExists_simp: "x \<in> dom f \<longleftrightarrow> (\<exists>y. f x \<triangleq> y)"
  by (auto)

lemma wf_knownIds_subset_generatedIds:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
  shows "knownIds S \<subseteq> dom (generatedIds S)"
proof -

  define progr where "progr \<equiv> prog S"

  from prog_wf
  have "procedures_cannot_guess_ids uids (procedure progr)"
   and "queries_cannot_guess_ids (querySpec progr)"
    using progr_def program_wellFormed_def by auto


  from \<open>procedures_cannot_guess_ids uids (procedure progr)\<close>
  have cannotGuessLs: 
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
     using that by (auto simp add: procedures_cannot_guess_ids_def)




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
           " if "currentProc S i \<triangleq> impl" "state_wellFormed S" "progr = prog S "
          for S :: "('localState, 'any::valueType) state" and i impl ls
  proof -
    obtain p args lsInit where  "procedure progr p args \<triangleq> (lsInit, impl)"
      using exists_implementation[OF \<open>state_wellFormed S\<close> \<open>currentProc S i \<triangleq> impl\<close> \<open>progr = prog S\<close>]
      by auto

    then show ?thesis
      by (rule cannotGuessLs, simp)
  qed

  from \<open>queries_cannot_guess_ids (querySpec progr)\<close>
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

    from  \<open> S1 ~~ a \<leadsto> S2\<close> \<open>prog S2 = progr\<close>
    have [simp]: "prog S1 = progr"
      by (auto simp add: step.simps)

    have [simp]: "prog S2 = progr" using \<open>prog S2 = progr\<close> .

    have IH1: "\<And>i ls x. localState S1 i \<triangleq> ls \<Longrightarrow> x \<in> uids ls  \<Longrightarrow> x \<in> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    have IH2: "\<And>cId c x. calls S1 cId \<triangleq> c \<Longrightarrow> x \<in> uniqueIdsInList (call_args c) \<Longrightarrow> x \<in> dom (generatedIds S1)"
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    have IH3: "x \<in> knownIds S1 \<Longrightarrow> x \<in> dom (generatedIds S1)" for  x
      using \<open>prog S1 = progr\<close> step.hyps(2) by blast

    have "state_wellFormed S1"
      by (simp add: step.hyps(1))


    have "state_wellFormed S2"
      using state_wellFormed_combine_step step.hyps(1) step.hyps(3) step.hyps(4) by blast

    have "prog S1 = progr"
      by simp


    from \<open>S1 ~~ a \<leadsto> S2\<close>
    show ?case
    proof (induct rule: step.cases)
      case (local C s ls f ls')
      then show ?case using step.hyps cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] IH1 IH2 IH3 \<open>state_wellFormed S1\<close> \<open>prog S1 = progr\<close> by (auto simp add: domExists_simp)

    next
      case (newId C s ls f ls' uid)
      then show ?case using step.hyps cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] IH1 IH2  IH3 \<open>state_wellFormed S1\<close> \<open>prog S1 = progr\<close>
        apply auto
        by blast+
    next
      case (beginAtomic C s ls f ls' t vis snapshot)
      then show ?case using step.hyps cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] IH1 IH2 IH3  \<open>state_wellFormed S1\<close> \<open>prog S1 = progr\<close>
        by (auto simp add: domExists_simp)
    next
      case (endAtomic C s ls f ls' t)
      then show ?case using step.hyps cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] IH1 IH2 IH3  \<open>state_wellFormed S1\<close> \<open>prog S1 = progr\<close>
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
          from \<open>x \<in> uids (ls' res)\<close>
          have "x \<in> uids ls \<or> x \<in> uniqueIds res"
            using  cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] \<open>state_wellFormed S1\<close> \<open>prog C = progr\<close> \<open>S1 = C\<close> by (auto simp add: \<open>f ls = DbOperation Op args ls'\<close>)

          show "\<exists>y. generatedIds C x \<triangleq> y"
          proof (cases "x \<in> uids ls")
            assume "x \<in> uids ls"
            show "\<exists>y. generatedIds C x \<triangleq> y"
              using IH1 \<open>x \<in> uids ls\<close> dbop.hyps(1) dbop.hyps(4) by blast
          next
            assume "x \<notin> uids ls"
            then have "x \<in> uniqueIds res"
              using \<open>x \<in> uids ls \<or> x \<in> uniqueIds res\<close> by blast

            have "x \<notin> uniqueIdsInList args"
              using  cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls]  \<open>state_wellFormed S1\<close> \<open>prog S1 = progr\<close> \<open>prog C = progr\<close> \<open>S1 = C\<close> by (auto simp add: \<open>f ls = DbOperation Op args ls'\<close> \<open>x \<notin> uids ls\<close> contra_subsetD)

            obtain c cId 
              where "calls (getContext C s) cId \<triangleq> c" and "x\<in>uniqueIdsInList (call_args c)"
              using cannotGuessQ[OF \<open>querySpec (prog C) Op args (getContext C s) res\<close> \<open>prog C = progr\<close> \<open>x \<in> uniqueIds res\<close>]
              apply auto
              using \<open>x \<notin> uniqueIdsInList args\<close> by blast

            have "x \<in> dom (generatedIds S1)"
            proof (rule IH2)
              show "calls S1 cId \<triangleq> c"
                using \<open>calls (getContext C s) cId \<triangleq> c\<close>
                by (auto simp add: getContextH_def restrict_map_def dbop.hyps(1) split: option.splits if_splits)
              show "x \<in> uniqueIdsInList (call_args c)"
                using \<open>x\<in>uniqueIdsInList (call_args c)\<close> .
            qed

            then show "\<exists>y. generatedIds C x \<triangleq> y"
              by (auto simp add: dbop.hyps(1))
          qed
        qed


        show " \<exists>y. generatedIds C x \<triangleq> y"
          if c0: "i \<noteq> s"
            and c1: "localState C i \<triangleq> ls"
            and c2: "x \<in> uids ls"
          for  i ls x
          using IH1 c1 c2 dbop.hyps(1) by blast


        from \<open> currentProc C s \<triangleq> f\<close>
        obtain p pargs lsInit where "procedure progr p pargs \<triangleq> (lsInit, f)"
          using \<open>prog C = progr\<close> dbop.hyps(1) exists_implementation step.hyps(1) by blast



        show "\<exists>y. generatedIds C x \<triangleq> y"
          if c0: "x \<in> uniqueIdsInList args"
          for  x
        proof -
          from \<open>procedures_cannot_guess_ids uids (procedure progr)\<close> 
            and \<open>f ls = DbOperation Op args ls'\<close> and c0
            and \<open>procedure progr p pargs \<triangleq> (lsInit, f)\<close>
          have "x \<in> uids ls"
            apply (auto simp add: procedures_cannot_guess_ids_def)
            apply ((drule spec)+, drule(1) mp)
            apply auto
            apply (drule_tac x=ls in spec)
            apply auto
            done

          then show "\<exists>y. generatedIds C x \<triangleq> y"
            using IH1 dbop.hyps(1) dbop.hyps(4) by blast
        qed


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
      case (invocId C s procName args initialState impl)
      have [simp]: "prog C = progr"
        using \<open>prog S1 = progr\<close> invocId.hyps(1) by blast


      from invocId 
      show ?case using step.hyps cannotGuessLs[OF \<open>procedure (prog C) procName args \<triangleq> (initialState, impl)\<close>] 
        apply (auto simp add:  step_simps)
        using cannotGuessLs' by blast

    next
      case (return C s ls f res)
      then show ?case using step.hyps cannotGuessLs2[OF \<open>currentProc C s \<triangleq> f\<close>, where ls=ls] IH1 IH2 IH3  \<open>prog S1 = progr\<close>
        by (auto simp add: domExists_simp)

    next
      case (fail C s ls)
      then show ?case using  IH1 IH2 IH3
        by (auto simp add: domExists_simp)
    next
      case (invCheck C res s)
      then show ?case using IH1 IH2 IH3
        by (auto simp add: domExists_simp)
    qed
  qed

  then show ?thesis
    using progr_def by auto
qed


lemma wf_knownIds_subset_generatedIds2:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
    and "x \<in> knownIds S"
  shows "x \<in> dom (generatedIds S)"
  using assms
  by (meson subsetCE wf_knownIds_subset_generatedIds) 


lemma steps_private_uniqueIds_h:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and uid_generated: "generatedIds S uid \<triangleq> i"
    and not_known: "uid \<notin> knownIds S"
    and not_in_db: "\<forall>c opr args r. calls S c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
    and wf: "state_wellFormed S"
    and nofail: "(\<forall>i. (i, AFail) \<notin> set tr)"
    and no_step_in_i: "(\<forall>a. (i, a) \<notin> set tr)"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_in_ls: "\<forall>i' ls. i'\<noteq>i \<longrightarrow> localState S i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
  shows "uid \<notin> knownIds S' 
     \<and> (\<forall>i' ls. localState S' i' \<triangleq> ls \<longrightarrow> i'\<noteq>i \<longrightarrow> uid \<notin> uids ls)
     \<and> (\<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"

  using \<open>S ~~ tr \<leadsto>* S'\<close> nofail no_step_in_i proof (induct rule: steps_induct)
  case initial
  then show ?case
    using not_in_db not_in_ls not_known by blast

next
  case (step S' tr a S'')

  have "program_wellFormed uids (prog S')"
    using prog_wf step.steps steps_do_not_change_prog by fastforce


  have "state_wellFormed S'"
    using local.wf state_wellFormed_combine \<open>\<forall>i. (i, AFail) \<notin> set (tr @ [a])\<close> step.steps by fastforce

  from step.IH 
  have IH1: "uid \<notin> knownIds S'"
    and IH2: "\<And>i' ls. localState S' i' \<triangleq> ls \<Longrightarrow> i' \<noteq> i \<Longrightarrow> uid \<notin> uids ls"
    and IH3: "\<And>c opr args r. calls S' c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
    using step.prems by force+


  from \<open>S' ~~ a \<leadsto> S''\<close>
  show "uid \<notin> knownIds S'' \<and> (\<forall>i' ls. localState S'' i' \<triangleq> ls \<longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> uids ls) \<and> (\<forall>c opr args r. calls S'' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"
  proof (induct rule: step.cases)
    case (local C s ls f ls')
    then show ?case 
    proof (intro conjI)
      show "uid \<notin> knownIds S''" using IH1 local by auto
      show "\<forall>c opr args r. calls S'' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
        using IH3 local by auto

      show " \<forall>i' ls. localState S'' i' \<triangleq> ls \<longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> uids ls"
        using IH2 local apply auto
        using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S'\<close> program_wellFormed_procedures_cannot_guess_ids_LocalStep by fastforce
    qed

  next
    case (newId C s ls f ls' nuid ls'')

    have "currentProc S' s \<triangleq> f"
      by (simp add: newId.hyps)

    have "s \<noteq> i"
      using newId.hyps(2) step.prems(2) by auto

    
    show ?case
    proof (intro conjI)
      show "uid \<notin> knownIds S''" using IH1 newId by auto
      show "\<forall>c opr args r. calls S'' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
        using IH3 newId by auto

      show " \<forall>i' ls. localState S'' i' \<triangleq> ls \<longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> uids ls"
        using IH2 newId 
          program_wellFormed_procedures_cannot_guess_ids_NewId[OF \<open>program_wellFormed uids (prog S')\<close> \<open>currentProc S' s \<triangleq> f\<close> \<open>state_wellFormed S'\<close> \<open> f ls = NewId ls'\<close> \<open>ls' nuid \<triangleq> ls''\<close>] apply auto
        using generatedIds_mono1 step.steps uid_generated by fastforce
    qed
  next
    case (beginAtomic C s ls f ls' t vis snapshot)
    then show ?case
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S'\<close> program_wellFormed_procedures_cannot_guess_ids_BeginAtomic by fastforce


  next
    case (endAtomic C s ls f ls' t)
    then show ?case 
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S'\<close> program_wellFormed_procedures_cannot_guess_ids_EndAtomic by fastforce
  next
    case (dbop C s ls f Op args ls' t c res vis)

    have "program_wellFormed uids (prog C)"
      using \<open>program_wellFormed uids (prog S')\<close> dbop.hyps(1) by auto

    have "state_wellFormed C"
      using \<open>state_wellFormed S'\<close> dbop.hyps(1) by auto

    have [simp]: "uid \<notin> uniqueIdsInList args"
      by (metis IH2 \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S'\<close> append_is_Nil_conv dbop.hyps(1) dbop.hyps(2) dbop.hyps(4) dbop.hyps(5) dbop.hyps(6) last_in_set last_snoc list.simps(3) program_wellFormed_procedures_cannot_guess_ids_DbOperation2 step.prems(2))


    from dbop
    show ?case 
      using IH1 IH2 IH3 apply auto
      by (metis (no_types, lifting) \<open>program_wellFormed uids (prog C)\<close> \<open>state_wellFormed C\<close> \<open>uid \<notin> uniqueIdsInList args\<close> call.collapse program_wellFormed_procedures_cannot_guess_ids_DbOperation program_wellFormed_queries_cannot_guess_ids_getContextH)
  next
    case (invocId C s procName args initialState impl)
    then show ?case 
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> program_wellFormed_procedures_cannot_guess_ids_init by fastforce

  next
    case (return C s ls f res)
    then show ?case using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S'\<close> program_wellFormed_procedures_cannot_guess_ids_Return step.prems(2) by fastforce
  next
    case (fail C s ls)
    then show ?case
      using step.prems(1) by auto 

  next
    case (invCheck C res s)
    then show ?case
      using IH1 IH2 IH3 by auto 

  qed
qed


lemma steps_private_knownIds:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and uid_generated: "generatedIds S uid \<triangleq> i"
    and not_known: "uid \<notin> knownIds S"
    and not_in_db: "\<forall>c opr args r. calls S c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
    and wf: "state_wellFormed S"
    and nofail: "(\<forall>i. (i, AFail) \<notin> set tr)"
    and no_step_in_i: "(\<forall>a. (i, a) \<notin> set tr)"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_in_ls: "\<forall>i' ls. i'\<noteq>i \<longrightarrow> localState S i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
  shows "uid \<notin> knownIds S'"
using steps_private_uniqueIds_h[OF assms] by simp

lemma steps_private_localIds:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and uid_generated: "generatedIds S uid \<triangleq> i"
    and not_known: "uid \<notin> knownIds S"
    and not_in_db: "\<forall>c opr args r. calls S c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
    and wf: "state_wellFormed S"
    and nofail: "(\<forall>i. (i, AFail) \<notin> set tr)"
    and no_step_in_i: "(\<forall>a. (i, a) \<notin> set tr)"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_in_ls: "\<forall>i' ls. i'\<noteq>i \<longrightarrow> localState S i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
  shows "localState S' i' \<triangleq> ls \<Longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> uids ls"
using steps_private_uniqueIds_h[OF assms] by simp

lemma steps_private_callIds:
  assumes steps: "S ~~ tr \<leadsto>* S'"
    and uid_generated: "generatedIds S uid \<triangleq> i"
    and not_known: "uid \<notin> knownIds S"
    and not_in_db: "\<forall>c opr args r. calls S c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
    and wf: "state_wellFormed S"
    and nofail: "(\<forall>i. (i, AFail) \<notin> set tr)"
    and no_step_in_i: "(\<forall>a. (i, a) \<notin> set tr)"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_in_ls: "\<forall>i' ls. i'\<noteq>i \<longrightarrow> localState S i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
  shows " calls S' c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
  using steps_private_uniqueIds_h[OF assms] by blast 


lemma wf_onlyGeneratedIdsAreUsed:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "uid \<notin> knownIds S \<and> (\<forall>i ls. localState S i \<triangleq> ls \<longrightarrow> uid \<notin> uids ls) \<and> (\<forall>c opr args r. calls S c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"
 using assms proof (induct rule: wellFormed_induct)
  case initial
  then show ?case 
    by (auto simp add: initialState_def)
next
  case (step S a S')

  have " S ~~ [a] \<leadsto>* S'"
    by (simp add: step.hyps(3) steps_single)


  have not_generated_S: "generatedIds S uid = None"
    using generatedIds_mono1[OF \<open>S ~~ [a] \<leadsto>* S'\<close>] \<open>generatedIds S' uid = None\<close>
    by (meson domExists_simp domIff)

  have progr_wf_S: "program_wellFormed uids (prog S)"
    using \<open>S ~~ [a] \<leadsto>* S'\<close> step.prems(1) steps_do_not_change_prog by fastforce

  have IH1: "uid \<notin> knownIds S"
    using not_generated_S progr_wf_S step.hyps(2) by blast

  have IH2: "\<And>i ls. localState S i \<triangleq> ls \<Longrightarrow> uid \<notin> uids ls" 
    using not_generated_S progr_wf_S step.hyps(2) by blast
  have IH3: "\<And>c opr args r. calls S c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
    using not_generated_S progr_wf_S step.hyps(2) by blast

  from \<open>S ~~ a \<leadsto> S'\<close>
  show "uid \<notin> knownIds S' \<and> (\<forall>i ls. localState S' i \<triangleq> ls \<longrightarrow> uid \<notin> uids ls) \<and> (\<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"
  proof (induct rule: step.cases)
    case (local C s ls f ls')
    then show ?case 
    proof (intro conjI)
      show "uid \<notin> knownIds S'" using IH1 local by auto
      show "\<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
        using IH3 local by auto

      show " \<forall>i' ls. localState S' i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
        using IH2 local apply auto
        using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S\<close> program_wellFormed_procedures_cannot_guess_ids_LocalStep by fastforce
    qed

  next
    case (newId C s ls f ls' nuid ls'')

    have "currentProc S s \<triangleq> f"
      by (simp add: newId.hyps)

    have "uid \<notin> uids ls"
      using IH2 newId.hyps(1) newId.hyps(4) by blast


    
    show ?case
    proof (intro conjI)
      show "uid \<notin> knownIds S'" using IH1 newId by auto
      show "\<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
        using IH3 newId by auto

      show " \<forall>i' ls. localState S' i' \<triangleq> ls \<longrightarrow> uid \<notin> uids ls"
        using IH2 newId \<open>generatedIds S' uid = None\<close> 
          program_wellFormed_procedures_cannot_guess_ids_NewId[OF \<open>program_wellFormed uids (prog S)\<close> \<open>currentProc S s \<triangleq> f\<close> \<open>state_wellFormed S\<close> \<open> f ls = NewId ls'\<close> \<open>ls' nuid \<triangleq> ls''\<close>, where x=uid] by (auto split: if_splits)
    qed
  next
    case (beginAtomic C s ls f ls' t vis snapshot)
    then show ?case
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S)\<close> \<open>state_wellFormed S\<close> program_wellFormed_procedures_cannot_guess_ids_BeginAtomic by fastforce


  next
    case (endAtomic C s ls f ls' t)
    then show ?case 
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S)\<close> \<open>state_wellFormed S\<close> program_wellFormed_procedures_cannot_guess_ids_EndAtomic by fastforce
  next
    case (dbop C s ls f Op args ls' t c res vis)

    have "program_wellFormed uids (prog C)"
      using \<open>program_wellFormed uids (prog S)\<close> dbop.hyps(1) by auto

    have "state_wellFormed C"
      using \<open>state_wellFormed S\<close> dbop.hyps(1) by auto

    have [simp]: "uid \<notin> uniqueIdsInList args"
      using IH2 \<open>program_wellFormed uids (prog C)\<close> \<open>state_wellFormed C\<close> dbop.hyps(1) dbop.hyps(4) dbop.hyps(5) dbop.hyps(6) program_wellFormed_procedures_cannot_guess_ids_DbOperation2 by fastforce


    from dbop
    show ?case 
      using IH1 IH2 IH3 apply auto
      by (metis (no_types, lifting) \<open>program_wellFormed uids (prog C)\<close> \<open>state_wellFormed C\<close> \<open>uid \<notin> uniqueIdsInList args\<close> call.collapse program_wellFormed_procedures_cannot_guess_ids_DbOperation program_wellFormed_queries_cannot_guess_ids_getContextH)
  next
    case (invocId C s procName args initialState impl)
    then show ?case 
      using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> program_wellFormed_procedures_cannot_guess_ids_init by fastforce

  next
    case (return C s ls f res)
    then show ?case using IH1 IH2 IH3 apply auto
      using \<open>program_wellFormed uids (prog S')\<close> \<open>state_wellFormed S\<close> program_wellFormed_procedures_cannot_guess_ids_Return step.prems(2) by fastforce
  next
    case (fail C s ls)
    then show ?case
      using step.hyps(4) by auto
      

  next
    case (invCheck C res s)
    then show ?case
      using IH1 IH2 IH3 by auto 

  qed
qed

lemma wf_onlyGeneratedIdsInKnownIds:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "uid \<notin> knownIds S"
  using local.wf not_generated prog_wf wf_onlyGeneratedIdsAreUsed by blast


lemma wf_onlyGeneratedIdsInLocalState:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "localState S i \<triangleq> ls \<Longrightarrow> uid \<notin> uids ls"
  using local.wf not_generated prog_wf wf_onlyGeneratedIdsAreUsed by blast


lemma wf_onlyGeneratedIdsInCalls:
  fixes S :: "('localState, 'any::valueType) state"
  assumes wf: "state_wellFormed S"
    and prog_wf: "program_wellFormed uids (prog S)"
    and not_generated: "generatedIds S uid = None"
  shows "calls S c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
  using local.wf not_generated prog_wf wf_onlyGeneratedIdsAreUsed by blast





end
