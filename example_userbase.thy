section "Example: User Database"
theory example_userbase
  imports 
    program_verification_tactics
    impl_language_loops
    crdt_specs2
    unique_ids
    program_proof_rules_loops
    app_verification_helpers
    unique_ids_loops
    proof_state_facts
begin



datatype val =
  String string
  | UserId int
  | Bool bool
  | Undef
  | Found string string
  | NotFound


instance val :: countable
  by countable_datatype

instantiation val :: valueType begin

definition uniqueIds_val where
  "uniqueIds_val x \<equiv> case x of UserId u \<Rightarrow> {to_nat (UserId u)} | _ \<Rightarrow> {}"

definition [simp]: "default_val \<equiv> Undef"

lemma uniqueIds_simp[simp]:
  shows "uniqueIds (String x) = {}"
    "uniqueIds (Bool b) = {}"
    "uniqueIds Undef = {}"
    "uniqueIds (Found x y) = {}"
    "uniqueIds NotFound = {}"
  by (auto simp add: uniqueIds_val_def)

instance by (standard, auto)
end

instantiation val :: from_bool begin
definition [simp]: "from_bool_val \<equiv> Bool"

instance by (standard, auto)
end


definition "isUserId x \<equiv> case x of UserId _ \<Rightarrow> True | _ \<Rightarrow> False"

lemma "uniqueIds (Bool True) = {}"
  by (simp add: uniqueIds_val_def)


fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"

datatype userDataOp =
  Name "val registerOp"
  | Mail "val registerOp"


instance userDataOp :: countable
  by countable_datatype
instantiation userDataOp :: crdt_op begin
definition "uniqueIds_userDataOp x \<equiv> 
  case x of 
     Name x \<Rightarrow> uniqueIds x
   | Mail x \<Rightarrow> uniqueIds x"

lemma [simp]: "uniqueIds (Name x) = uniqueIds x"
  "uniqueIds (Mail x) = uniqueIds x"
  by (auto simp add: uniqueIds_userDataOp_def)

definition [simp]: "default_userDataOp = Mail default"

definition "is_update_userDataOp x \<equiv> case x of Name x \<Rightarrow> is_update x | Mail x \<Rightarrow> is_update x"

instance by (standard, auto)
end

type_synonym operation = 
  "(val, userDataOp) mapOp"



definition registerUser_impl :: "val \<Rightarrow> val \<Rightarrow> (val,operation,val) io" where
  "registerUser_impl name mail \<equiv>  do {
  u \<leftarrow> newId isUserId;
  atomic (do {
    call (NestedOp u (Name (Assign name)));
    call (NestedOp u (Mail (Assign mail)))
  });
  return u
}"


definition updateMail_impl :: "val \<Rightarrow> val \<Rightarrow> (val,operation,val) io" where
  "updateMail_impl u mail \<equiv>  do {
  atomic (do {
  exists \<leftarrow> call (KeyExists u);  
    (if exists = Bool True then do {
      call (NestedOp u (Mail (Assign mail)))
    } else skip)
  });
  return Undef
}"


definition removeUser_impl :: "val \<Rightarrow> (val,operation,val) io" where
  "removeUser_impl u \<equiv>  do {
  atomic (do {
      call (DeleteKey u)
  });
  return Undef
}"

definition getUser_impl :: "val \<Rightarrow> (val,operation,val) io" where
  "getUser_impl u \<equiv>  do {
  atomic (do {
    exists \<leftarrow> call (KeyExists u);  
    (if exists = Bool True then do {
      name \<leftarrow> call (NestedOp u (Name Read));
      mail \<leftarrow> call (NestedOp u (Mail Read));
      return (Found (stringval name) (stringval mail))
    } else return NotFound)
  })
}"




datatype proc =
  RegisterUser string string
  | UpdateMail int string
  | RemoveUser int
  | GetUser int

instance proc :: countable
  by countable_datatype

instantiation proc :: valueType begin
definition "uniqueIds_proc proc \<equiv> 
  case proc of 
     UpdateMail u _ \<Rightarrow> uniqueIds (UserId u)
   | RemoveUser u  \<Rightarrow> uniqueIds (UserId u)
   | GetUser u  \<Rightarrow> uniqueIds (UserId u)
   | RegisterUser _ _ \<Rightarrow> {}"

lemma [simp]:
  "uniqueIds (UpdateMail u x) = uniqueIds (UserId u)"
  "uniqueIds (RemoveUser u ) = uniqueIds (UserId u)"
  "uniqueIds (GetUser u ) = uniqueIds (UserId u)"
  "uniqueIds (RegisterUser x y) = {}"
  by (auto simp add: uniqueIds_proc_def)

definition [simp]: "default_proc \<equiv> RegisterUser [] []"

instance by (standard, auto)
end


type_synonym localState = "val store  \<times> uniqueId set \<times> (val, operation, val) io"

definition procedures :: "proc \<Rightarrow> (localState \<times> (localState, operation, val) procedureImpl)" where
  "procedures invoc \<equiv>
  case invoc of
    RegisterUser name mail \<Rightarrow> toImpl' invoc (registerUser_impl (String name) (String mail))
  | UpdateMail u mail \<Rightarrow> toImpl' invoc (updateMail_impl (UserId u) (String mail))
  | RemoveUser u \<Rightarrow>  toImpl' invoc (removeUser_impl (UserId u))
  | GetUser u  \<Rightarrow>  toImpl' invoc (getUser_impl (UserId u))
"

definition inv1  where
  "inv1 op res ihb \<equiv> \<forall>r g u g_res.
    op r \<triangleq> RemoveUser u
  \<longrightarrow> op g \<triangleq> GetUser u
  \<longrightarrow> (r,g) \<in> ihb
  \<longrightarrow> res g \<triangleq> g_res
  \<longrightarrow> g_res = NotFound"

definition inv2  where
  "inv2 op i_origin c_calls \<equiv> \<forall>u i c.
    op i \<triangleq> RemoveUser u
  \<longrightarrow> i_origin c \<triangleq> i
  \<longrightarrow> (c_calls c \<triangleq> Call (DeleteKey (UserId u)) Undef)"

definition inv3  where
  "inv3 c_calls hb \<equiv> \<not>(\<exists>write delete u upd.
    (\<exists>write_r. c_calls write \<triangleq> Call (NestedOp u upd) write_r)
  \<and> is_update upd
  \<and> (\<exists>delete_r. c_calls delete \<triangleq> Call (DeleteKey u) delete_r)
  \<and> (delete, write) \<in> hb
  )"

definition inv :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> 
    inv1 (invocationOp ctxt) (invocationRes ctxt) (invocation_happensBefore ctxt) 
  \<and> inv2 (invocationOp ctxt) (i_callOriginI ctxt) (calls ctxt)
  \<and> inv3 (calls ctxt) (happensBefore ctxt)"

lemma show_inv[intro, case_names inv1 inv2 inv3]:
  assumes "inv1 (invocationOp ctxt) (invocationRes ctxt) (invocation_happensBefore ctxt)" 
    and "inv2 (invocationOp ctxt) (i_callOriginI ctxt) (calls ctxt)" 
    and "inv3 (calls ctxt) (happensBefore ctxt)"
  shows "inv ctxt"
  using assms  by (auto simp add: inv_def)

lemma use_inv3:
  assumes "inv3 c_calls hb"
and "c_calls write \<triangleq> Call (NestedOp u upd) write_r"
and "is_update upd"
and "c_calls delete \<triangleq> Call (DeleteKey u) delete_r"
and "(delete, write) \<in> hb"
shows P
  by (meson assms inv3_def)

lemma use_inv3':
  assumes "inv3 c_calls hb"
and "c_calls write \<triangleq> Call (NestedOp u upd) write_r"
and "is_update upd"
and "c_calls delete \<triangleq> Call (DeleteKey u) delete_r"
shows "(delete, write) \<notin> hb"
  by (meson assms inv3_def)

definition userStruct :: "(userDataOp, val) crdtSpec" where
  "userStruct \<equiv> (\<lambda>oper.
  case oper of
    Name op \<Rightarrow> struct_field Name (register_spec Undef op) 
  | Mail op \<Rightarrow> struct_field Mail (register_spec Undef op)
)" 

definition crdtSpec :: "(operation, val) crdtSpec" where
  "crdtSpec \<equiv> map_sdw_spec userStruct"


definition userStruct' :: "('a, userDataOp, val) ccrdtSpec" where
"userStruct' \<equiv> (\<lambda>oper.
  case oper of
    Name op \<Rightarrow> struct_field' Name (register_spec' Undef op) 
  | Mail op \<Rightarrow> struct_field' Mail (register_spec' Undef op) 
)"

definition crdtSpec' :: "(operation, operation, val) ccrdtSpec" where
  "crdtSpec' \<equiv> map_sdw_spec' userStruct'"

lemma crdtSpec_rel:
  shows "crdt_spec_rel crdtSpec crdtSpec'"
  unfolding crdtSpec_def crdtSpec'_def
proof (rule map_sdw_spec_rel)

  show "crdt_spec_rel userStruct userStruct'"
  proof (rule show_crdt_spec_rel')


    show "userStruct op (sub_context C_in Cs ctxt) r = userStruct' op Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
      if c0: "is_reverse C_in C_out"
        and c1: "operationContext_wf ctxt"
        and c2: "C_in outer_op \<triangleq> op"
        and c3: "Cs \<subseteq> dom (map_map (calls ctxt) call_operation \<ggreater> C_in)"
      for  C_in C_out ctxt outer_op op r Cs
      unfolding userStruct_def userStruct'_def
    proof (cases op; clarsimp)
      case (Name x1)
      show "struct_field Name (register_spec Undef x1) (sub_context C_in Cs ctxt) r =
          struct_field' Name (register_spec' Undef x1) Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
      proof (rule struct_field_eq)
        show "crdt_spec_rel (register_spec Undef) (register_spec' Undef)"
          by (simp add: register_spec_rel)
        show "inj Name"
          using inj_def by auto
        show "is_reverse C_in C_out"
          by (simp add: c0)
        show "Cs \<subseteq> dom (calls ctxt)"
          by (smt c3 domI dom_map_map in_dom map_chain_eq_some subsetI)
        show "operationContext_wf ctxt"
          by (simp add: c1)
      qed

    next
      case (Mail x2)
      show "struct_field Mail (register_spec Undef x2) (sub_context C_in Cs ctxt) r =
          struct_field' Mail (register_spec' Undef x2) Cs (extract_op (calls ctxt)) (happensBefore ctxt) C_out r"
      proof (rule struct_field_eq)
        show "crdt_spec_rel (register_spec Undef) (register_spec' Undef)"
          by (simp add: register_spec_rel)
        show "inj Mail"
          using inj_def by auto
        show "is_reverse C_in C_out"
          by (simp add: c0)
        show "Cs \<subseteq> dom (calls ctxt)"
          by (smt c3 domI dom_map_map in_dom map_chain_eq_some subsetI)
        show "operationContext_wf ctxt"
          by (simp add: c1)
      qed
    qed
  qed
qed



definition progr :: "(proc, localState, operation, val) prog" where
  "progr \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"

lemma procedure_progr[simp]: "procedure progr = procedures"
  by (simp add: progr_def)

lemma querySpec_progr[simp]: "querySpec progr = crdtSpec"
  by (simp add: progr_def)






lemma progr_wf[simp]: "program_wellFormed progr"
proof (auto simp add: program_wellFormed_def)
  show "invocations_cannot_guess_ids progr"
  proof (rule invocations_cannot_guess_ids_io)

    show "impl = impl_language_loops.toImpl \<and> localKnown = uniqueIds proc"
      if c0: "procedure progr proc = ((store, localKnown, cmd), impl)"
      for  proc store localKnown cmd impl
      using that
      by (auto simp add: progr_def procedures_def split: proc.splits)
  qed

  show "queries_cannot_guess_ids crdtSpec"
  proof (simp add:  crdtSpec_def, standard)
    show "queries_cannot_guess_ids userStruct"
    proof (auto simp add: userStruct_def queries_cannot_guess_ids_def split: userDataOp.splits)

      show "query_cannot_guess_ids (uniqueIds s) (struct_field Name (register_spec Undef s) )" for s
        by (standard, auto split: userDataOp.splits)


      show "query_cannot_guess_ids (uniqueIds s) (struct_field Mail (register_spec Undef s) )" for s 
        by (standard, auto split: userDataOp.splits)
    qed

  qed 
qed





lemma isUserId_infinite[simp]: "infinite (Collect isUserId)"
proof (rule infinite_if_mappable_to_nat)
  show "\<exists>x\<in>Collect isUserId. n \<le> (case x of UserId n \<Rightarrow> nat n)" for n
    by (rule bexI[where x="UserId (int n)"],
        auto simp add: isUserId_def)
qed



lemma invariant_progr[simp]: "invariant progr = example_userbase.inv"
  by (auto simp add: progr_def)

lemma if_distrib_eq: "(if c then x else y) = z \<longleftrightarrow> (if c then x = z else y = z)"
  by (rule if_distrib)

declare invariantContext.defs[simp]

lemmas crdt_spec_defs = 
  toplevel_spec_def crdtSpec'_def struct_field'_def map_sdw_spec'_def map_spec'_def userStruct'_def register_spec'_def
  set_rw_spec'_def deleted_calls_sdw'_def


theorem userbase_correct: "programCorrect progr"
proof M_show_programCorrect

  case invariant_initial_state
  show "invariant_all' (initialState progr)"
    by (simp add: example_userbase.inv_def initialState_def inv1_def inv2_def inv3_def invContextH2_happensBefore invContextH2_i_invocationOp progr_def)

  case (procedure_correct S i)



  show "procedureCorrect S i"
  proof (rule Initial_Label, rule show_initial_state_prop[OF procedure_correct], rule DC_final2, casify)
    case (show_P S_pre proc initState impl)
    have "invocationOp S i \<triangleq> proc"
      using show_P by auto
    have "invocationRes S i = None"
      using show_P apply auto
      using state_wellFormed_invocation_before_result by blast

    have "uniqueIds proc \<subseteq> knownIds S"
      using show_P by auto


    note show_P[simp]

    show "procedureCorrect S i"
    proof (cases proc)
      case (RegisterUser name mail)

      show "procedureCorrect S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre RegisterUser
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)

      next
        case execution
        show "execution_s_correct S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound4)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: RegisterUser procedures_def )

          show "localState S i \<triangleq> (Map.empty, uniqueIds (RegisterUser name mail), registerUser_impl (String name) (String mail))"
            by (auto simp add: RegisterUser procedures_def )

          note registerUser_impl_def[simp]

          show "invocationOp S i \<triangleq> RegisterUser name mail"
            using RegisterUser \<open>invocationOp S i \<triangleq> proc\<close> by blast


          show "program_wellFormed (prog S)"
            by (simp add: initialStates_reachable_from_initialState procedure_correct.in_initial_state)

          show "invariant_all' S"
            using execution.in_initial_state by blast

          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 



          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> RegisterUser name mail), invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (RegisterUser name mail), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (registerUser_impl (String name) (String mail)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> RegisterUser name mail), invocationRes = s_invocationRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg_l, fuzzy_goal_cases "AtCommit" "AtReturn" )
            case (AtCommit v vn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa PS')


            have s_calls_mono: "s_calls' c \<triangleq> x" if "s_calls c \<triangleq> x" for c x
              using AtCommit.ps_growing that
              by (auto simp add: ps_growing_def proof_state_rel_calls dest!: state_monotonicGrowth_calls[where c=c and info=x])


            have v_no_op1: "vn \<notin> uniqueIds op" if "s_calls' c \<triangleq> Call op r" for c op r
            proof (rule new_unique_not_in_calls_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format])
              show " new_unique_not_in_calls s_calls' vn"
                using AtCommit.uid_is_private'
                by (meson AtCommit.uid_is_private'2 uid_is_private'_def)

              show "s_calls' c \<triangleq> Call op r"
                using that .
            qed


            hence v_no_op: "vn \<notin> uniqueIds op" if "s_calls c \<triangleq> Call op r" for c op r
              using s_calls_mono that by blast


            have v_no_delete1: False if "s_calls c \<triangleq> Call (DeleteKey v) Undef" for c
              using v_no_op[OF that] AtCommit.uniqueIds_eq
              by (auto simp add: uniqueIds_mapOp_def uniqueIds_val_def)


            have v_no_delete2: "s_calls c \<noteq> Some (Call (DeleteKey v) Undef)" for c
              using v_no_delete1 by blast


            have v_no_op': "vn \<notin> uniqueIds op" if "s_calls' c \<triangleq> Call op r" for c op r
            proof (rule new_unique_not_in_calls_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format])
              show " new_unique_not_in_calls s_calls' vn"
                by (meson AtCommit.uid_is_private'2 uid_is_private'_def)

              show "s_calls' c \<triangleq> Call op r"
                using that .
            qed


            have v_no_delete1': False if "s_calls' c \<triangleq> Call (DeleteKey v) Undef" for c
              using v_no_op'[OF that] ` uniqueIds v = {vn}`
              by (auto simp add: uniqueIds_mapOp_def uniqueIds_val_def)

            have v_no_delete2': "s_calls' c \<noteq> Some (Call (DeleteKey v) Undef)" for c
              using v_no_delete1' by blast



            from AtCommit
            show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)

              case inv1

              from `inv1 (s_invocationOp'(i \<mapsto> RegisterUser name mail)) (s_invocationRes'(i := None))
                  (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)



            next
              case inv2
              from `inv2 (s_invocationOp'(i \<mapsto> RegisterUser name mail)) (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
              show ?case
                apply (auto simp add: inv2_def)
                   apply (auto simp add: map_update_all_get i_callOriginI_h_simp)
                by (auto simp add: i_callOriginI_h_update_to3 split: if_splits)
            next 
              case inv3

              from `uid_is_private' i s_calls' s_invocationOp' s_invocationRes' s_knownIds' vn`
              have "new_unique_not_in_calls s_calls' vn"
                by (auto simp add: uid_is_private'_def)


              text "Because v is a new unique id there can be no delete operation on that type:"
              hence no_delete: "s_calls' delete \<noteq> Some (Call (DeleteKey v) delete_r)" for delete delete_r
                using `uniqueIds v = {vn}` by (auto simp add: new_unique_not_in_calls_def uniqueIds_mapOp_def, force)

                

              from `inv3 s_calls' s_happensBefore'`
              show ?case
                by (auto simp add: no_delete inv3_def `c \<noteq> ca` updateHb_cases in_sequence_cons inv3(17) inv3(19) v_no_delete2')
                


            qed




          next
            case (AtReturn v vn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            then show ?case
              apply (auto simp add: inv_def)
              apply (auto simp add: inv1_def )
              by presburger
          qed

        qed
      qed

    next
      case (UpdateMail user mail)

      show "procedureCorrect S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre UpdateMail
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)

      next
        case execution
        show "execution_s_correct S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound4)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: UpdateMail procedures_def )

          show "localState S i \<triangleq> (Map.empty, uniqueIds (UpdateMail user mail), updateMail_impl (UserId user) (String mail))"
            by (auto simp add: UpdateMail procedures_def )

          note updateMail_impl_def[simp]

          show "invocationOp S i \<triangleq> UpdateMail user mail"
            using UpdateMail \<open>invocationOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by (simp add: procedure_correct.in_initial_state)

          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> UpdateMail user mail), invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (UpdateMail user mail), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (updateMail_impl (UserId user) (String mail)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> UpdateMail user mail), invocationRes = s_invocationRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c ca resa PS')
            
            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)
              case inv1
              
              from `inv1 (s_invocationOp'(i \<mapsto> UpdateMail user mail)) (s_invocationRes'(i := None))
               (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)

            next
              case inv2
              from `inv2 (s_invocationOp'(i \<mapsto> UpdateMail user mail)) (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
              show ?case
                using `c \<noteq> ca` by (auto simp add: inv2_def i_callOriginI_h_update_to3, meson)

            next
              case inv3

              from \<open>toplevel_spec crdtSpec' \<lparr>calls = s_calls', happensBefore = s_happensBefore'\<rparr> vis' (KeyExists (UserId user)) (Bool True)\<close>
                obtain upd_c upd_op upd_r 
                  where c0: "upd_c \<in> vis'"
                    and c1: "is_update upd_op"
                    and c2: "s_calls' upd_c \<triangleq> Call (NestedOp (UserId user) upd_op) upd_r"
                    and c3: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>r. s_calls' c' \<noteq> Some (Call (DeleteKey (UserId user)) r)) \<or> (c', upd_c) \<in> s_happensBefore'"
                  apply (auto simp add: crdt_spec_defs)
                  by (smt extract_op_eq inv3.less_eq subset_h1)


                show ?case
                proof (auto simp add: inv3_def `c \<noteq> ca` `c \<noteq> ca`[symmetric])

                  show "False"
                    if d3: "is_update (Mail (Assign (String mail)))"
                      and d0: "delete \<noteq> c"
                      and d1: "delete \<noteq> ca"
                      and d5: "(delete, ca) \<in> updateHb s_happensBefore' vis' [c, ca]"
                      and d2: "s_calls' delete \<triangleq> Call (DeleteKey (UserId user)) delete_r"
                    for  delete delete_r
                  proof -
                    from d5
                    have "delete \<in> vis'"
                      by (auto simp add: updateHb_cases in_sequence_cons `\<And>x y.  x = c \<or> x = ca \<Longrightarrow> (y, x) \<notin> s_happensBefore'` d0[symmetric])


                    from c3[rule_format, OF `delete \<in> vis'`]
                    have "(delete, upd_c) \<in> s_happensBefore'"
                      by (auto simp add: d2)

                    text "This violates invariant 3"
                    with `inv3 s_calls' s_happensBefore'` c2 c1 d2
                    show False
                      apply (auto simp add: inv3_def)
                      by blast
                  qed

                  show "False"
                    if d0: "write \<noteq> c"
                      and d1: "write \<noteq> ca"
                      and d2: "delete \<noteq> c"
                      and d3: "delete \<noteq> ca"
                      and d4: "is_update upd"
                      and d5: "s_calls' write \<triangleq> Call (NestedOp u upd) write_r"
                      and d6: "(delete, write) \<in> updateHb s_happensBefore' vis' [c, ca]"
                      and d7: "s_calls' delete \<triangleq> Call (DeleteKey u) delete_r"
                    for "write" delete u upd write_r delete_r
                  proof - text "From old invariant ... "
                    from d6
                    have "(delete, write) \<in> s_happensBefore'"
                      by (metis d0 d1  insert_iff list.set(1) list.simps(15) singletonD updateHb_simp2)


                    with `inv3 s_calls' s_happensBefore'` d4 d5 d7 
                    show False
                      by (auto simp add: inv3_def, blast)

                  qed
                qed
              qed

            next
              case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c ca resa)
              then show ?case
                by (auto simp add: inv_def inv1_def, presburger) 
            next
              case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res PS')

              


              
              show ?case 
                using NotExists_AtCommit.invocation_happensBeforeH_eq
                using NotExists_AtCommit.inv
                by (auto simp add: inv_def inv1_def inv2_def inv3_def 
                      i_callOriginI_h_update_to3 map_update_all_get updateHb_single NotExists_AtCommit.PS'_eq, meson)



            next
              case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
              then show ?case 
                by (auto simp add: inv_def inv1_def, presburger) 
            qed
          qed
        qed

    next
      case (RemoveUser user)
      
      show "procedureCorrect S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre RemoveUser
          apply (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)
          using new_invocation_cannot_happen_before show_P.i_fresh show_P.wf_pre apply blast
          using i_callOriginI_notI1 show_P.i_fresh show_P.wf_pre by blast


      next
        case execution
        show "execution_s_correct S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound4)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: RemoveUser procedures_def )

          show "localState S i \<triangleq> (Map.empty, uniqueIds (RemoveUser user), removeUser_impl (UserId user))"
            by (auto simp add: RemoveUser procedures_def )

          note removeUser_impl_def[simp]

          show "invocationOp S i \<triangleq> RemoveUser user"
            using RemoveUser \<open>invocationOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by simp


          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> RemoveUser user), invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (RemoveUser user), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (removeUser_impl (UserId user)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> RemoveUser user), invocationRes = s_invocationRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res PS')

            from \<open>toplevel_spec crdtSpec' \<lparr>calls = s_calls', happensBefore = s_happensBefore'\<rparr> vis' (DeleteKey (UserId user)) res\<close>
            have [simp]: "res= Undef"
              by (auto simp add: crdt_spec_defs)

            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)
              case inv1
              from `inv1 (s_invocationOp'(i \<mapsto> RemoveUser user)) (s_invocationRes'(i := None))
                   (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)

              
            next
              case inv2
              from `inv2 (s_invocationOp'(i \<mapsto> RemoveUser user)) (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
              show ?case 
                apply (auto simp add: inv2_def i_callOriginI_h_update_to3   `\<And>c. s_callOrigin' c \<noteq> Some tx`)
                using inv2(2) by force+

            next
              case inv3
              from `inv3 s_calls' s_happensBefore'`
              show ?case
                by (auto simp add: inv3_def updateHb_cases  in_sequence_cons  inv3)
            qed

          next
             case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case
              apply (auto simp add: inv_def inv1_def)
              by presburger+
          qed
        qed
      qed
    next
      case (GetUser user)
  
      show "procedureCorrect S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre GetUser
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps  new_invocation_cannot_happen_after)


      next
        case execution
        show "execution_s_correct S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound4)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: GetUser procedures_def )

          show "localState S i \<triangleq> (Map.empty, uniqueIds (GetUser user), getUser_impl (UserId user))"
            by (auto simp add: GetUser procedures_def )

          note getUser_impl_def[simp]

          show "invocationOp S i \<triangleq> GetUser user"
            using GetUser \<open>invocationOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by simp
          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> GetUser user), invocationRes = s_invocationRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (GetUser user), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (getUser_impl (UserId user)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp(i \<mapsto> GetUser user), invocationRes = s_invocationRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c ca resa cb res PS')
            then show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)
              case (inv1)
              then show ?case
                by (auto simp add: inv1_def)
            next
              case (inv2)
              then show ?case 
                apply (auto simp add: inv2_def)
                apply (metis i_callOriginI_h_update_to2 list.set_intros(1) map_update_all_get option.inject)
                apply (metis (no_types, lifting) i_callOriginI_h_update_to2 insertCI list.simps(15) map_update_all_get option.inject)
                 apply (metis (no_types, lifting) i_callOriginI_h_update_to2 insertCI list.simps(15) map_update_all_get option.inject)
                by (smt i_callOriginI_h_def i_callOriginI_h_update_to2 map_update_all_get option.inject)
            next
              case (inv3)
              then show ?case 
                by (auto simp add: inv3_def i_callOriginI_h_update_to3 updateHb_cases in_sequence_cons is_update_userDataOp_def)
            qed  
              
          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c ca resa cb res)
            then show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 )
              case (inv1)

              text "From the query result, we get an update that is not affected by a remove."

              from \<open>toplevel_spec crdtSpec' \<lparr>calls = s_calls', happensBefore = s_happensBefore'\<rparr> vis' (KeyExists (UserId user)) (Bool True)\<close>
              obtain upd_c upd_op upd_r
                where upd_c0: "upd_c \<in> vis'"
                  and upd_c1: "is_update upd_op"
                  and upd_c2: "s_calls' upd_c \<triangleq> Call (NestedOp (UserId user) upd_op) upd_r"
                  and upd_c3: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>r. s_calls' c' \<noteq> Some (Call (DeleteKey (UserId user)) r)) \<or> (c', upd_c) \<in> s_happensBefore'"
                apply (auto simp add: crdt_spec_defs  split: if_splits)
                by (smt extract_op_eq in_mono inv1.less_eq)




              text "No calls means we do not have any invocation happened before"
              have no_hb: "(r, i) \<notin> invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore'" for r
                using inv1(5) by (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)

              have [simp]: "s_transactionOrigin'(tx := None) = s_transactionOrigin'"
                  by (simp add: fun_upd_idem_iff inv1.s_transactionOrigin'___eq)
              
              show ?case
              proof (auto simp add: inv1_def no_hb)

                show "\<exists>c''. i_callOriginI_h s_callOrigin' s_transactionOrigin' c'' \<triangleq> r \<and> c'' \<notin> vis'"
                  if c0: "r \<noteq> i"
                    and c1: "s_invocationOp' r \<triangleq> RemoveUser user"
                    and c3: "i_callOriginI_h s_callOrigin' s_transactionOrigin' c' \<triangleq> r"
                    and c4: "c' \<in> vis'"
                  for  r c'
                  using use_inv3'[OF `inv3 s_calls' s_happensBefore'`]
                  by (smt c1 c3 fun_upd_triv inv1.inv2 inv1.s_invocationOp'___eq inv2_def upd_c1 upd_c2 upd_c3)

                show "g_res = NotFound"
                  if c0: "r \<noteq> i"
                    and c1: "g \<noteq> i"
                    and c2: "s_invocationOp' r \<triangleq> RemoveUser u"
                    and c3: "s_invocationOp' g \<triangleq> GetUser u"
                    and r_g_hb: "(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore'"
                    and c5: "s_invocationRes' g \<triangleq> g_res"
                  for  r g u g_res
                  using \<open>inv1 (s_invocationOp'(i \<mapsto> GetUser user)) (s_invocationRes'(i := None))
                         (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')\<close>
                  using that  by (auto simp add: inv1_def split: if_splits)




              qed
            qed
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case 
              by (auto simp add: inv_def inv1_def inv2_def inv3_def i_callOriginI_h_update_to3 map_update_all_get updateHb_cases in_sequence_cons split: if_splits, meson)

          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case 
              by  (auto simp add: inv_def inv1_def, presburger)
          qed
        qed
      qed
    qed
  qed
qed

end
