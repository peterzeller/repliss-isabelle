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



text_raw \<open>\DefineSnippet{userbase_impl}{\<close>
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
text_raw \<open>}%EndSnippet\<close>





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

text_raw \<open>\DefineSnippet{userbase_invariants}{\<close>
definition inv1  where
  "inv1 op res ihb \<equiv> \<forall>r g u g_res.
    op r \<triangleq> RemoveUser u
  \<longrightarrow> op g \<triangleq> GetUser u
  \<longrightarrow> (r,g) \<in> ihb
  \<longrightarrow> res g \<triangleq> g_res
  \<longrightarrow> g_res = NotFound"

definition inv2  where
  "inv2 c_calls hb \<equiv> \<not>(\<exists>write delete u upd.
    (cOp c_calls write \<triangleq> NestedOp u upd)
  \<and> is_update upd
  \<and> (cOp c_calls delete \<triangleq> DeleteKey u)
  \<and> (delete, write) \<in> hb
  )"

definition inv3  where
  "inv3 op i_origin c_calls \<equiv> \<forall>u i c.
    op i \<triangleq> RemoveUser u
  \<longrightarrow> i_origin c \<triangleq> i
  \<longrightarrow> cOp c_calls c \<triangleq> DeleteKey (UserId u)"

definition inv :: "(proc, operation, val) invContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> 
    inv1 (invocOp ctxt) (invocRes ctxt) (invocation_happensBefore ctxt) 
  \<and> inv2 (calls ctxt) (happensBefore ctxt)
  \<and> inv3 (invocOp ctxt) (i_callOriginI ctxt) (calls ctxt)"
text_raw \<open>}%EndSnippet\<close>



lemma use_inv2'':
  assumes "inv2 c_calls hb"
    and "cOp c_calls write \<triangleq> NestedOp u upd"
    and "is_update upd"
    and "cOp c_calls delete \<triangleq> DeleteKey u"
  shows "(delete, write) \<notin> hb"
  by (meson assms inv2_def)

lemmas use_inv3 = inv3_def[unfolded atomize_eq, THEN iffD1, rule_format]

definition userStruct :: "(userDataOp, val) crdtSpec" where
  "userStruct \<equiv> 
      struct_field Name (register_spec Undef) 
  .\<or>. struct_field Mail (register_spec Undef)" 

definition crdtSpec :: "(operation, val) crdtSpec" where
  "crdtSpec \<equiv> map_sdw_spec userStruct"


definition userStruct' :: "('a, userDataOp, val) ccrdtSpec" where
  "userStruct' \<equiv> 
      struct_field' Name (register_spec' Undef) 
 .\<or>.. struct_field' Mail (register_spec' Undef)" 

definition crdtSpec' :: "(operation, operation, val) ccrdtSpec" where
  "crdtSpec' \<equiv> map_sdw_spec' userStruct'"

lemma inj_fields[simp]:
  "inj Name" "inj Mail"
  by (auto simp add: inj_def)

lemma crdtSpec_rel:
  shows "crdt_spec_rel crdtSpec crdtSpec'"
  by (auto simp add: crdtSpec_def crdtSpec'_def userStruct_def userStruct'_def)



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
    by (auto simp add: crdtSpec_def userStruct_def)
qed





lemma isUserId_infinite[simp]: "infinite (Collect isUserId)"
proof (rule infinite_if_mappable_to_nat)
  show "\<exists>x\<in>Collect isUserId. n \<le> (case x of UserId n \<Rightarrow> nat n)" for n
    by (rule bexI[where x="UserId (int n)"],
        auto simp add: isUserId_def)
qed



lemma invariant_progr[simp]: "invariant progr = example_userbase.inv"
  by (auto simp add: progr_def)

declare invContext.defs[simp]

lemmas crdt_spec_defs = 
  toplevel_spec_def crdtSpec'_def struct_field'_def map_sdw_spec'_def map_spec'_def userStruct'_def register_spec'_def
  set_rw_spec'_def deleted_calls_sdw'_def


theorem userbase_correct: "programCorrect progr"
proof M_show_programCorrect

  case invariant_initial_state
  show "invariant_all' (initialState progr)"
    by (simp add: example_userbase.inv_def initialState_def inv1_def inv3_def inv2_def invContextH2_happensBefore invContextH2_i_invocOp progr_def)

  case (procedure_correct S i)



  show "procedureCorrect S i"
  proof (rule Initial_Label, rule show_initial_state_prop[OF procedure_correct], rule DC_final2, casify)
    case (show_P S_pre proc initState impl)
    have "invocOp S i \<triangleq> proc"
      using show_P by auto
    have "invocRes S i = None"
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
          by (auto simp add:  inv_def inv1_def inv3_def invContextH2_simps)

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

          show "invocOp S i \<triangleq> RegisterUser name mail"
            using RegisterUser \<open>invocOp S i \<triangleq> proc\<close> by blast


          show "program_wellFormed (prog S)"
            by (simp add: initialStates_reachable_from_initialState procedure_correct.in_initial_state)

          show "invariant_all' S"
            using execution.in_initial_state by blast

          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 



          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> RegisterUser name mail), invocRes = s_invocRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (RegisterUser name mail), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (registerUser_impl (String name) (String mail)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_txOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> RegisterUser name mail), invocRes = s_invocRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes
          proof (repliss_vcg_l, fuzzy_goal_cases "AtCommit" "AtReturn" )
            case (AtCommit v vn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res ca resa PS')


            from AtCommit.inv
            show ?case
            proof (auto simp add: inv_def AtCommit.PS'_eq, fuzzy_goal_cases inv1 inv2 inv3)

              case inv1

              from `inv1 (s_invocOp'(i \<mapsto> RegisterUser name mail)) (s_invocRes'(i := None))
                  (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore')`
              show ?case
                using AtCommit.invocation_happensBeforeH_eq
                by (auto simp add: inv1_def)




            next
              case inv3
              from `inv3 (s_invocOp'(i \<mapsto> RegisterUser name mail)) (i_callOriginI_h s_callOrigin' s_txOrigin') s_calls'`
              show ?case
                by (auto simp add: inv3_def map_update_all_get i_callOriginI_h_simp i_callOriginI_h_update_to3 split: if_splits)
            next 
              case inv2

              from `uid_is_private' i s_calls' s_invocOp' s_invocRes' s_knownIds' vn`
              have "new_unique_not_in_calls s_calls' vn"
                by (auto simp add: uid_is_private'_def)


              text "Because v is a new unique id there can be no delete operation on that type:"
              hence no_delete: "cOp s_calls' delete \<noteq> Some (DeleteKey v)" for delete
                using `uniqueIds v = {vn}` by (auto simp add: new_unique_not_in_calls_def uniqueIds_mapOp_def cOp_Some_iff, force)

              from `inv2 s_calls' s_happensBefore'`
              show ?case
                by (auto simp add: no_delete inv2_def  updateHb_cases in_sequence_cons  )

            qed




          next
            case (AtReturn v vn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res ca resa)
            then show ?case
              by (auto simp add: inv_def inv1_def split: if_splits)
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
          by (auto simp add:  inv_def inv1_def inv3_def inv2_def invContextH2_simps)

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

          show "invocOp S i \<triangleq> UpdateMail user mail"
            using UpdateMail \<open>invocOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by (simp add: procedure_correct.in_initial_state)

          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> UpdateMail user mail), invocRes = s_invocRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (UpdateMail user mail), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (updateMail_impl (UserId user) (String mail)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_txOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> UpdateMail user mail), invocRes = s_invocRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c ca resa PS')

            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)
              case inv1

              from `inv1 (s_invocOp'(i \<mapsto> UpdateMail user mail)) (s_invocRes'(i := None))
               (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)

            next
              case inv3
              from `inv3 (s_invocOp'(i \<mapsto> UpdateMail user mail)) (i_callOriginI_h s_callOrigin' s_txOrigin') s_calls'`
              show ?case
                by (auto simp add: inv3_def i_callOriginI_h_update_to3 split: if_splits)

            next
              case inv2


              from \<open>toplevel_spec crdtSpec' \<lparr>calls = s_calls', happensBefore = s_happensBefore'\<rparr> vis' (KeyExists (UserId user)) (Bool True)\<close>

              obtain upd_c upd_op
                where a0: "upd_c \<in> vis'"
                  and a1: "extract_op s_calls' upd_c = NestedOp (UserId user) upd_op"
                  and a2: "is_update upd_op"
                  and a3: "\<forall>d\<in>vis'. extract_op s_calls' d = DeleteKey (UserId user) \<longrightarrow> (d, upd_c) \<in> s_happensBefore'"
                by (auto simp add: crdt_spec_defs)


              from a1 
              have a1': "cOp s_calls' upd_c \<triangleq> NestedOp (UserId user) upd_op"
                by (metis (mono_tags, lifting) a0 cOp_Some extract_op_def in_dom inv2.less_eq option.sel)

              from a3 
              have a3': "\<forall>d\<in>vis'. cOp s_calls' d \<triangleq> DeleteKey (UserId user) \<longrightarrow> (d, upd_c) \<in> s_happensBefore'"
                by (meson extract_op_eq' inv2.less_eq subset_iff)


              text \<open>There can be no delete:\<close>

              have noDelete: "delete \<notin> vis'" if "cOp s_calls' delete \<triangleq> DeleteKey (UserId user)" for delete
                using use_inv2''[OF \<open>inv2 s_calls' s_happensBefore'\<close> a1' a2 that] a3' that by blast

              text \<open>With this we can show that inv2 is maintained:\<close>

              show ?case
                using noDelete inv2.not_member3 use_inv2''[OF inv2.inv2]
                by (auto simp add: inv2_def `c \<noteq> ca` `c \<noteq> ca`[symmetric] updateHb_cons)

            qed

          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c ca resa)
            then show ?case
              by (auto simp add: inv_def inv1_def, presburger) 
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res PS')


            show ?case 
              using NotExists_AtCommit.invocation_happensBeforeH_eq
              using NotExists_AtCommit.inv
              by (auto simp add: inv_def inv1_def inv3_def inv2_def 
                  i_callOriginI_h_update_to3 map_update_all_get updateHb_single NotExists_AtCommit.PS'_eq, meson)

          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res)
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
          apply (auto simp add:  inv_def inv1_def inv3_def inv2_def invContextH2_simps)
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

          show "invocOp S i \<triangleq> RemoveUser user"
            using RemoveUser \<open>invocOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by simp


          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> RemoveUser user), invocRes = s_invocRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (RemoveUser user), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (removeUser_impl (UserId user)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_txOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> RemoveUser user), invocRes = s_invocRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res PS')


            from Exists_AtCommit.inv Exists_AtCommit.invocation_happensBeforeH_eq
            show ?case
            proof (auto simp add: inv_def Exists_AtCommit.PS'_eq, fuzzy_goal_cases inv1 inv2 inv3)
              case inv1
              from `inv1 (s_invocOp'(i \<mapsto> RemoveUser user)) (s_invocRes'(i := None))
                   (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)

            next
              case inv3
              from `inv3 (s_invocOp'(i \<mapsto> RemoveUser user)) (i_callOriginI_h s_callOrigin' s_txOrigin') s_calls'`
              show ?case 
                by (auto simp add: inv3_def i_callOriginI_h_update_to3   `\<And>c. s_callOrigin' c \<noteq> Some tx` split: if_splits)

            next
              case inv2
              from `inv2 s_calls' s_happensBefore'`
              show ?case
                using Exists_AtCommit.not_member2
                by (auto simp add: inv2_def updateHb_cases  in_sequence_cons  inv2)

            qed

          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res)
            then show ?case
              by (auto simp add: inv_def inv1_def split: if_splits)
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
          by (auto simp add:  inv_def inv1_def inv3_def inv2_def invContextH2_simps  new_invocation_cannot_happen_after)


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

          show "invocOp S i \<triangleq> GetUser user"
            using GetUser \<open>invocOp S i \<triangleq> proc\<close> by blast

          show "program_wellFormed (prog S)"
            by simp
          show "invariant_all' S"
            using execution.in_initial_state by blast


          from crdtSpec_rel
          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            by simp 

          show "execution_s_check (invariant progr) crdtSpec' \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> GetUser user), invocRes = s_invocRes(i := None), ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (GetUser user), ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty, ps_prog = progr\<rparr> (getUser_impl (UserId user)) (finalCheck (invariant progr) i)"
            if c0: "\<And>tx. s_txOrigin tx \<noteq> Some i"
              and c1: "invariant progr \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin, txOrigin = s_txOrigin, knownIds = s_knownIds, invocOp = s_invocOp(i \<mapsto> GetUser user), invocRes = s_invocRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes
          proof (repliss_vcg_l, fuzzy_goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c ca resa cb res PS')

            from Exists_AtCommit.inv
            show ?case
            proof (auto simp add: inv_def Exists_AtCommit.PS'_eq, fuzzy_goal_cases inv1 inv2 inv3)
              case (inv1)
              then show ?case
                using Exists_AtCommit.invocation_happensBeforeH_eq
                by (auto simp add: inv1_def)


            next
              case (inv3)
              then show ?case 
                using Exists_AtCommit.not_ca_eq Exists_AtCommit.not_c_eq Exists_AtCommit.not_c_eq2
                by (auto simp add: inv3_def i_callOriginI_h_update_to3 split: if_splits)
            next
              case (inv2)
              then show ?case 
                by (auto simp add: inv2_def i_callOriginI_h_update_to3 updateHb_cases in_sequence_cons is_update_userDataOp_def)
            qed  

          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c ca resa cb res)

            find_theorems name: "Exists_AtReturn." 

            from Exists_AtReturn.inv
            show ?case
            proof (auto simp add: inv_def, fuzzy_goal_cases inv1 inv2 inv3)
              case (inv1)


              text "From the query result, we get an update that is not affected by a remove."

              from \<open>toplevel_spec crdtSpec' \<lparr>calls = s_calls', happensBefore = s_happensBefore'\<rparr> vis' (KeyExists (UserId user)) (Bool True)\<close>
              obtain upd_c upd_op
                where upd_c0: "upd_c \<in> vis'"
                  and upd_c1: "extract_op s_calls' upd_c = NestedOp (UserId user) upd_op"
                  and upd_c2: "is_update upd_op"
                  and upd_c3: "\<forall>d\<in>vis'. extract_op s_calls' d = DeleteKey (UserId user) \<longrightarrow> (d, upd_c) \<in> s_happensBefore'"
                by (auto simp add: crdt_spec_defs  split: if_splits)

              from upd_c1
              have upd_c1': "cOp s_calls' upd_c \<triangleq> NestedOp (UserId user) upd_op"
                by (metis Exists_AtReturn.less_eq extract_op_eq' in_mono upd_c0)


              from upd_c3
              have upd_c3': "(d, upd_c) \<in> s_happensBefore'"
                if "cOp s_calls' d \<triangleq> DeleteKey (UserId user)"
                  and "d \<in> vis'"
                for d
                using that
                by (meson extract_op_eq' Exists_AtReturn.less_eq subset_iff)

              text "No calls means we do not have any invocation happened before in the pre-state."
              have no_hb: "(r, i) \<notin> invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore'" for r
                using Exists_AtReturn.not_s_txOrigin'_eq by (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)


              have [simp]: "s_txOrigin'(tx := None) = s_txOrigin'"
                by (simp add: fun_upd_idem_iff Exists_AtReturn.s_txOrigin'_eq)


              show ?case
              proof (auto simp add: inv1_def no_hb Exists_AtReturn.invocation_happensBeforeH_eq)




                show "\<exists>c''. i_callOriginI_h s_callOrigin' s_txOrigin' c'' \<triangleq> r \<and> c'' \<notin> vis'"
                  if c0: "r \<noteq> i"
                    and c1: "s_invocOp' r \<triangleq> RemoveUser user"
                    and c3: "i_callOriginI_h s_callOrigin' s_txOrigin' c' \<triangleq> r"
                    and c4: "c' \<in> vis'"
                  for  r c'
                proof -

                  from c1 c0
                  have c1': \<open>(s_invocOp'(i \<mapsto> GetUser user)) r \<triangleq> RemoveUser user\<close> by simp


                  text \<open>use inv3 to get the delete operation\<close>

                  from use_inv3[OF inv1.inv3 c1' c3]
                  have "cOp s_calls' c' \<triangleq> DeleteKey (UserId user)" .


                  text \<open>The delete must be before upd_c by the CRDT spec (otherwise entry would not exist)\<close>

                  from upd_c3'[OF \<open>cOp s_calls' c' \<triangleq> DeleteKey (UserId user)\<close> c4]
                  have "(c', upd_c) \<in> s_happensBefore'" .

                  from use_inv2''[OF inv1.inv2 upd_c1' upd_c2 \<open>cOp s_calls' c' \<triangleq> DeleteKey (UserId user)\<close>]
                  have \<open>(c', upd_c) \<notin> s_happensBefore'\<close>  .

                  with \<open>(c', upd_c) \<in> s_happensBefore'\<close>
                  show ?thesis by blast
                qed

                show "g_res = NotFound"
                  if c0: "r \<noteq> i"
                    and c1: "g \<noteq> i"
                    and c2: "s_invocOp' r \<triangleq> RemoveUser u"
                    and c3: "s_invocOp' g \<triangleq> GetUser u"
                    and r_g_hb: "(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore'"
                    and c5: "s_invocRes' g \<triangleq> g_res"
                  for  r g u g_res
                  using \<open>inv1 (s_invocOp'(i \<mapsto> GetUser user)) (s_invocRes'(i := None))
                         (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_txOrigin') s_happensBefore')\<close>
                  using that  by (auto simp add: inv1_def split: if_splits)




              qed

            next
              case inv2
              thus ?case
                by (auto simp add: inv2_def Exists_AtReturn is_update_userDataOp_def updateHb_simp2)
            next
              case inv3
              thus ?case
                by (auto simp add: inv3_def Exists_AtReturn i_callOriginI_h_update_to3 split: if_splits)

            qed
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res)
            then show ?case 
              by (auto simp add: inv_def inv1_def inv3_def inv2_def i_callOriginI_h_update_to3 map_update_all_get updateHb_cases in_sequence_cons split: if_splits, meson)

          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_txOrigin' s_knownIds' vis' s_invocOp' s_invocRes' c res)
            then show ?case 
              by  (auto simp add: inv_def inv1_def, presburger)
          qed
        qed
      qed
    qed
  qed
qed


end
