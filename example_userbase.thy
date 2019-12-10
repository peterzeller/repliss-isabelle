theory example_userbase
  imports 
    program_verification_tactics
    impl_language
    crdt_specs
    unique_ids
    program_proof_rules
begin

section "Example: User database"


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

type_synonym localState = "(val,operation,val) io"


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


abbreviation "toImpl2 x \<equiv> (x, toImpl)" 

definition procedures :: "proc \<Rightarrow> ((val, operation, val) io \<times> ((val, operation, val) io, operation, val) procedureImpl)" where
  "procedures invoc \<equiv>
  case invoc of
    RegisterUser name mail \<Rightarrow> toImpl2 (registerUser_impl (String name) (String mail))
  | UpdateMail u mail \<Rightarrow> toImpl2 (updateMail_impl (UserId u) (String mail))
  | RemoveUser u \<Rightarrow>  toImpl2 (removeUser_impl (UserId u))
  | GetUser u  \<Rightarrow>  toImpl2 (getUser_impl (UserId u))
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
    Name op \<Rightarrow> struct_field (register_spec Undef op) (\<lambda>oper. case oper of Name op \<Rightarrow> Some op | _ \<Rightarrow> None) 
  | Mail op \<Rightarrow> struct_field (register_spec Undef op) (\<lambda>oper. case oper of Mail op \<Rightarrow> Some op | _ \<Rightarrow> None)
)" 

definition crdtSpec :: "(operation, val) crdtSpec" where
  "crdtSpec \<equiv> map_dw_spec Bool userStruct"

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
  show "procedures_cannot_guess_ids procedures"
  proof (auto simp add: procedures_cannot_guess_ids_def procedures_def uniqueIds_proc_def split: proc.splits)
    show "\<And>n m uids. procedure_cannot_guess_ids uids (registerUser_impl (String n) (String m)) toImpl"
      by (auto simp add: registerUser_impl_def, show_procedures_cannot_guess_ids  )

    show "\<And>x21 x22 uids. procedure_cannot_guess_ids (uids \<union> uniqueIds (UserId x21)) (updateMail_impl (UserId x21) (String x22)) toImpl"
      by (auto simp add: updateMail_impl_def, show_procedures_cannot_guess_ids  )

    show "\<And>x3 uids. procedure_cannot_guess_ids (uids \<union> uniqueIds (UserId x3)) (removeUser_impl (UserId x3)) toImpl"
      by (auto simp add: removeUser_impl_def, show_procedures_cannot_guess_ids  )
  
    show " \<And>x4 uids. procedure_cannot_guess_ids (uids \<union> uniqueIds (UserId x4)) (getUser_impl (UserId x4)) toImpl"
      by (auto simp add: getUser_impl_def, show_procedures_cannot_guess_ids  )
  qed

  show "queries_cannot_guess_ids crdtSpec"
  proof (simp add:  crdtSpec_def, standard)
    show "queries_cannot_guess_ids userStruct"
    proof (auto simp add: userStruct_def queries_cannot_guess_ids_def split: userDataOp.splits)

      show "query_cannot_guess_ids (uniqueIds s) (struct_field (register_spec Undef s) (case_userDataOp Some Map.empty))" for s
        by (standard, auto split: userDataOp.splits)


      show "query_cannot_guess_ids (uniqueIds s) (struct_field (register_spec Undef s) (case_userDataOp Map.empty Some))" for s 
        by (standard, auto split: userDataOp.splits)
    qed

  qed (simp)
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

theorem userbase_correct: "programCorrect progr"
proof M_show_programCorrect

  case invariant_initial_state
  show "invariant_all' (initialState progr)"
    by (simp add: example_userbase.inv_def initialState_def inv1_def inv2_def inv3_def invContextH2_happensBefore invContextH2_i_invocationOp progr_def)

  case (procedure_correct S i)



  show "procedureCorrect progr S i"
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

    show "procedureCorrect progr S i"
    proof (cases proc)
      case (RegisterUser name mail)

      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre RegisterUser
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)

      next
        case execution
        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: RegisterUser procedures_def )

          show "localState S i \<triangleq> registerUser_impl (String name) (String mail)"
            by (auto simp add: RegisterUser procedures_def )

          note registerUser_impl_def[simp]

          show "invocationOp S i \<triangleq> RegisterUser name mail"
            using RegisterUser \<open>invocationOp S i \<triangleq> proc\<close> by blast



          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
              (s_invocationOp(i \<mapsto> RegisterUser name mail)) (s_invocationRes(i := None)) {} {} {} [] None True
              (registerUser_impl (String name) (String mail))"
            for s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "AtCommit" "AtReturn" )
            case (AtCommit v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)

            find_theorems uid_is_private



            have v_no_op: "to_nat v \<notin> uniqueIds op" if "s_calls c \<triangleq> Call op r" for c op r
            proof (rule new_unique_not_in_calls_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format])
              show " new_unique_not_in_calls s_calls (to_nat v)"
                by (meson AtCommit(4) uid_is_private'_def)

              show "s_calls c \<triangleq> Call op r"
                using that .
            qed


            have v_no_delete1: False if "s_calls c \<triangleq> Call (DeleteKey v) Undef" for c
              using v_no_op[OF that] ` uniqueIds v = {to_nat v}`
              by (auto simp add: uniqueIds_mapOp_def uniqueIds_val_def)

            have v_no_delete2: "s_calls c \<noteq> Some (Call (DeleteKey v) Undef)" for c
              using v_no_delete1 by blast


            have v_no_op': "to_nat v \<notin> uniqueIds op" if "s_calls' c \<triangleq> Call op r" for c op r
            proof (rule new_unique_not_in_calls_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format])
              show " new_unique_not_in_calls s_calls' (to_nat v)"
                by (meson `uid_is_private' i s_calls' s_invocationOp' s_invocationRes' s_knownIds' (to_nat v)` uid_is_private'_def)

              show "s_calls' c \<triangleq> Call op r"
                using that .
            qed


            have v_no_delete1': False if "s_calls' c \<triangleq> Call (DeleteKey v) Undef" for c
              using v_no_op'[OF that] ` uniqueIds v = {to_nat v}`
              by (auto simp add: uniqueIds_mapOp_def uniqueIds_val_def)

            have v_no_delete2': "s_calls' c \<noteq> Some (Call (DeleteKey v) Undef)" for c
              using v_no_delete1' by blast



            from AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3)

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

              from `uid_is_private' i s_calls' s_invocationOp' s_invocationRes' s_knownIds' (to_nat v)`
              have "new_unique_not_in_calls s_calls' (to_nat v)"
                by (auto simp add: uid_is_private'_def)


              text "Because v is a new unique id there can be no delete operation on that type:"
              hence no_delete: "s_calls' delete \<noteq> Some (Call (DeleteKey v) delete_r)" for delete delete_r
                using `uniqueIds v = {to_nat v}` by (auto simp add: new_unique_not_in_calls_def uniqueIds_mapOp_def, force)

                

              from `inv3 s_calls' s_happensBefore'`
              show ?case
                by (auto simp add: no_delete inv3_def `c \<noteq> ca` updateHb_cases in_sequence_cons inv3(17) inv3(19) v_no_delete2')
                


            qed




          next
            case (AtReturn v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            then show ?case
              apply (auto simp add: inv_def)
              apply (auto simp add: inv1_def )
              by presburger
          qed

        qed
      qed

    next
      case (UpdateMail user mail)

      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre UpdateMail
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)

      next
        case execution
        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: UpdateMail procedures_def )

          show "localState S i \<triangleq> updateMail_impl (UserId user) (String mail)"
            by (auto simp add: UpdateMail procedures_def )

          note updateMail_impl_def[simp]

          show "invocationOp S i \<triangleq> UpdateMail user mail"
            using UpdateMail \<open>invocationOp S i \<triangleq> proc\<close> by blast



          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
              (s_invocationOp(i \<mapsto> UpdateMail user mail)) (s_invocationRes(i := None)) {} {} {} [] None True
              (updateMail_impl (UserId user) (String mail))"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            
            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3)
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

              from \<open>crdtSpec (KeyExists (UserId user)) \<lparr>calls = s_calls' |` vis', happensBefore = s_happensBefore' |r vis'\<rparr> (Bool True)\<close>
                obtain upd_c upd_op upd_r 
                  where c0: "upd_c \<in> vis'"
                    and c1: "is_update upd_op"
                    and c2: "s_calls' upd_c \<triangleq> Call (NestedOp (UserId user) upd_op) upd_r"
                    and c3: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>r. s_calls' c' \<noteq> Some (Call (DeleteKey (UserId user)) r)) \<or> (c', upd_c) \<in> s_happensBefore'"
                  by (auto simp add: crdtSpec_def map_dw_spec_def map_spec_def deleted_calls_dw_def restrict_relation_def restrict_map_def split: if_splits)


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
              case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
              then show ?case
                by (auto simp add: inv_def inv1_def, presburger) 
            next
              case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)

              


              
              from NotExists_AtCommit
              show ?case 
                by (auto simp add: inv_def inv1_def inv2_def inv3_def 
                      i_callOriginI_h_update_to3 map_update_all_get updateHb_single, meson)


            next
              case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
              then show ?case 
                by (auto simp add: inv_def inv1_def, presburger) 
            qed
          qed
        qed

    next
      case (RemoveUser user)
      
      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre RemoveUser
          apply (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps)
          using new_invocation_cannot_happen_before show_P.i_fresh show_P.wf_pre apply blast
          using i_callOriginI_notI1 show_P.i_fresh show_P.wf_pre by blast


      next
        case execution
        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: RemoveUser procedures_def )

          show "localState S i \<triangleq> removeUser_impl (UserId user)"
            by (auto simp add: RemoveUser procedures_def )

          note removeUser_impl_def[simp]

          show "invocationOp S i \<triangleq> RemoveUser user"
            using RemoveUser \<open>invocationOp S i \<triangleq> proc\<close> by blast



          show " execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
        (s_invocationOp(i \<mapsto> RemoveUser user)) (s_invocationRes(i := None)) {} {} {} [] None True (removeUser_impl (UserId user))"
            for s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)

            from \<open>crdtSpec (DeleteKey (UserId user)) \<lparr>calls = s_calls' |` vis', happensBefore = s_happensBefore' |r vis'\<rparr> res\<close>
            have [simp]: "res= Undef"
              by (auto simp add: crdtSpec_def map_dw_spec_def map_spec_def)

            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3)
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
  
      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case 
          using show_P.invariant_pre GetUser
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def invContextH2_simps  new_invocation_cannot_happen_after)


      next
        case execution
        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: GetUser procedures_def )

          show "localState S i \<triangleq> getUser_impl (UserId user)"
            by (auto simp add: GetUser procedures_def )

          note getUser_impl_def[simp]

          show "invocationOp S i \<triangleq> GetUser user"
            using GetUser \<open>invocationOp S i \<triangleq> proc\<close> by blast



          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds (s_invocationOp(i \<mapsto> GetUser user))
        (s_invocationRes(i := None)) {} {} {} [] None True (getUser_impl (UserId user))"
            for s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            then show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3)
              case (inv1 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case
                by (auto simp add: inv1_def)
            next
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                apply (auto simp add: inv2_def)
                apply (metis i_callOriginI_h_update_to2 list.set_intros(1) map_update_all_get option.inject)
                apply (metis (no_types, lifting) i_callOriginI_h_update_to2 insertCI list.simps(15) map_update_all_get option.inject)
                 apply (metis (no_types, lifting) i_callOriginI_h_update_to2 insertCI list.simps(15) map_update_all_get option.inject)
                by (smt i_callOriginI_h_def i_callOriginI_h_update_to2 map_update_all_get option.inject)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv3_def i_callOriginI_h_update_to3 updateHb_cases in_sequence_cons is_update_userDataOp_def)
            qed  
              
          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            then show ?case
            proof (auto simp add: inv_def, goal_cases inv1 )
              case (inv1 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)

              text "From the query result, we get an update that is not affected by a remove."

              from \<open>crdtSpec (KeyExists (UserId user)) \<lparr>calls = s_calls' |` vis', happensBefore = s_happensBefore' |r vis'\<rparr> (Bool True)\<close>
              obtain upd_c upd_op upd_r
                where upd_c0: "upd_c \<in> vis'"
                  and upd_c1: "is_update upd_op"
                  and upd_c2: "s_calls' upd_c \<triangleq> Call (NestedOp (UserId user) upd_op) upd_r"
                  and upd_c3: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>r. s_calls' c' \<noteq> Some (Call (DeleteKey (UserId user)) r)) \<or> (c', upd_c) \<in> s_happensBefore'"
                by (auto simp add:crdtSpec_def map_dw_spec_def map_spec_def deleted_calls_dw_def restrict_map_def restrict_relation_def split: if_splits)




              text "No calls means we do not have any invocation happened before"
              have no_hb: "(r, i) \<notin> invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore'" for r
                using inv1(5) by (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)

              
              show ?case
              proof (auto simp add: inv1_def no_hb)


                show "\<exists>c''. i_callOriginI_h s_callOrigin' s_transactionOrigin' c'' \<triangleq> r \<and> c'' \<notin> vis'"
                  if c0: "r \<noteq> i"
                    and c1: "s_invocationOp' r \<triangleq> RemoveUser user"
                    and c3: "i_callOriginI_h s_callOrigin' s_transactionOrigin' c' \<triangleq> r"
                    and c4: "c' \<in> vis'"
                  for  r c'
                  thm inv1(18)
                  using c0 c1 c3 state_monotonicGrowth_invocationOp_i[OF inv1(18)]
                    ` inv2 (s_invocationOp'(i \<mapsto> GetUser user)) (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
                    use_inv3'[OF `inv3 s_calls' s_happensBefore'`]
                     upd_c1 upd_c2 upd_c3
                  by (auto simp add: inv2_def fun_upd_same  if_distrib_eq split: if_splits, blast)

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
