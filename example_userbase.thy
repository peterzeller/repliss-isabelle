theory example_userbase
  imports 
    program_verification_tactics
    impl_language
    crdt_specs
    unique_ids
    program_proof_rules
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
    exists \<leftarrow> call (KeyExists u);  
    (if exists = Bool True then do {
      call (DeleteKey u)
    } else skip)
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

term "toImpl (registerUser_impl (String name) (String mail))"

abbreviation "toImpl2 x \<equiv> (x, toImpl)" 

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
     UpdateMail u _ \<Rightarrow> {to_nat (UserId u)}
   | RemoveUser u  \<Rightarrow> {to_nat (UserId u)}
   | GetUser u  \<Rightarrow> {to_nat (UserId u)}
   | RegisterUser _ _ \<Rightarrow> {}"

lemma [simp]:
  "uniqueIds (UpdateMail u x) = {to_nat (UserId u)}"
  "uniqueIds (RemoveUser u ) = {to_nat (UserId u)}"
  "uniqueIds (GetUser u ) = {to_nat (UserId u)}"
  "uniqueIds (RegisterUser x y) = {}"
  by (auto simp add: uniqueIds_proc_def)

definition [simp]: "default_proc \<equiv> RegisterUser [] []"

instance by (standard, auto)
end


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
  \<longrightarrow> c_calls c \<triangleq> Call (DeleteKey (UserId u)) Undef"

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





lemma uniqueId_no_nested: "x \<in> uniqueIds uid \<Longrightarrow> x = (to_nat (uid :: val))"
  by (auto simp add: uniqueIds_val_def split: val.splits)

lemma uniqueId_no_nested2: "x \<in> uniqueIds uid \<longleftrightarrow> (\<exists>u. x = to_nat (UserId u) \<and> uid = UserId u)"
  by (auto simp add: uniqueIds_val_def split: val.splits)

method show_procedures_cannot_guess_ids = 
  (((auto simp add: newId_def bind_def atomic_def beginAtomic_def call_def skip_def endAtomic_def return_def 
        uniqueIds_mapOp_def uniqueIds_userDataOp_def uniqueIds_registerOp_def uniqueIds_val_def
        split: if_splits)[1])?;
    ((rule procedure_cannot_guess_ids.intros, force); show_procedures_cannot_guess_ids?)?)


lemma progr_wf[simp]: "program_wellFormed progr"
proof (auto simp add: program_wellFormed_def)
  show "procedures_cannot_guess_ids procedures"
  proof (auto simp add: procedures_cannot_guess_ids_def procedures_def uniqueIds_proc_def split: proc.splits)
    show "\<And>n m uids. procedure_cannot_guess_ids uids (registerUser_impl (String n) (String m)) toImpl"
      by (auto simp add: registerUser_impl_def, show_procedures_cannot_guess_ids  )

    show "\<And>u m uids. procedure_cannot_guess_ids (insert (to_nat (UserId u)) uids) (updateMail_impl (UserId u) (String m)) toImpl"
      by (auto simp add: updateMail_impl_def, show_procedures_cannot_guess_ids  )

    show "\<And>u uids. procedure_cannot_guess_ids (insert (to_nat (UserId u)) uids) (removeUser_impl (UserId u)) toImpl"
      by (auto simp add: removeUser_impl_def, show_procedures_cannot_guess_ids  )
    show "\<And>u uids. procedure_cannot_guess_ids (insert (to_nat (UserId u)) uids) (getUser_impl (UserId u)) toImpl"
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

lemma infinite_if_mappable_to_nat:
  assumes mapping: "\<And>n::nat. \<exists>x\<in>S. f x \<ge> n"
  shows "infinite S"
proof auto
  assume "finite S"
  hence "finite (f ` S)"
    by force

  define m where "m \<equiv> Max (f ` S)"

  from mapping[where n="Suc m"] obtain x where
    "x\<in>S" and "f x \<ge> Suc m"
    by auto

  have "f x \<in> (f ` S)"
    using \<open>x \<in> S\<close> by blast

  have "f x > m"
    using Suc_le_eq \<open>Suc m \<le> f x\<close> by blast
  hence "f x > Max (f ` S)"
    using m_def by blast
  thus False
    using Max_ge \<open>f x \<in> f ` S\<close> \<open>finite (f ` S)\<close> leD by blast
qed





lemma isUserId_infinite[simp]: "infinite (Collect isUserId)"
proof (rule infinite_if_mappable_to_nat)
  show "\<exists>x\<in>Collect isUserId. n \<le> (case x of UserId n \<Rightarrow> nat n)" for n
    by (rule bexI[where x="UserId (int n)"],
        auto simp add: isUserId_def)
qed



lemma invariant_progr[simp]: "invariant progr = example_userbase.inv"
  by (auto simp add: progr_def)

method unfold_invs_p = (((subst(asm) inv_def)+)?; (elim conjE)?)?

theorem userbase_correct: "programCorrect progr"
proof M_show_programCorrect
  print_nested_cases

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
                by (meson AtCommit(12) uid_is_private'_def)

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

              from `inv1 s_invocationOp' s_invocationRes'
                (invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def)


            next
              case inv2
              from `inv2 s_invocationOp' (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
              show ?case
                apply (auto simp add: inv2_def)
                   apply (auto simp add: map_update_all_get i_callOriginI_h_simp)
                apply (auto simp add: i_callOriginI_h_update_to3 split: if_splits)
                done 
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
              apply (auto simp add: inv1_def)
              done
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
          proof ((repliss_vcg; intro conjI impI; repliss_vcg?), goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn"  )
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            
            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3)
              case inv1
              
              from `inv1 s_invocationOp' s_invocationRes'(invocation_happensBeforeH (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_happensBefore')`
              show ?case
                by (auto simp add: inv1_def) 

            next
              case inv2
              from `inv2 s_invocationOp' (i_callOriginI_h s_callOrigin' s_transactionOrigin') s_calls'`
              show ?case
               using `c \<noteq> ca` by (auto simp add: inv2_def i_callOriginI_h_update_to3)
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
                      by (auto simp add: updateHb_cases in_sequence_cons inv3(13) d0[symmetric])

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
                by (auto simp add: inv_def inv1_def) 
            next
              case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)

              


              
              from NotExists_AtCommit
              show ?case 
                by (auto simp add: inv_def inv1_def inv2_def inv3_def 
                      i_callOriginI_h_update_to3 map_update_all_get updateHb_single)

            next
              case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
              then show ?case 
                by (auto simp add: inv_def inv1_def) 
            qed
          qed
        qed

    next
      case (RemoveUser user)
      then show ?thesis sorry
    next
      case (GetUser user)
      then show ?thesis sorry
    qed
  qed
qed

end
