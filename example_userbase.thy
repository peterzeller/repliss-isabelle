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
instantiation userDataOp ::  valueType begin
definition "uniqueIds_userDataOp x \<equiv> 
  case x of 
     Name x \<Rightarrow> uniqueIds x
   | Mail x \<Rightarrow> uniqueIds x"

lemma [simp]: "uniqueIds (Name x) = uniqueIds x"
  "uniqueIds (Mail x) = uniqueIds x"
  by (auto simp add: uniqueIds_userDataOp_def)

definition [simp]: "default_userDataOp = Mail default"

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
    (c_calls write \<triangleq> Call (NestedOp u upd) Undef)
  \<and> (c_calls delete \<triangleq> Call (DeleteKey u) Undef)
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

  show "queries_cannot_guess_ids (querySpec progr)"
  proof (simp add: progr_def crdtSpec_def, standard)
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
        proof (fuzzy_rule execution_s_check_sound2)



          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: RegisterUser procedures_def )

          show "localState S i \<triangleq> registerUser_impl (String name) (String mail)"
            by (auto simp add: RegisterUser procedures_def )

          note registerUser_impl_def[simp]




          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin
            s_knownIds s_invocationOp s_invocationRes {} {} {} [] None True
            (registerUser_impl (String name) (String mail))"
            if "s_invocationOp i = invocationOp S i"
              and "s_invocationRes i = None"
            for s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "AtCommit" "AtReturn" )
            case (AtCommit v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)

            find_theorems uid_is_private

            have my_invoc[simp]: "s_invocationOp' i \<triangleq> RegisterUser name mail"
              by (simp add: AtCommit that(1) RegisterUser)


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
              from `inv3 s_calls' s_happensBefore'`
              show ?case
                by (auto simp add: inv3_def `c \<noteq> ca` updateHb_cases in_sequence_cons inv3(19) v_no_delete2')

            qed




          next
            case (AtReturn v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            then show ?case
              apply (auto simp add: inv_def)
              apply (auto simp add: inv1_def)
              apply (metis RegisterUser \<open>invocationOp S i \<triangleq> proc\<close> option.inject proc.distinct(5) that(1))
              apply (metis RegisterUser \<open>invocationOp S i \<triangleq> proc\<close> option.inject proc.distinct(5) that(1))
              done
          qed

          show "initialStates' progr i = initialStates progr i"
            by (simp add: initialStates'_same)
        qed
      qed

    next
      case (UpdateMail x21 x22)
      then show ?thesis sorry
    next
      case (RemoveUser x3)
      then show ?thesis sorry
    next
      case (GetUser x4)
      then show ?thesis sorry
    qed
  qed
qed

end
