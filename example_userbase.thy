theory example_userbase
  imports 
    program_verification_tactics
    impl_language
    "HOL-Library.Countable"
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

definition inv1 :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv1 ctxt \<equiv> \<forall>r g u g_res.
    invocationOp ctxt r \<triangleq> RemoveUser u
  \<longrightarrow> invocationOp ctxt g \<triangleq> GetUser u
  \<longrightarrow> (r,g) \<in> invocation_happensBefore ctxt
  \<longrightarrow> invocationRes ctxt g \<triangleq> g_res
  \<longrightarrow> g_res = NotFound"

definition inv2 :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv2 ctxt \<equiv> \<forall>u i c.
    invocationOp ctxt i \<triangleq> RemoveUser u
  \<longrightarrow> i_callOriginI ctxt c \<triangleq> i
  \<longrightarrow> calls ctxt c \<triangleq> Call (DeleteKey (UserId u)) Undef"

definition inv3 :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv3 ctxt \<equiv> \<not>(\<exists>write delete u upd.
    (calls ctxt write \<triangleq> Call (NestedOp u upd) Undef)
  \<and> (calls ctxt delete \<triangleq> Call (DeleteKey u) Undef)
  \<and> (delete, write) \<in> happensBefore ctxt
  )"

definition inv :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> inv1 ctxt \<and> inv2 ctxt \<and> inv3 ctxt"

lemma show_inv[intro]:
  assumes "inv1 S" and "inv2 S" and "inv3 S"
  shows "inv S"
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


lemma progr_wf: "program_wellFormed progr"
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


lemma no_more_invoc:
  assumes steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"
and ls: "localState S i \<noteq> None"
and wf: "state_wellFormed S"
shows "(AInvoc p, t) \<notin> set trace"
proof -

  from ls have no_invoc: "invocationOp S (fst (i, trace)) \<noteq> None"
    by (simp add: wf wf_localState_to_invocationOp)


  have "(AInvoc p, t) \<notin> set (snd (i, trace))"
  using steps no_invoc
proof (induct rule: steps_s.induct)
case (steps_s_refl S s)
  then show ?case 
    by auto

next
  case (steps_s_step S s tr S' a S'')
  then show ?case 
    by (auto simp add: step_s.simps has_invocationOp_forever)
qed


lemma invariant_progr[simp]: "invariant progr = example_userbase.inv"
      by (auto simp add: progr_def)

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
    find_theorems name: show_P

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
          using show_P.proc_impl
          apply (auto simp add: RegisterUser procedures_def registerUser_impl_def)
          apply (rule execution_s_check_sound; simp?)

          find_theorems  execution_s_correct 

      qed

      then show ?thesis sorry
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
      case (case_registerUser name mail)

      show " procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation

        show ?case 
          using show_P.invariant_pre case_registerUser
          by (auto simp add: show_P.progr_def inv_def inv1_def inv2_def inv3_def invContextH2_simps show_P.Si_def)
      next
        case execution

        have todo1[simp]: "currentTransaction S_pre i = None"
          by (simp add: show_P.i_fresh show_P.wf_pre wellFormed_invoc_notStarted(1))


        show ?case
          apply (simp add: case_registerUser show_P registerUser_impl_def ) 

          apply (rule exI)
          apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )
          apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )
          apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )
           apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )
          apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )
          defer
           apply (subst funpow.simps(2), subst checkCorrect2F_def, auto simp add: case_registerUser show_P registerUser_impl_def  )

(* TODO should be possible to do some nice syntax directed rules now *)

          sorry
      qed


    next
      case (case_updateMail u mail)

      show " procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        then show ?case 
          using show_P.invariant_pre case_updateMail
          by (auto simp add: show_P.progr_def inv_def inv1_def inv2_def inv3_def invContextH2_simps show_P.Si_def)

      next
        case execution
        then show ?case sorry
      qed

        

    next
      case (case_removeUser u)
       show " procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        then show ?case 
          using show_P.invariant_pre case_removeUser
        apply (auto simp add: show_P.progr_def inv_def inv1_def inv2_def inv3_def invContextH2_simps show_P.Si_def)
        apply (simp add: new_invocation_cannot_happen_before show_P.i_fresh show_P.wf_pre)
        using i_callOriginI_notI2 show_P.i_fresh show_P.wf_pre by blast


      next
        case execution
        then show ?case sorry
      qed

    next
      case (case_get_User u)
       show " procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        then show ?case 
        using show_P.invariant_pre case_get_User
        apply (auto simp add: show_P.progr_def inv_def inv1_def inv2_def inv3_def invContextH2_simps show_P.Si_def)
        using new_invocation_cannot_happen_after show_P.i_fresh show_P.wf_pre by blast

      next
        case execution
        then show ?case sorry
      qed

    qed
  qed
qed


(*old proof *)

(*


theorem userbase_correct: "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect)
  have [simp]: "invariant progr = inv" by (simp add: progr_def)

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)

  subsection \<open>Initial state\<close>

  text \<open>Show that the initial state satisfies the invariant\<close>
  show "invariant_all' (repliss_sem.initialState progr)"
    by (auto simp add: initialState_def invContextH2_happensBefore  inv_def inv1_def inv2_def inv3_def invContextH_def invContextH2_i_invocationRes invContextH2_i_invocationOp)
    

  subsection \<open>Initial state of procedure invocations\<close>

  text \<open>Show that the initial state of procedure invocations satisfies the invariant.\<close>
  show "\<And>S i. S \<in> initialStates' progr i \<Longrightarrow> invariant_all' S"
    apply (subst(asm) initialStates'_def)
  proof auto

    show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (procName, args))) (invocationRes S'))" (is ?inv)
      if i0: "prog S' = progr"
        and i1: "procedures procName args \<triangleq> (initState, impl)"
        and i2: "uniqueIdsInList args \<subseteq> knownIds S'"
        and old_inv: "example_userbase.inv (invContext' S')"
        and i4: "state_wellFormed S'"
        and i5: "invocationOp S' i = None"
        and i6: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
      for  i S' procName args initState impl
      using i1 proof (subst(asm) procedure_cases2, auto)

      text \<open>We consider the initial state for each procedure individually:\<close>

      paragraph \<open>Case registerUser\<close>
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (registerUser, [String name, String mail]))) (invocationRes S'))"
        if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
          and c1: "procName = registerUser"
          and c2: "args = [String name, String mail]"
          and c3: "impl = registerUserImpl"
          and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
        for  name mail
        using old_inv
        by (auto simp add: inv_def inv1_def inv2_def inv3_def invContextH2_simps)


      paragraph \<open>Case updateMail\<close>
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (updateMail, [UserId u, String mail]))) (invocationRes S'))"
        if c0: "procedures updateMail [UserId u, String mail] \<triangleq> (lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>, updateMailImpl)"
          and c1: "procName = updateMail"
          and c2: "args = [UserId u, String mail]"
          and c3: "impl = updateMailImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>"
        for  u mail
        using old_inv
        by (auto simp add: inv_def inv1_def inv2_def inv3_def invContextH2_simps)

      paragraph \<open>Case removeUser\<close>
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u]))) (invocationRes S'))"
        if c0: "procedures removeUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, removeUserImpl)"
          and c1: "procName = removeUser"
          and c2: "args = [UserId u]"
          and c3: "impl = removeUserImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
        for  u
      proof 
        show "inv1 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
          using old_inv
          apply (auto simp add: inv_def inv1_def invContextH2_simps)[1]
          using i4 i5 new_invocation_cannot_happen_before by blast


        show "inv2 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
          using old_inv
          apply (auto simp add: inv_def inv2_def)
          using i4 i5 wf_no_invocation_no_origin  by (auto simp add: i_callOriginI_h_def invContextH2_simps split: option.splits if_splits)



        show "inv3 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
          using old_inv
          by (auto simp add: inv_def inv3_def invContextH2_simps)
      qed


      paragraph \<open>Case getUser\<close>
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u]))) (invocationRes S'))"
        if c0: "procedures getUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, getUserImpl)"
          and c1: "procName = getUser"
          and c2: "args = [UserId u]"
          and c3: "impl = getUserImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
        for  u
      proof

        from old_inv
        show "inv1 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
          apply (auto simp add: inv_def inv1_def invContextH2_simps)
          using i4 i5 new_invocation_cannot_happen_after by blast

        from old_inv
        show "inv2 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
          by (auto simp add: inv_def inv2_def invContextH2_simps)

        from old_inv
        show "inv3 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
          by (auto simp add: inv_def inv3_def invContextH2_simps)
      qed
    qed
  qed

  subsection \<open>We check the implementation using the checkCorrect2F function. 
       This basically checks the implementation up to the given bound.
       We have to show that there exists a bound such that all reachable states are covered and proven correct.\<close>
  show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    if c0: "S \<in> initialStates' progr i"
    for  S i

    text \<open>We unfold the definition of initial states.\<close>
    using c0  apply (subst(asm) initialStates'_def)
  proof auto


    show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>, i)"
      if S_def: "S = Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>"
        and prog_Sa: "prog Sa = progr"
        and procedures: "procedures procName args \<triangleq> (initState, impl)"
        and uniqueIds_args: "uniqueIdsInList args \<subseteq> knownIds Sa"
        and inv_Sa: "example_userbase.inv (invContext' Sa)"
        and Sa_wf: "state_wellFormed Sa"
        and invoc_Sa: "invocationOp Sa i = None"
        and transactions_Sa: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"
        and transactionOriginSa: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
      for  Sa procName args initState impl
      text \<open>We consider the case for each procedure separately:\<close>
      using procedures proof (subst(asm) procedure_cases2, auto)

      have [simp]: "currentTransaction Sa i = None"
        by (simp add: Sa_wf invoc_Sa wellFormed_invoc_notStarted(1))

\<comment> \<open>ony unfold definitions, when needed for evaluation:\<close>
      have h1[simp]:  "S' ::= S \<Longrightarrow> (currentProc S' i \<triangleq> x) \<longleftrightarrow> (currentProc S i \<triangleq> x)" for S' S i x  by (auto simp add: Def_def)
      have h2[simp]: "S' ::= S \<Longrightarrow>  ls_pc (the (localState S' i)) = ls_pc (the (localState S i))" for S' S i by (auto simp add: Def_def)
      have h3[simp]: "S' ::= S \<Longrightarrow>  (currentTransaction S' i = None) \<longleftrightarrow> (currentTransaction S i = None)" for S' S i by (auto simp add: Def_def)



      from \<open> example_userbase.inv (invContext' Sa)\<close>
      have inv1_Sa: "inv1 (invContext' Sa)"
        and inv2_Sa: "inv2 (invContext' Sa)"
        and inv3_Sa: "inv3 (invContext' Sa)"
        by (auto simp add: inv_def)


      paragraph \<open>Case register User:\<close>
      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>), currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail]))\<rparr>, i)"
        if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
          and c1: "procName = registerUser"
          and c2: "args = [String name, String mail]"
          and c3: "impl = registerUserImpl"
          and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
        for  name mail
        text \<open>We start by unrolling the implementation.\<close>
        apply (rule_tac x="10" in exI)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
         defer
         apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def invContextH2_simps split: localAction.splits option.splits)
      proof (unfold Def_def)
        print_cases

        text \<open>Check invariant at end of invocId:\<close>
          (*
fix uid S' t S'a newTxns S'' vis' ls x2 c res S'b vis'a hb' x2a ca resa S'c vis'b hb'a x2b S'd S'e
assume a0: "isUserId uid"
   and a1: "generatedIds Sa uid = None"
   and a2: "uniqueIds uid = {uid}"
   and a3: "S' = Sa\<lparr>currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail])),                   localState := localState Sa(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = uid, ls_name = name, ls_mail = mail, ls_exists = False\<rparr>), generatedIds := generatedIds Sa(uid \<mapsto> i)\<rparr>"
   and a4: "localState S' i \<triangleq> ls"
   and a5: "transactionStatus S' t = None"
   and a6: "prog S'a = prog S'"
   and a7: "invariant (prog S') (invContext' S'a)"
   and a8: "\<forall>tx. transactionStatus S'a tx \<noteq> Some Uncommitted"
   and a9: "state_wellFormed S'a"
   and a10: "state_wellFormed S''"
   and a11: "state_monotonicGrowth S' S'a"
   and a12: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S'a t \<triangleq> i"
   and a13: "localState S'a i \<triangleq> ls"
   and a14: "currentProc S'a i \<triangleq> registerUserImpl"
   and a15: "currentTransaction S'a i = None"
   and a16: "visibleCalls S' i \<triangleq> {}"
   and a17: "visibleCalls S'a i \<triangleq> {}"
   and a18: "vis' = callsInTransaction S'a newTxns \<down> happensBefore S'a"
   and a19: "newTxns \<subseteq> dom (transactionStatus S'a)"
   and a20: "consistentSnapshot S'a vis'"
   and a21: "transactionStatus S'a t = None"
   and a22: "\<forall>c. callOrigin S'a c \<noteq> Some t"
   and a23: "transactionOrigin S'a t = None"
   and a24: "S'' = S'a\<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'a(t \<mapsto> i), currentTransaction := currentTransaction S'a(i \<mapsto> t),                     localState := localState S'a(i \<mapsto> ls\<lparr>ls_pc := 2\<rparr>), visibleCalls := visibleCalls S'a(i \<mapsto> vis')\<rparr>"
   and a25: "currentTransaction S'' i \<triangleq> x2"
   and a26: "calls S'' c = None"
   and a27: "querySpec progr users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] (getContextH (calls S'') (happensBefore S'') (Some vis')) res"
   and a28: "visibleCalls S'' i \<triangleq> vis'"
   and a29: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
   and a30: "hb' = updateHb (happensBefore S'') vis' [c]"
   and a31: "S'b = S''\<lparr>localState := localState S''(i \<mapsto> the (localState S'' i)\<lparr>ls_pc := 3\<rparr>),                     calls := calls S''(c \<mapsto> Call users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] res), callOrigin := callOrigin S''(c \<mapsto> x2),                     visibleCalls := vis'a, happensBefore := hb'\<rparr>"
   and a32: "currentTransaction S'b i \<triangleq> x2a"
   and a33: "calls S'b ca = None"
   and a34: "querySpec progr users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))] (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) resa"
   and a35: "visibleCalls S'b i \<triangleq> insert c vis'"
   and a36: "vis'b = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
   and a37: "hb'a = updateHb (happensBefore S'b) (insert c vis') [ca]"
   and a38: "S'c = S'b\<lparr>localState := localState S'b(i \<mapsto> the (localState S'b i)\<lparr>ls_pc := 4\<rparr>),                     calls := calls S'b(ca \<mapsto> Call users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))] resa), callOrigin := callOrigin S'b(ca \<mapsto> x2a),                     visibleCalls := vis'b, happensBefore := hb'a\<rparr>"
   and a39: "currentTransaction S'c i \<triangleq> x2b"
   and a40: "S'd = S'c\<lparr>localState := localState S'c(i \<mapsto> the (localState S'c i)\<lparr>ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S'c)(i := None),                     transactionStatus := transactionStatus S'c(x2b \<mapsto> Committed)\<rparr>"
   and a41: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"
   and a42: "example_userbase.inv (invContext' S'd)"
   and a43: "S'e = S'd\<lparr>localState := (localState S'd)(i := None), currentProc := (currentProc S'd)(i := None), visibleCalls := (visibleCalls S'd)(i := None),                     invocationRes := invocationRes S'd(i \<mapsto> ls_u (the (localState S'd i))), knownIds := knownIds S'd \<union> uniqueIds (ls_u (the (localState S'd i)))\<rparr>"
   and a44: "\<forall>t. transactionStatus S'e t \<noteq> Some Uncommitted"

show "example_userbase.inv (invContext' S'e)"

*)



        fix uid S' t S'a newTxns S'' vis' ls x2 c res S'b vis'a hb' x2a ca resa S'c vis'b hb'a x2b S'd
        assume a0: "generatedIds Sa uid = None"
          and isUserId: "isUserId uid"
          and uniqueIds_uid1: "uniqueIds uid = {uid}"
          and S'_def: "S' = Sa         \<lparr>currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),            invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail])),            localState := localState Sa(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = uid, ls_name = name, ls_mail = mail, ls_exists = False\<rparr>), generatedIds := generatedIds Sa(uid \<mapsto> i)\<rparr>"
          and a2: "localState S' i \<triangleq> ls"
          and a3: "transactionStatus S' t = None"
          and a4: "prog S'a = prog S'"
          and old_inv: "invariant (prog S') (invContext' S'a)"
          and a6: "\<forall>tx. transactionStatus S'a tx \<noteq> Some Uncommitted"
          and S'a_wf: "state_wellFormed S'a"
          and S''_wf: "state_wellFormed S''"
          and S'a_mono: "state_monotonicGrowth i S' S'a"
          and tranactionOriginUnchanged: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S'a t \<triangleq> i"
          and a10: "localState S'a i \<triangleq> ls"
          and a11: "currentProc S'a i \<triangleq> registerUserImpl"
          and a12: "currentTransaction S'a i = None"
          and a13: "visibleCalls S' i \<triangleq> {}"
          and a14: "visibleCalls S'a i \<triangleq> {}"
          and a15: "vis' = callsInTransaction S'a newTxns \<down> happensBefore S'a"
          and a16: "newTxns \<subseteq> dom (transactionStatus S'a)"
          and a17: "consistentSnapshot S'a vis'"
          and a18: "transactionStatus S'a t = None"
          and t_origin: "\<forall>c. callOrigin S'a c \<noteq> Some t"
          and a20: "transactionOrigin S'a t = None"
          and S''_def: "S'' = S'a         \<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'a(t \<mapsto> i), currentTransaction := currentTransaction S'a(i \<mapsto> t),            localState := localState S'a(i \<mapsto> ls\<lparr>ls_pc := 2\<rparr>), visibleCalls := visibleCalls S'a(i \<mapsto> vis')\<rparr>"
          and a22: "currentTransaction S'' i \<triangleq> x2"
          and calls_S'': "calls S'' c = None"
          and a24: "querySpec progr users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] (getContextH (calls S'') (happensBefore S'') (Some vis')) res"
          and visibleCalls_S'': "visibleCalls S'' i \<triangleq> vis'"
          and a26: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
          and hb'_def: "hb' = updateHb (happensBefore S'') vis' [c]"
          and S'b_def: "S'b = S''         \<lparr>localState := localState S''(i \<mapsto> the (localState S'' i)\<lparr>ls_pc := 3\<rparr>),            calls := calls S''(c \<mapsto> Call users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] res), callOrigin := callOrigin S''(c \<mapsto> x2),            visibleCalls := vis'a, happensBefore := hb'\<rparr>"
          and a29: "currentTransaction S'b i \<triangleq> x2a"
          and a30: "calls S'b ca = None"
          and a31: "querySpec progr users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))]          (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) resa"
          and a32: "visibleCalls S'b i \<triangleq> insert c vis'"
          and a33: "vis'b = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
          and hb'a_def: "hb'a = updateHb (happensBefore S'b) (insert c vis') [ca]"
          and S'c_def: "S'c = S'b         \<lparr>localState := localState S'b(i \<mapsto> the (localState S'b i)\<lparr>ls_pc := 4\<rparr>),            calls := calls S'b(ca \<mapsto> Call users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))] resa),            callOrigin := callOrigin S'b(ca \<mapsto> x2a), visibleCalls := vis'b, happensBefore := hb'a\<rparr>"
          and a36: "currentTransaction S'c i \<triangleq> x2b"
          and S'd_def: "S'd = S'c         \<lparr>localState := localState S'c(i \<mapsto> the (localState S'c i)\<lparr>ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S'c)(i := None),            transactionStatus := transactionStatus S'c(x2b \<mapsto> Committed)\<rparr>"
          and a38: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"

        
        have invocationOp_unchanged: "invocationOp S'd = invocationOp S'a"
          by (subst S'd_def S'c_def S'b_def S''_def, simp)+

        find_theorems hb'

        text \<open>Same transcation TODO: remember in verification condition generation\<close>
        have[simp]: "x2a = t"
          using \<open>currentTransaction S'b i \<triangleq> x2a\<close> S''_def by (auto simp add: S'b_def)
        have [simp]: "x2 = t"
          using \<open>currentTransaction S'' i \<triangleq> x2\<close> S''_def by (auto simp add: S'b_def)

        have [simp]: "c \<noteq> ca" "ca \<noteq> c"
          using \<open>calls S'b ca = None\<close> by (auto simp add: S'b_def)


        have i_callOriginI_h_update:
          "(i_callOriginI_h (callOrigin S'd) (transactionOrigin S'd))
           = (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a))(c \<mapsto> i, ca \<mapsto> i)"
          apply (rule ext)
          apply (subst S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: i_callOriginI_h_simps t_origin)


        have happensBefore_update:
          "happensBefore S'd = updateHb (happensBefore S'a) vis' [c, ca]"
          apply (subst S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: updateHb_chain) \<comment> \<open>TODO add updateHb-chain lemma above\<close>


        then have happensBefore_update2:
          "happensBefore S'd = (happensBefore S'a \<union> (vis' \<times> {c, ca}) \<union> {(c, ca)})"
          by (auto simp add: updateHb_cons)


        from \<open>calls S'' c = None\<close>
        have "calls S'a c = None"
          by (auto simp add: S''_def)

        then have [simp]: "callOrigin S'a c = None"
          using S'a_wf wellFormed_callOrigin_dom3 by blast

        from S''_def \<open>calls S'b ca = None\<close> S'b_def
        have "calls S'a ca = None"
          by auto

        then have [simp]: "callOrigin S'a ca = None"
          by (simp add: S'a_wf wf_callOrigin_and_calls)

        have [simp]: "c \<notin> vis'"
          using S''_wf calls_S'' visibleCalls_S'' wellFormed_visibleCallsSubsetCalls_h(2) by fastforce
        have [simp]: "ca \<notin> vis'"
          using \<open>calls S'b ca = None\<close> \<open>visibleCalls S'b i \<triangleq> insert c vis'\<close>
            S''_wf visibleCalls_S'' wellFormed_visibleCallsSubsetCalls2
          by (auto simp add: S'b_def)


        from \<open>invocationOp Sa i = None\<close>
        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: Sa_wf wf_no_invocation_no_origin)


        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: transactionOriginSa)
        then have "transactionOrigin S' tx \<noteq> Some i" for tx
          by (simp add: S'_def)
        then have "transactionOrigin S'a tx \<noteq> Some i" for tx
          using tranactionOriginUnchanged by blast


        have invocationHb_update:
          "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'd) (transactionOrigin S'd)) (happensBefore S'd)
            = invocation_happensBeforeH (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a)) (happensBefore S'a)
             \<union> {i'. (\<forall>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i') }  \<times> {i}"
          apply (subst happensBefore_update)
          apply (rule invocation_happensBeforeH_update)
                apply (auto simp add: i_callOriginI_h_update split: option.splits)
                    apply (auto simp add: i_callOriginI_h_def split: option.splits)
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_l apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_l apply blast
          using \<open>\<And>tx. transactionOrigin S'a tx \<noteq> Some i\<close> by blast

        from \<open>prog Sa = progr\<close> 
        have "prog S' = progr"
          by (auto simp add: S'_def)


        from \<open>invariant (prog S') (invContext' S'a)\<close>
        have old_inv1: "inv1 (invContext' S'a)"
          by (simp add: \<open>prog S' = progr\<close> example_userbase.inv_def)

        have invocationRes_S'e: "invocationRes S'd i' \<triangleq> r" if "invocationRes S'a i' \<triangleq> r" for i' r
          using that state_wellFormed_no_result_when_running[OF S'a_wf a10] by (auto simp add: S'd_def S'c_def S'b_def S''_def)

        have invocationRes_S'e2: "invocationRes S'd = (invocationRes S'a)"
          by (auto simp add: S'd_def S'c_def S'b_def S''_def)

        have "invocationOp S' i \<triangleq> (registerUser, [String name, String mail])"
          by (auto simp add: S'_def)
        then have [simp]: "invocationOp S'a i \<triangleq> (registerUser, [String name, String mail])"
          using S'a_mono state_monotonicGrowth_invocationOp by blast
        then have [simp]: "invocationOp S'd i \<triangleq> (registerUser, [String name, String mail])"
          using invocationOp_unchanged by auto


        show "example_userbase.inv (invContext' S'd)"
        proof

          show "inv1 (invContext' S'd)"
            apply (auto simp add: inv1_def invocationOp_unchanged invocationHb_update)
            using old_inv1 by (auto simp add: inv1_def invocationRes_S'e2 invContextH2_simps invocationHb_update)



          have "inv2 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto


          then show "inv2 (invContext' S'd)"
            by (auto simp add: inv2_def invocationOp_unchanged S'd_def S'c_def S'b_def S''_def i_callOriginI_h_simps invContextH2_simps  split: option.splits if_splits)

          have "inv3 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto



          then show "inv3 (invContext' S'd)"
            apply (auto simp add: inv3_def invocationOp_unchanged invocationRes_S'e2 invContextH2_simps)
             apply (auto simp add: S'd_def split: if_splits)
             apply (auto simp add: S'c_def split: if_splits)
              apply (auto simp add: S'b_def split: if_splits)
               apply (auto simp add: S''_def split: if_splits)
               apply (auto simp add: hb'a_def updateHb_cons S'b_def hb'_def S''_def )
          proof -

            show "False"
              if c0: "\<forall>write delete u. calls S'a delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S'a write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S'a write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'a"
                and c1: "delete \<noteq> ca"
                and c2: "delete \<noteq> c"
                and c3: "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
                and c4: "res = Undef"
                and c5: "(delete, c) \<in> happensBefore S'a"
              for  delete
              using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_r that by blast

            find_theorems generatedIds name: "local."


            find_theorems ls
            from \<open>localState S' i \<triangleq> ls\<close>
            have "ls_u ls = uid"
              by (auto simp add: S'_def)


            from \<open>generatedIds Sa uid = None\<close> \<open>localState S' i \<triangleq> ls\<close>
            have "generatedIds Sa (ls_u ls) = None" 
              by (auto simp add: S'_def)



            from \<open>generatedIds Sa uid = None\<close>
            have "uid \<notin> knownIds Sa"
              using Sa_wf \<open>prog Sa = progr\<close> progr_wf wf_knownIds_subset_generatedIds2 by fastforce

            then have "uid \<notin> knownIds S'"
              by (simp add: S'_def)

            have "generatedIds S' uid \<triangleq> i"
              by (auto simp add: S'_def)

            from S'a_mono
            obtain tr
              where "S' ~~ tr \<leadsto>* S'a"
                and "\<forall>(i',a)\<in>set tr. i' \<noteq> i" 
                and "\<forall>i. (i, AFail) \<notin> set tr"
              by (auto simp add: state_monotonicGrowth_def)


            from \<open>S' ~~ tr \<leadsto>* S'a\<close> \<open>generatedIds S' uid \<triangleq> i\<close> \<open>uid \<notin> knownIds S'\<close>
            thm steps_private_uniqueIds_h
            have "uid \<notin> knownIds S'a  
              \<and> (\<forall>i' ls. localState S'a i' \<triangleq> ls \<longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> progr_uids ls) \<and> (\<forall>c opr args r. calls S'a c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"
              (* the uid is not written to the database and not known and it cannot be generated again, so
    it cannot become known in the monotonic growth step.
       TODO: this could be a general lemma in the framework for monotonicGrowth  *)

            proof (rule steps_private_uniqueIds_h)
              show " \<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
                apply (auto simp add: S'_def)
                using \<open>generatedIds Sa uid = None\<close> \<comment> \<open>id did not exist in Sa, so it cannot be in a call\<close>
                using Sa_wf \<open>prog Sa = progr\<close> progr_wf wf_onlyGeneratedIdsInCalls by force
              show "state_wellFormed S'"
                using S'a_mono state_monotonicGrowth_wf1 by blast

              show "\<forall>i. (i, AFail) \<notin> set tr"
                by (simp add: \<open>\<forall>i. (i, AFail) \<notin> set tr\<close>)

              show "\<forall>a. (i, a) \<notin> set tr"
                using \<open>\<forall>(i', a)\<in>set tr. i' \<noteq> i\<close> by blast

              show " program_wellFormed progr_uids (prog S')"
                by (simp add: \<open>prog S' = progr\<close> progr_wf)

              show "\<forall>i' ls. i' \<noteq> i \<longrightarrow> localState S' i' \<triangleq> ls \<longrightarrow> uid \<notin> progr_uids ls"
                apply (auto simp add: S'_def)
                using \<open>generatedIds Sa uid = None\<close> \<comment> \<open>id did not exist in Sa, so it cannot be in a local state\<close>
                using Sa_wf \<open>prog Sa = progr\<close> progr_wf wf_onlyGeneratedIdsInLocalState by fastforce
            qed
            then have S'a_uid_not_known: "uid \<notin> knownIds S'a"  
              and S'a_uid_not_in_ls:"\<And>i' ls. localState S'a i' \<triangleq> ls \<Longrightarrow> i' \<noteq> i \<Longrightarrow> uid \<notin> progr_uids ls"
              and S'a_uid_not_in_calls: "\<And>c opr args r. calls S'a c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
              by blast+


            have not_deleted: "calls S'a delete \<noteq> Some (Call users_remove [ls_u ls] Undef)" for delete
            proof (rule ccontr, simp)
              assume "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
              then have "uid \<notin> uniqueIdsInList [ls_u ls]"
                by (rule S'a_uid_not_in_calls)

              moreover have "uid \<in> uniqueIdsInList [ls_u ls]"
                by (auto simp add: uniqueIdsInList_def \<open>ls_u ls = uid\<close> uniqueIds_uid1)

              ultimately show  "False"
                by blast
            qed

            show x: "False"
              if c0: "\<forall>write delete u. calls S'a delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S'a write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S'a write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'a"
                and c1: "delete \<noteq> ca"
                and c2: "delete \<noteq> c"
                and c3: "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
                and c4: "res = Undef"
                and c5: "delete \<in> vis'"
              for  delete
              using not_deleted c3 by blast


            show "False"
              if c0: "resa = Undef"
                and c1: "\<forall>write delete u. calls S'a delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S'a write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S'a write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'a"
                and c2: "delete \<noteq> ca"
                and c3: "delete \<noteq> c"
                and c4: "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
                and c5: "(delete, ca) \<in> happensBefore S'a"
              for  delete
              using c5 S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_r by blast


            show "False"
              if c0: "resa = Undef"
                and c1: "\<forall>write delete u. calls S'a delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S'a write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S'a write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'a"
                and c2: "delete \<noteq> ca"
                and c3: "delete \<noteq> c"
                and c4: "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
                and c5: "delete \<in> vis'"
              for  delete
              using not_deleted c4 by blast
          qed
        qed


        fix uid S' t S'a newTxns S'' vis' ls x2 c res S'b vis'a hb' x2a ca resa S'c vis'b hb'a x2b S'd S'e
        assume a0: "generatedIds Sa uid = None"
          and isUserId: "isUserId uid"
          and uniqueIds_uid1: "uniqueIds uid = {uid}"
          and S'_def: "S' = Sa\<lparr>currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail])),                   localState := localState Sa(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = uid, ls_name = name, ls_mail = mail, ls_exists = False\<rparr>), generatedIds := generatedIds Sa(uid \<mapsto> i)\<rparr>"
          and a2: "localState S' i \<triangleq> ls"
          and a3: "transactionStatus S' t = None"
          and a4: "prog S'a = prog S'"
          and old_inv: "invariant (prog S') (invContext' S'a)"
          and a6: "\<forall>tx. transactionStatus S'a tx \<noteq> Some Uncommitted"
          and S'a_wf: "state_wellFormed S'a"
          and S''_wf: "state_wellFormed S''"
          and S'a_mono: "state_monotonicGrowth i S' S'a"
          and a10: "localState S'a i \<triangleq> ls"
          and a11: "currentProc S'a i \<triangleq> registerUserImpl"
          and a12: "currentTransaction S'a i = None"
          and a13: "visibleCalls S' i \<triangleq> {}"
          and a14: "visibleCalls S'a i \<triangleq> {}"
          and a15: "vis' = callsInTransaction S'a newTxns \<down> happensBefore S'a"
          and a16: "newTxns \<subseteq> dom (transactionStatus S'a)"
          and a17: "consistentSnapshot S'a vis'"
          and a18: "transactionStatus S'a t = None"
          and t_origin: "\<forall>c. callOrigin S'a c \<noteq> Some t"
          and a20: "transactionOrigin S'a t = None"
          and S''_def: "S'' = S'a         \<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'a(t \<mapsto> i),            currentTransaction := currentTransaction S'a(i \<mapsto> t), localState := localState S'a(i \<mapsto> ls\<lparr>ls_pc := 2\<rparr>), visibleCalls := visibleCalls S'a(i \<mapsto> vis')\<rparr>"
          and a22: "currentTransaction S'' i \<triangleq> x2"
          and calls_S'': "calls S'' c = None"
          and a24: "querySpec progr users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))]          (getContextH (calls S'') (happensBefore S'') (Some vis')) res"
          and visibleCalls_S'': "visibleCalls S'' i \<triangleq> vis'"
          and a26: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
          and hb'_def: "hb' = updateHb (happensBefore S'') vis' [c]"
          and S'b_def: "S'b = S''         \<lparr>localState := localState S''(i \<mapsto> the (localState S'' i)\<lparr>ls_pc := 3\<rparr>),            calls := calls S''(c \<mapsto> Call users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] res),            callOrigin := callOrigin S''(c \<mapsto> x2), visibleCalls := vis'a, happensBefore := hb'\<rparr>"
          and a29: "currentTransaction S'b i \<triangleq> x2a"
          and a30: "calls S'b ca = None"
          and a31: "querySpec progr users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))]          (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) resa"
          and a32: "visibleCalls S'b i \<triangleq> insert c vis'"
          and a33: "vis'b = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
          and hb'a_def: "hb'a = updateHb (happensBefore S'b) (insert c vis') [ca]"
          and S'c_def: "S'c = S'b         \<lparr>localState := localState S'b(i \<mapsto> the (localState S'b i)\<lparr>ls_pc := 4\<rparr>),            calls := calls S'b(ca \<mapsto> Call users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))] resa),            callOrigin := callOrigin S'b(ca \<mapsto> x2a), visibleCalls := vis'b, happensBefore := hb'a\<rparr>"
          and a36: "currentTransaction S'c i \<triangleq> x2b"
          and S'd_def: "S'd = S'c         \<lparr>localState := localState S'c(i \<mapsto> the (localState S'c i)\<lparr>ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S'c)(i := None),            transactionStatus := transactionStatus S'c(x2b \<mapsto> Committed)\<rparr>"
          and a38: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"
          and a39: "example_userbase.inv (invContext' S'd)"
          and S'e_def: "S'e = S'd         \<lparr>localState := (localState S'd)(i := None), currentProc := (currentProc S'd)(i := None), visibleCalls := (visibleCalls S'd)(i := None),            invocationRes := invocationRes S'd(i \<mapsto> ls_u (the (localState S'd i))), knownIds := knownIds S'd \<union> uniqueIds (ls_u (the (localState S'd i)))\<rparr>"
          and a41: "\<forall>t. transactionStatus S'e t \<noteq> Some Uncommitted"
          and tranactionOriginUnchanged: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S'a t \<triangleq> i"


        have invocationOp_unchanged: "invocationOp S'e = invocationOp S'a"
          by (subst S'e_def S'd_def S'c_def S'b_def S''_def, simp)+

        find_theorems hb'

        text \<open>Same transcation TODO: remember in verification condition generation\<close>
        have[simp]: "x2a = t"
          using \<open>currentTransaction S'b i \<triangleq> x2a\<close> S''_def by (auto simp add: S'b_def)
        have [simp]: "x2 = t"
          using \<open>currentTransaction S'' i \<triangleq> x2\<close> S''_def by (auto simp add: S'b_def)

        have [simp]: "c \<noteq> ca" "ca \<noteq> c"
          using \<open>calls S'b ca = None\<close> by (auto simp add: S'b_def)


        have i_callOriginI_h_update:
          "(i_callOriginI_h (callOrigin S'e) (transactionOrigin S'e))
           = (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a))(c \<mapsto> i, ca \<mapsto> i)"
          apply (rule ext)
          apply (subst S'e_def S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: i_callOriginI_h_simps t_origin split: option.splits if_splits)


        have happensBefore_update:
          "happensBefore S'e = updateHb (happensBefore S'a) vis' [c, ca]"
          apply (subst S'e_def S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: updateHb_chain) \<comment> \<open>TODO add updateHb-chain lemma above\<close>


        then have happensBefore_update2:
          "happensBefore S'e = (happensBefore S'a \<union> (vis' \<times> {c, ca}) \<union> {(c, ca)})"
          by (auto simp add: updateHb_cons)


        from \<open>calls S'' c = None\<close>
        have "calls S'a c = None"
          by (auto simp add: S''_def)

        then have [simp]: "callOrigin S'a c = None"
          by (simp add: S'a_wf wf_callOrigin_and_calls)

        from S''_def \<open>calls S'b ca = None\<close> S'b_def
        have "calls S'a ca = None"
          by auto

        then have [simp]: "callOrigin S'a ca = None"
          using S'a_wf wellFormed_callOrigin_dom3 by blast

        have [simp]: "c \<notin> vis'"
          using S''_wf calls_S'' visibleCalls_S'' wellFormed_visibleCallsSubsetCalls_h(2) by fastforce
        have [simp]: "ca \<notin> vis'"
          using \<open>calls S'b ca = None\<close> \<open>visibleCalls S'b i \<triangleq> insert c vis'\<close>
            S''_wf visibleCalls_S'' wellFormed_visibleCallsSubsetCalls2
          by (auto simp add: S'b_def)


        from \<open>invocationOp Sa i = None\<close>
        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: Sa_wf wf_no_invocation_no_origin)


        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: transactionOriginSa)
        then have "transactionOrigin S' tx \<noteq> Some i" for tx
          by (simp add: S'_def)
        then have "transactionOrigin S'a tx \<noteq> Some i" for tx
          using tranactionOriginUnchanged by blast


        have invocationHb_update:
          "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'e) (transactionOrigin S'e)) (happensBefore S'e)
            = invocation_happensBeforeH (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a)) (happensBefore S'a)
             \<union> {i'. (\<forall>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i') }  \<times> {i}"
          apply (subst happensBefore_update)
          apply (rule invocation_happensBeforeH_update)
                apply (auto simp add: i_callOriginI_h_update split: option.splits)
                    apply (auto simp add: i_callOriginI_h_def split: option.splits)
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_l apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_l apply blast
          using \<open>\<And>tx. transactionOrigin S'a tx \<noteq> Some i\<close> by blast

        from \<open>prog Sa = progr\<close> 
        have "prog S' = progr"
          by (auto simp add: S'_def)


        from \<open>example_userbase.inv (invContext' S'd)\<close>
        have old_inv1: "inv1 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        from \<open>example_userbase.inv (invContext' S'd)\<close>
        have old_inv2: "inv2 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        from \<open>example_userbase.inv (invContext' S'd)\<close>
        have old_inv3: "inv3 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        have [simp]: "invocationOp S'd i \<triangleq> (registerUser, [String name, String mail])" 
          by (auto simp add: S'd_def S'c_def S'b_def S''_def S'_def intro!: state_monotonicGrowth_invocationOp[OF \<open>state_monotonicGrowth i S' S'a\<close>])

        show "example_userbase.inv (invContext' S'e)"
        proof

          show "inv1 (invContext' S'e)"
            using old_inv1 by (auto simp add: S'e_def inv1_def invContextH2_simps)


          show "inv2 (invContext' S'e)"
            using old_inv2
            by (auto simp add: inv2_def S'e_def invContextH2_simps)

          show "inv3 (invContext' S'e)"
            using old_inv3 
            by (auto simp add: inv3_def S'e_def invContextH2_simps)
        qed
      qed

      paragraph \<open>Procedure updateMail\<close>



      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>), currentProc := currentProc Sa(i \<mapsto> updateMailImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (updateMail, [UserId u, String mail]))\<rparr>, i)"
        if c0: "procedures updateMail [UserId u, String mail] \<triangleq> (lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>, updateMailImpl)"
          and c1: "procName = updateMail"
          and c2: "args = [UserId u, String mail]"
          and c3: "impl = updateMailImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>"
        for  u mail
        text \<open>We start by unrolling the implementation.\<close>
      proof -
        show ?thesis
        proof (rule_tac x="15" in exI, rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)
          fix t S' newTxns S'' vis'
          assume a0: "transactionStatus Sa t = None"
            and a1: "prog S' = prog Sa"
            and a2: "invariant (prog Sa) (invContext' S')"
            and a3: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
            and S'_wf: "state_wellFormed S'"
            and S''_wf: "state_wellFormed S''"
            and S'_growth: "state_monotonicGrowth i          (Sa\<lparr>localState := localState Sa(i \<mapsto> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>), currentProc := currentProc Sa(i \<mapsto> updateMailImpl),                visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (updateMail, [UserId u, String mail]))\<rparr>)          S'"
            and a7: "\<forall>t. transactionOrigin Sa t \<triangleq> i = transactionOrigin S' t \<triangleq> i"
            and a8: "localState S' i \<triangleq> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>"
            and a9: "currentProc S' i \<triangleq> updateMailImpl"
            and a10: "currentTransaction S' i = None"
            and a11: "visibleCalls S' i \<triangleq> {}"
            and a12: "vis' = callsInTransaction S' newTxns \<down> happensBefore S'"
            and a13: "newTxns \<subseteq> dom (transactionStatus S')"
            and a14: "consistentSnapshot S' vis'"
            and a15: "transactionStatus S' t = None"
            and a16: "\<forall>c. callOrigin S' c \<noteq> Some t"
            and a17[simp]: "transactionOrigin S' t = None"
            and S''_def: "S'' = S'         \<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t),            localState := localState S'(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>), visibleCalls := visibleCalls S'(i \<mapsto> vis')\<rparr>"


          from \<open>invariant (prog Sa) (invContext' S')\<close>
          have "inv (invContext' S')"
            by (simp add: prog_Sa)
          then have old_inv1: "inv1 (invContext' S')"
            and old_inv2: "inv2 (invContext' S')"
            and old_inv3: "inv3 (invContext' S')"
            by (auto simp add: inv_def)

          have invocationOp_S'_i[simp]: "invocationOp S' i \<triangleq> (updateMail, [UserId u, String mail])"
            by (auto simp add: state_monotonicGrowth_invocationOp_i[OF S'_growth])

          have [simp]: "currentProc S'' i \<triangleq> updateMailImpl"
            by (auto simp add: S''_def a9)

          have [simp]: "localState S'' i \<triangleq> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>"
            by (auto simp add: S''_def)

          have [simp]: "currentTransaction S'' i \<triangleq> t" 
            by (auto simp add: S''_def)


          show "(checkCorrect2F ^^ 14) bot (progr, vis', S'', i)"
          proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)



            show "Ex (querySpec progr users_contains_key [UserId u] (getContext S'' i))"
              by (auto simp add: progr_def crdtSpec_def)
            fix c res_userExists S'a vis'a hb'
            assume b0: "calls S'' c = None"
              and userExists_query: "querySpec progr users_contains_key [UserId u] (getContextH (calls S'') (happensBefore S'') (Some vis')) res_userExists"
              and b2: "visibleCalls S'' i \<triangleq> vis'"
              and b3: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
              and hb'_def[simp]: "hb' = updateHb (happensBefore S'') vis' [c]"
              and S'a_def: "S'a = S''         \<lparr>localState := localState S''(i \<mapsto> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = res_userExists = Bool True\<rparr>),            calls := calls S''(c \<mapsto> Call users_contains_key [UserId u] res_userExists), callOrigin := callOrigin S''(c \<mapsto> t), visibleCalls := vis'a, happensBefore := hb'\<rparr>"


            have [simp]: "calls S' c = None" 
              using b0 by (auto simp add: S''_def)

            have [simp]: "currentProc S'a i \<triangleq> updateMailImpl"
              by (auto simp add: S'a_def a9)

            have [simp]: "localState S'a i \<triangleq> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = res_userExists = Bool True\<rparr>"
              by (auto simp add: S'a_def)

            have [simp]: "currentTransaction S'a i \<triangleq> t" 
              by (auto simp add: S'a_def)


            from userExists_query
            have userExists_query2: "crdtSpec users_contains_key [UserId u] (getContextH (calls S') (happensBefore S') (Some vis')) res_userExists"
              by (auto simp add: S''_def progr_def)
            then have userExists_query3:  
              "(res_userExists = Bool True) \<longleftrightarrow> (\<exists>cw. 
              (\<exists>v. calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_name_assign [UserId u, v] Undef
                 \<or> calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_mail_assign [UserId u, v] Undef)
              \<and> (\<forall>cr. calls (getContextH (calls S') (happensBefore S') (Some vis')) cr \<triangleq> Call users_remove [UserId u] Undef \<longrightarrow>
                           (cr, cw) \<in> happensBefore (getContextH (calls S') (happensBefore S') (Some vis'))))
"
              using that
              by (auto simp add: crdtSpec_def)


            show "(checkCorrect2F ^^ 13) bot (progr, insert c vis', S'a, i)"
            proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)

\<comment> \<open>Case 1: Result is True: the user exists so we execute the update in line 3\<close>
              fix S'b
              assume c0: "res_userExists = Bool True"
                and S'b_def: "S'b = S'a\<lparr>localState := localState S'a(i \<mapsto> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>)\<rparr>"

              have [simp]: "currentProc S'b i \<triangleq> updateMailImpl"
                by (auto simp add: S'b_def)

              have [simp]: "localState S'b i \<triangleq> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>"
                by (auto simp add: S'b_def)

              have [simp]: "currentTransaction S'b i \<triangleq> t" 
                by (auto simp add: S'b_def)

              show "(checkCorrect2F ^^ 12) bot (progr, insert c vis', S'b, i)"
              proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac ca res S'c vis'c hb'c)
                fix ca res S'c vis'c hb'c
                assume d0: "calls S'b ca = None"
                  and d1: "querySpec progr users_mail_assign [UserId u, String mail] (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) res"
                  and d2: "visibleCalls S'b i \<triangleq> insert c vis'"
                  and d3: "vis'c = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
                  and hb'c_def: "hb'c = updateHb (happensBefore S'b) (insert c vis') [ca]"
                  and S'c_def: "S'c = S'b         \<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>),            calls := calls S'b(ca \<mapsto> Call users_mail_assign [UserId u, String mail] res), callOrigin := callOrigin S'b(ca \<mapsto> t), visibleCalls := vis'c, happensBefore := hb'c\<rparr>"


                have [simp]: "ca \<noteq> c" and [simp]: "c \<noteq> ca" 
                  using \<open>calls S'b ca = None\<close>
                  by (auto simp add: S'b_def S'a_def)

                have [simp]: "calls S' ca = None" 
                  using d0 by (auto simp add: S'b_def S'a_def S''_def)


                have [simp]: "currentProc S'c i \<triangleq> updateMailImpl"
                  by (auto simp add: S'c_def)

                have [simp]: "localState S'c i \<triangleq> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>"
                  by (auto simp add: S'c_def)

                have [simp]: "currentTransaction S'c i \<triangleq> t" 
                  by (auto simp add: S'c_def)

                show "(checkCorrect2F ^^ 11) bot (progr, insert ca (insert c vis'), S'c, i)"
                proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'd)
                  fix S'd
                  assume S'd_def: "S'd = S'c
                      \<lparr>localState := localState S'c(i \<mapsto> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>),
                         currentTransaction := (currentTransaction S'c)(i := None), transactionStatus := transactionStatus S'c(t \<mapsto> Committed)\<rparr>"
                    and e1: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"


                  show "example_userbase.inv (invContext' S'd)"
                  proof 



                    show "inv1 (invContext' S'd)"
                    proof (auto simp add: inv1_def S'd_def S'c_def S'b_def S'a_def S''_def invContextH2_simps)

                      find_theorems "updateHb"

                      show "g_res = NotFound"
                        if c0: "invocationOp S' r \<triangleq> (removeUser, [u'])"
                          and c1: "invocationOp S' g \<triangleq> (getUser, [u'])"
                          and c2: "(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) hb'c"
                          and c3: "invocationRes S' g \<triangleq> g_res"
                        for  r g u' g_res
                      proof -

                        have [simp]: "r \<noteq> i" and [simp]: "g \<noteq> i"
                          using c0 c1 by auto
                        then have [simp]: "i \<noteq> r" and [simp]: "i \<noteq> g"
                          by blast+
                            \<comment> \<open>Alternatively, we could prove that they are not equal because there are no call in i and we need calls for i-happens-before\<close>


                        from c2 
                        obtain cx cy
                          where cx: "i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) cx \<triangleq> r"
                            and cy: "i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) cy \<triangleq> g"
                            and "r \<noteq> g"
                            and all_hb: "\<forall>cx cy.
                               i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) cx \<triangleq> r \<and>
                               i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) cy \<triangleq> g \<longrightarrow>
                             (cx, cy) \<in> hb'c"
                          by (auto simp add: invocation_happensBeforeH_def)

                        have [simp]: "cx \<noteq> cy" "cy \<noteq> cx"
                          using \<open>r \<noteq> g\<close> cx cy by auto


                        have [simp]: "calls S' c = None"
                          using \<open>calls S'' c = None\<close> by (simp add: S''_def)
                        then have [simp]: "callOrigin S' c = None"
                          using S'_wf wellFormed_callOrigin_dom2 by blast

                        have [simp]: "calls S' ca = None"
                          using \<open>calls S'b ca = None\<close> by (simp add: S''_def S'b_def S'a_def)
                        then have [simp]: "callOrigin S' ca = None"
                          by (simp add: S'_wf wellFormed_callOrigin_dom2)

                        have [simp]: "transactionOrigin S' t = None"
                          by (simp add: a17)


                        have cx': "i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> r"
                          using cx by (auto simp add: i_callOriginI_h_simps split: if_splits option.splits)

                        have cy': "i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> g"
                          using cy by (auto simp add: i_callOriginI_h_simps split: if_splits option.splits)

                        have "(r, g) \<in> invocation_happensBefore (invContext' S')"
                          using c2 apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def invContextH2_simps split: option.splits if_splits)
                          apply (drule_tac x=cx in spec)
                          apply auto
                          apply (drule_tac x=cy in spec)
                          apply (auto simp add: hb'c_def S'a_def updateHb_cons S'b_def S''_def)
                          done
                        then show ?thesis
                          using old_inv1[simplified inv1_def] c0 c1 c3 invContextH2_simps
                          by metis

                      qed
                    qed

                    show "inv2 (invContext' S'd)"
                      using old_inv2
                      apply (auto simp add: inv2_def S'd_def S'c_def S'b_def S'a_def S''_def invContextH2_simps)
                      by (auto simp add: i_callOriginI_h_simps split: if_splits)

                    from userExists_query3 and \<open>res_userExists = Bool True\<close>
                    obtain cw
                      where existsWrite: "(\<exists>v. calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_name_assign [UserId u, v] Undef
                           \<or> calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_mail_assign [UserId u, v] Undef)"
                        and writeNotOverridden: "\<And>crr. calls (getContextH (calls S') (happensBefore S') (Some vis')) crr \<triangleq> Call users_remove [UserId u] Undef \<Longrightarrow>
                           (crr, cw) \<in> happensBefore (getContextH (calls S') (happensBefore S') (Some vis'))"
                      by auto
                    find_theorems res_userExists

                    show "inv3 (invContext' S'd)"
                      using old_inv3
                      apply (auto simp add: hb'c_def updateHb_cons inv3_def S'd_def S'c_def S'b_def S'a_def S''_def invContextH2_simps)
                      using S'_wf \<open>calls S' ca = None\<close> wellFormed_happensBefore_calls_r apply blast
                    proof -

                      show "False"
                        if c0: "\<forall>write delete u. calls S' delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S' write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S' write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'"
                          and c1: "delete \<noteq> c"
                          and c2: "delete \<noteq> ca"
                          and c3: "calls S' delete \<triangleq> Call users_remove [UserId u] Undef"
                          and c4: "res = Undef"
                          and c5: "delete \<in> vis'"
                        for  delete
                      proof -
                        from c3
                        have c3': "calls (getContextH (calls S') (happensBefore S') (Some vis')) delete \<triangleq> Call users_remove [UserId u] Undef"
                          by (auto simp add: getContextH_def restrict_map_def c5)

                        thm writeNotOverridden
                        from writeNotOverridden[where crr3=delete, OF c3']
                        have "(delete, cw) \<in> happensBefore (getContextH (calls S') (happensBefore S') (Some vis'))"
                          by simp
                        then have "(delete, cw) \<in> happensBefore S'"
                          by (auto simp add: getContextH_def  restrict_relation_def)
                        then show False
                          by (smt c0 c3' existsWrite getContextH_def operationContext.simps(1) option.case(2) option.distinct(1) restrict_map_def)
                      qed
                    qed
                  qed

                  assume e2: "example_userbase.inv (invContext' S'd)"


                  from  e2 
                  have S'd_inv1: "inv1 (invContext' S'd)"
                    and S'd_inv2: "inv2 (invContext' S'd)"
                    and S'd_inv3: "inv3 (invContext' S'd)"
                    using example_userbase.inv_def by auto


                  have [simp]: "currentProc S'd i \<triangleq> updateMailImpl"
                    by (auto simp add: S'd_def)

                  have [simp]: "localState S'd i \<triangleq> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = True\<rparr>"
                    by (auto simp add: S'd_def)

                  have [simp]: "currentTransaction S'd i = None" 
                    by (auto simp add: S'd_def)

                  show "(checkCorrect2F ^^ 10) bot (progr, insert ca (insert c vis'), S'd, i)"
                  proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'e)
                    fix S'e
                    assume S'e_def: "S'e = S'd
                        \<lparr>localState := (localState S'd)(i := None), currentProc := (currentProc S'd)(i := None), visibleCalls := (visibleCalls S'd)(i := None),
                           invocationRes := invocationRes S'd(i \<mapsto> Undef)\<rparr>"
                      and f1: "\<forall>t. transactionStatus S'e t \<noteq> Some Uncommitted"

                    find_theorems invocationOp u
                    have [simp]: "invocationOp S'd i \<triangleq> (updateMail, [UserId u, String mail])"
                      by (auto simp add: S'd_def S'c_def S'b_def S'a_def S''_def state_monotonicGrowth_invocationOp_i[OF S'_growth, simplified])

                    show "example_userbase.inv (invContext' S'e)"
                    proof
                      show " inv1 (invContext' S'e)"
                        using S'd_inv1 by (auto simp add: S'e_def inv1_def invContextH2_simps)

                      show "inv2 (invContext' S'e)"
                        using S'd_inv2 by (auto simp add: S'e_def inv2_def invContextH2_simps)

                      show "inv3 (invContext' S'e)"
                        using S'd_inv3 by (auto simp add: S'e_def inv3_def invContextH2_simps)
                    qed
                  qed
                qed
              qed
            next \<comment> \<open>Case 2: The user does not exist -- we do not update the email and directly go to the return statement\<close>

              fix S'b
              assume res_userExists_false: "res_userExists \<noteq> Bool True"
                and S'b_def: "S'b = S'a\<lparr>localState := localState S'a(i \<mapsto> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>)\<rparr>"


              have [simp]: "currentProc S'b i \<triangleq> updateMailImpl"
                by (auto simp add: S'b_def)

              have [simp]: "localState S'b i \<triangleq> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>"
                by (auto simp add: S'b_def)

              have [simp]: "currentTransaction S'b i \<triangleq> t" 
                by (auto simp add: S'b_def)

              show "(checkCorrect2F ^^ 12) bot (progr, insert c vis', S'b, i)"
              proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def; rename_tac S'c)
                fix S'c
                assume S'c_def: "S'c = S'b             \<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>),                currentTransaction := (currentTransaction S'b)(i := None), transactionStatus := transactionStatus S'b(t \<mapsto> Committed)\<rparr>"
                  and d1: "\<forall>t. transactionStatus S'c t \<noteq> Some Uncommitted"

                thm old_inv1
                have [simp]: "invocationOp S'c i \<triangleq> (updateMail, [UserId u, String mail])"
                  by (auto simp add: S'c_def S'b_def S'a_def S''_def)

                show "example_userbase.inv (invContext' S'c)"
                proof
                  show " inv1 (invContext' S'c)"
                  proof (auto simp add: inv1_def S'c_def S'b_def S'a_def S''_def invContextH2_simps)



                    show "g_res = NotFound"
                      if c0: "invocationOp S' r \<triangleq> (removeUser, [u])"
                        and c1: "invocationOp S' g \<triangleq> (getUser, [u])"
                        and c2: "(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) (updateHb (happensBefore S') vis' [c])"
                        and c3: "invocationRes S' g \<triangleq> g_res"
                      for  r g u g_res
                      using c0 c1
                    proof (rule old_inv1[simplified inv1_def invContextH2_i_invocationRes invContextH2_i_invocationOp, rule_format])

                      from c0 have [simp]: "r \<noteq> i"
                        using invocationOp_S'_i by auto

                      from c1 have [simp]: "g \<noteq> i"
                        using invocationOp_S'_i by auto

                      have [simp]: "i \<noteq> r" and [simp]: "i \<noteq> g"
                        using \<open>r \<noteq> i\<close> \<open>g \<noteq> i\<close> by blast+


                      from c2
                      show "(r, g) \<in> invocation_happensBefore (invContext' S')"
                        apply (auto simp add:  invocation_happensBeforeH_def  i_callOriginI_h_def updateHb_cons invContextH2_simps split: option.splits if_splits)
                        by (metis S'_wf \<open>calls S' c = None\<close> a15 option.distinct(1) wellFormed_callOrigin_dom2 wellFormed_state_callOrigin_transactionStatus)

                      show "invocationRes S' g \<triangleq> g_res"
                        using c3 .
      
                    qed
                  qed
                  have no_co_t: "\<And>c. callOrigin S' c \<noteq> Some t"
                    by (simp add: a16)


                  show "inv2 (invContext' S'c)"
                    using old_inv2
                    apply (auto simp add: inv2_def S'c_def S'b_def S'a_def S''_def invContextH2_simps)
                    by (auto simp add: i_callOriginI_h_simps no_co_t)

                  show "inv3 (invContext' S'c)"
                    using old_inv3
                    by (auto simp add: inv3_def S'c_def S'b_def S'a_def S''_def updateHb_cons invContextH2_simps)
                qed

                have [simp]: "currentProc S'c i \<triangleq> updateMailImpl"
                  by (auto simp add: S'c_def)

                have [simp]: "localState S'c i \<triangleq> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = [], ls_mail = mail, ls_exists = False\<rparr>"
                  by (auto simp add: S'c_def)

                have [simp]: "currentTransaction S'c i = None" 
                  by (auto simp add: S'c_def)

                assume d2: "example_userbase.inv (invContext' S'c)"
                show "(checkCorrect2F ^^ 11) bot (progr, insert c vis', S'c, i)"
                proof (rule checkCorrect2F_step, auto simp add: updateMailImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def; rename_tac S'd)
                  fix S'd
                  assume S'd_def: "S'd = S'c             \<lparr>localState := (localState S'c)(i := None), currentProc := (currentProc S'c)(i := None), visibleCalls := (visibleCalls S'c)(i := None),                invocationRes := invocationRes S'c(i \<mapsto> Undef)\<rparr>"
                    and e1: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"

                  show "inv (invContext' S'd)"
                    using \<open>inv (invContext' S'c)\<close>
                    by  (auto simp add: inv_def inv1_def inv2_def inv3_def S'd_def invContextH2_simps)
                qed
              qed
            qed
          qed
        qed
      qed
      paragraph \<open>Procedure removeUser \<close>

      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_u := UserId u\<rparr>), currentProc := currentProc Sa(i \<mapsto> removeUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (removeUser, [UserId u]))\<rparr>, i)"
        if procedure_removeUser: "procedures removeUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, removeUserImpl)"
          and procName_def: "procName = removeUser"
          and args_def: "args = [UserId u]"
          and impl_def: "impl = removeUserImpl"
          and initState_def: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
        for  u
      proof (rule_tac x="15" in exI, rule checkCorrect2F_step, auto simp add: removeUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)
        fix t S' newTxns S'' vis'
        assume a0: "transactionStatus Sa t = None"
          and a1: "prog S' = prog Sa"
          and a2: "invariant (prog Sa) (invContext' S')"
          and a3: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
          and wf_S': "state_wellFormed S'"
          and wf_S'': "state_wellFormed S''"
          and S'_growth: "state_monotonicGrowth i          (Sa\<lparr>localState := localState Sa(i \<mapsto> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>), currentProc := currentProc Sa(i \<mapsto> removeUserImpl),                visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (removeUser, [UserId u]))\<rparr>)          S'"
          and no_transaction_in_i_Sa: "\<forall>t. transactionOrigin Sa t \<triangleq> i = transactionOrigin S' t \<triangleq> i"
          and a8: "localState S' i \<triangleq> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
          and currentProc_S': "currentProc S' i \<triangleq> removeUserImpl"
          and a10: "currentTransaction S' i = None"
          and a11: "visibleCalls S' i \<triangleq> {}"
          and a12: "vis' = callsInTransaction S' newTxns \<down> happensBefore S'"
          and a13: "newTxns \<subseteq> dom (transactionStatus S')"
          and a14: "consistentSnapshot S' vis'"
          and a15: "transactionStatus S' t = None"
          and no_call_in_t_S': "\<forall>c. callOrigin S' c \<noteq> Some t"
          and transactionOrigin_t_S': "transactionOrigin S' t = None"
          and S''_def: "S'' = S'         \<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t),            localState := localState S'(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>), visibleCalls := visibleCalls S'(i \<mapsto> vis')\<rparr>"

        have [simp]: "invocationOp S' i \<triangleq> (removeUser, [UserId u])"
          using state_monotonicGrowth_invocationOp_i[OF S'_growth ] by simp


        from \<open>invariant (prog Sa) (invContext' S')\<close>
        have inv1_S': "inv1 (invContext' S')"
          and inv2_S': "inv2 (invContext' S')"
          and inv3_S': "inv3 (invContext' S')"
          by (auto simp add: prog_Sa inv_def) 

        have [simp]: "currentProc S'' i \<triangleq> removeUserImpl"
          by (auto simp add: S''_def currentProc_S')

        have [simp]: "localState S'' i \<triangleq> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
          by (auto simp add: S''_def)

        have [simp]: "currentTransaction S'' i \<triangleq> t" 
          by (auto simp add: S''_def)

        show "(checkCorrect2F ^^ 14) bot (progr, vis', S'', i)"
        proof (rule checkCorrect2F_step, auto simp add: removeUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)

          show "Ex (querySpec progr users_remove [UserId u] (getContext S'' i))"
            by (auto simp add: progr_def crdtSpec_def)

          fix c res S'a vis'a hb'
          assume a0: "calls S'' c = None"
            and a1: "querySpec progr users_remove [UserId u] (getContextH (calls S'') (happensBefore S'') (Some vis')) res"
            and a2: "visibleCalls S'' i \<triangleq> vis'"
            and a3: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
            and hb'_def: "hb' = updateHb (happensBefore S'') vis' [c]"
            and S'a_def: "S'a = S''         \<lparr>localState := localState S''(i \<mapsto> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>), calls := calls S''(c \<mapsto> Call users_remove [UserId u] res),            callOrigin := callOrigin S''(c \<mapsto> t), visibleCalls := vis'a, happensBefore := hb'\<rparr>"

          have [simp]: "currentProc S'a i \<triangleq> removeUserImpl"
            by (auto simp add: S'a_def)

          have [simp]: "localState S'a i \<triangleq> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
            by (auto simp add: S'a_def)

          have [simp]: "currentTransaction S'a i \<triangleq> t" 
            by (auto simp add: S'a_def)

          show "(checkCorrect2F ^^ 13) bot (progr, insert c vis', S'a, i)"
          proof (rule checkCorrect2F_step, auto simp add: removeUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'b)
            fix S'b
            assume S'b_def: "S'b = S'a             \<lparr>localState := localState S'a(i \<mapsto> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>),                currentTransaction := (currentTransaction S'a)(i := None), transactionStatus := transactionStatus S'a(t \<mapsto> Committed)\<rparr>"
              and "\<forall>t. transactionStatus S'b t \<noteq> Some Uncommitted"

            from \<open>calls S'' c = None\<close>
            have "calls S' c = None"
              by (auto simp add: S''_def)
            then have [simp]: "callOrigin S' c = None"
              using S'_growth state_monotonicGrowth_wf2 wellFormed_callOrigin_dom3 by blast

            from \<open> transactionOrigin S' t = None\<close>
            have no_tx_in_i: "transactionOrigin S' x \<noteq> Some i" for x
              using no_transaction_in_i_Sa transactionOriginSa by blast

            have no_call_in_t_S'_h: "x\<noteq>t" if "callOrigin S' c \<triangleq> x" for c x
              using no_call_in_t_S' that by blast

            from \<open>calls S'' c = None\<close>
            have "calls S' c = None"
              by (simp add: S''_def)

            then have c_no_hb: "(c, c') \<notin> happensBefore S'" for c'
              using wf_S' wellFormed_happensBefore_calls_l by blast

            show "example_userbase.inv (invContext' S'b)"
            proof
              show "inv1 (invContext' S'b)"
              proof (auto simp add: inv1_def S'b_def S'a_def S''_def invContextH2_simps)




                show "g_res = NotFound"
                  if c0: "invocationOp S' r \<triangleq> (removeUser, [u])"
                    and c1: "invocationOp S' g \<triangleq> (getUser, [u])"
                    and c2: "(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) hb'"
                    and c3: "invocationRes S' g \<triangleq> g_res"
                  for  r g u g_res
                  using c0 c1
                proof (rule inv1_S'[simplified inv1_def invContextH2_i_invocationRes invContextH2_i_invocationOp, rule_format])

                  have [simp]: "g \<noteq> i"
                    using c1 by auto
                  then have [simp]: "i \<noteq> g" by blast

                  have "r\<noteq>i"
                  proof 
                    assume [simp]: "r = i"
                    text \<open>This case is not possible, as there cannot be any calls that happened after the new call c. \<close>






                    from \<open>(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) hb'\<close>
                    show False
                      apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def hb'_def updateHb_cons S''_def  split: option.splits if_splits)
                      by (auto simp add: no_tx_in_i no_call_in_t_S' no_call_in_t_S'_h c_no_hb)
                  qed
                  then have [simp]: "i\<noteq> r" and [simp]: "r \<noteq>i" by blast+





                  have h1: "i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) ca \<triangleq> r
                      \<longleftrightarrow> i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> r"
                    for ca
                    by (auto simp add: i_callOriginI_h_def no_call_in_t_S' split: option.splits)

                  have h2: "i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i)) ca \<triangleq> g
                      \<longleftrightarrow> i_callOriginI_h (callOrigin S') (transactionOrigin S') ca \<triangleq> g"
                    for ca
                    by (auto simp add: i_callOriginI_h_def no_call_in_t_S' split: option.splits)

                  have otherC: "c' \<noteq> c" if "callOrigin S' c' \<triangleq> x" for c' x
                    using that by auto


                  from c2
                  show "(r, g) \<in> invocation_happensBefore (invContext' S')"
                    apply (auto simp add: h1 h2 invocation_happensBeforeH_def hb'_def updateHb_cons S''_def invContextH2_simps)
                    by (auto simp add: i_callOriginI_h_def otherC split: option.splits)
                  show "invocationRes S' g \<triangleq> g_res" using c3 .
                qed
              qed

              have [simp]: "res = Undef"
              proof -
                have "querySpec progr = crdtSpec"
                  by (simp add: progr_def)
                then show ?thesis
                  using a1 crdtSpec_def by force
              qed


              show "inv2 (invContext' S'b)"
                text \<open>The new invocId and call trivially satisfy the invariant (there is a call and there is no result yet).
                       We need some manual work to establish, that the invariant still holds for old calls. \<close> 
                using inv2_S'
                apply (auto simp add: inv2_def S'b_def S'a_def S''_def invContextH2_simps)
                using no_call_in_t_S'   by (auto simp add: i_callOriginI_h_simps split: if_splits)

              show "inv3 (invContext' S'b) "
                using inv3_S'
                using c_no_hb by (auto simp add: inv3_def S'b_def S'a_def S''_def hb'_def updateHb_cons invContextH2_simps)
            qed


            fix S'c
            assume S'c_def: "S'c = S'a            \<lparr>localState := localState S'a(i \<mapsto> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>),               currentTransaction := (currentTransaction S'a)(i := None), transactionStatus := transactionStatus S'a(t \<mapsto> Committed)\<rparr>"
              and "\<forall>t. transactionStatus S'c t \<noteq> Some Uncommitted"
              and "example_userbase.inv (invContext' S'c)"

            have [simp]: "currentProc S'c i \<triangleq> removeUserImpl"
              by (auto simp add: S'c_def currentProc_S')

            have [simp]: "localState S'c i \<triangleq> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
              by (auto simp add: S'c_def)

            have [simp]: "currentTransaction S'c i = None" 
              by (auto simp add: S'c_def)

            show "(checkCorrect2F ^^ 12) bot (progr, insert c vis', S'c, i)"
            proof (rule checkCorrect2F_step, auto simp add: removeUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'd)

              fix S'd
              assume S'd_def: "S'd = S'c             \<lparr>localState := (localState S'c)(i := None), currentProc := (currentProc S'c)(i := None), visibleCalls := (visibleCalls S'c)(i := None),                invocationRes := invocationRes S'c(i \<mapsto> Undef)\<rparr>"
                and "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"

              have [simp]: "invocationOp S'c i \<triangleq> (removeUser, [UserId u])"
                by (auto simp add: S'c_def S'a_def S''_def)

              have [simp]: "i_callOriginI_h (callOrigin S'c) (transactionOrigin S'c) c \<triangleq> i"
                by (auto simp add: S'c_def S'a_def S''_def invContextH2_simps i_callOriginI_h_simp2)

              have [simp]: "calls S'c c \<triangleq> Call users_remove [UserId u] Undef"
                apply (auto simp add: S'c_def S'a_def)
                using a1 by (auto simp add: progr_def crdtSpec_def)

              show "inv (invContext' S'd)"
              proof 
                show "inv1 (invContext' S'd)"
                  using \<open>inv (invContext' S'c)\<close>
                  by (auto simp add: inv_def inv1_def S'd_def invContextH2_simps)

                show "inv2 (invContext' S'd)"
                  using \<open>inv (invContext' S'c)\<close>
                  by (auto simp add: inv_def inv2_def S'd_def invContextH2_simps)

                show "inv3 (invContext' S'd)"
                  using \<open>inv (invContext' S'c)\<close>
                  by (auto simp add: inv_def inv3_def S'd_def invContextH2_simps )
              qed
            qed
          qed
        qed
      qed


      paragraph \<open>Procedure getUser \<close>

      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_u := UserId u\<rparr>), currentProc := currentProc Sa(i \<mapsto> getUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (getUser, [UserId u]))\<rparr>, i)"
        if c0: "procedures getUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, getUserImpl)"
          and c1: "procName = getUser"
          and c2: "args = [UserId u]"
          and c3: "impl = getUserImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
        for  u
      proof (rule_tac x="15" in exI, rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def, rename_tac t S' newTxns S'a vis')
        fix t S' newTxns S'a vis'
        assume a0: "transactionStatus Sa t = None"
          and a1: "prog S' = prog Sa"
          and a2: "invariant (prog Sa) (invContext' S')"
          and a3: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
          and S'_wf: "state_wellFormed S'"
          and S'a_wf: "state_wellFormed S'a"
          and S'_growth: "state_monotonicGrowth i          (Sa\<lparr>localState := localState Sa(i \<mapsto> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>), currentProc := currentProc Sa(i \<mapsto> getUserImpl),                visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (getUser, [UserId u]))\<rparr>)          S'"
          and a7: "\<forall>t. transactionOrigin Sa t \<triangleq> i = transactionOrigin S' t \<triangleq> i"
          and a8: "localState S' i \<triangleq> \<lparr>ls_pc = 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
          and currentProc_S': "currentProc S' i \<triangleq> getUserImpl"
          and a10: "currentTransaction S' i = None"
          and a11: "visibleCalls S' i \<triangleq> {}"
          and a12: "vis' = callsInTransaction S' newTxns \<down> happensBefore S'"
          and a13: "newTxns \<subseteq> dom (transactionStatus S')"
          and a14: "consistentSnapshot S' vis'"
          and a15: "transactionStatus S' t = None"
          and a16: "\<forall>c. callOrigin S' c \<noteq> Some t"
          and a17: "transactionOrigin S' t = None"
          and S'a_def: "S'a = S'         \<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t),            localState := localState S'(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>), visibleCalls := visibleCalls S'(i \<mapsto> vis')\<rparr>"

        have [simp]: "invocationOp S' i \<triangleq> (getUser, [UserId u])"
          using state_monotonicGrowth_invocationOp_i[OF S'_growth ] by simp

        have [simp]: "invocationRes S' i = None"
          by (simp add: S'_wf a8 wf_localState_noReturn)



        from \<open>invariant (prog Sa) (invContext' S')\<close>
        have inv1_S': "inv1 (invContext' S')"
          and inv2_S': "inv2 (invContext' S')"
          and inv3_S': "inv3 (invContext' S')"
          by (auto simp add: prog_Sa inv_def) 


        have [simp]: "currentProc S'a i \<triangleq> getUserImpl"
          by (auto simp add: S'a_def currentProc_S')

        have [simp]: "localState S'a i \<triangleq> \<lparr>ls_pc = Suc 0, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
          by (auto simp add: S'a_def)

        have [simp]: "currentTransaction S'a i \<triangleq> t" 
          by (auto simp add: S'a_def)



        show "(checkCorrect2F ^^ 14) bot (progr, vis', S'a, i)"
        proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def)

          show "Ex (querySpec progr users_contains_key [UserId u] (getContext S'a i))"
            by (auto simp add: progr_def crdtSpec_def)


          fix c res_contains S'b vis'a hb'
          assume call_c_None: "calls S'a c = None"
            and contains_query: "querySpec progr users_contains_key [UserId u] (getContextH (calls S'a) (happensBefore S'a) (Some vis')) res_contains"
            and vis'_def: "visibleCalls S'a i \<triangleq> vis'"
            and vis'a_def: "vis'a = visibleCalls S'a(i \<mapsto> insert c vis')"
            and hb'_def: "hb' = updateHb (happensBefore S'a) vis' [c]"
            and S'b_def: "S'b = S'a         \<lparr>localState := localState S'a(i \<mapsto> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = res_contains = Bool True\<rparr>),            calls := calls S'a(c \<mapsto> Call users_contains_key [UserId u] res_contains), callOrigin := callOrigin S'a(c \<mapsto> t), visibleCalls := vis'a, happensBefore := hb'\<rparr>"

          have [simp]: "currentProc S'b i \<triangleq> getUserImpl"
            by (auto simp add: S'b_def currentProc_S')

          have [simp]: "localState S'b i \<triangleq> \<lparr>ls_pc = 2, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = res_contains = Bool True\<rparr>"
            by (auto simp add: S'b_def)

          have [simp]: "currentTransaction S'b i \<triangleq> t" 
            by (auto simp add: S'b_def)


          show "(checkCorrect2F ^^ 13) bot (progr, insert c vis', S'b, i)"
          proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def split: localAction.splits option.splits, unfold Def_def; rename_tac S'c)

            text \<open> First the case that the user exists: \<close>
            show "(checkCorrect2F ^^ 12) bot (progr, insert c vis', S'c, i)"
              if res_True: "res_contains = Bool True"
                and S'c_def: "S'c = S'b\<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 3, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = True\<rparr>)\<rparr>"
              for  S'c
            proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def)

              show "\<exists>res. (querySpec progr users_name_get [UserId u] (getContext S'b i)) res"
                by (auto simp add: progr_def crdtSpec_def)

              fix ca res_name S'd vis'd hb'd
              assume  "calls S'b ca = None"
                and  "querySpec progr users_name_get [UserId u] (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) res_name"
                and  "visibleCalls S'b i \<triangleq> insert c vis'"
                and vis'd_def: "vis'd = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
                and hb'd_def: "hb'd = updateHb (happensBefore S'b) (insert c vis') [ca]"
                and S'd_def: "S'd = S'b         \<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = stringval res_name, ls_mail = [], ls_exists = True\<rparr>),            calls := calls S'b(ca \<mapsto> Call users_name_get [UserId u] res_name), callOrigin := callOrigin S'b(ca \<mapsto> t), visibleCalls := vis'd, happensBefore := hb'd\<rparr>"



              have [simp]: "currentProc S'd i \<triangleq> getUserImpl"
                by (auto simp add: S'd_def)

              have [simp]: "localState S'd i \<triangleq> \<lparr>ls_pc = 4, ls_u = UserId u, ls_name = stringval res_name, ls_mail = [], ls_exists = True\<rparr>"
                by (auto simp add: S'd_def)

              have [simp]: "currentTransaction S'd i \<triangleq> t" 
                by (auto simp add: S'd_def)

              show "(checkCorrect2F ^^ 11) bot (progr, insert ca (insert c vis'), S'd, i)"
              proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def)

                show "\<exists>res. (querySpec progr users_mail_get [UserId u] (getContext S'd i)) res"
                  by (auto simp add: progr_def crdtSpec_def)


                fix cb res S'e vis'e hb'e
                assume  "calls S'd cb = None"
                  and  "querySpec progr users_mail_get [UserId u] (getContextH (calls S'd) (happensBefore S'd) (Some (insert ca (insert c vis')))) res"
                  and  "visibleCalls S'd i \<triangleq> insert ca (insert c vis')"
                  and vis'e_def: "vis'e = visibleCalls S'd(i \<mapsto> insert cb (insert ca (insert c vis')))"
                  and hb'e_def: "hb'e = updateHb (happensBefore S'd) (insert ca (insert c vis')) [cb]"
                  and S'e_def: "S'e = S'd         \<lparr>localState := localState S'd(i \<mapsto> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = stringval res_name, ls_mail = stringval res, ls_exists = True\<rparr>),            calls := calls S'd(cb \<mapsto> Call users_mail_get [UserId u] res), callOrigin := callOrigin S'd(cb \<mapsto> t), visibleCalls := vis'e, happensBefore := hb'e\<rparr>"

                have [simp]: "currentProc S'e i \<triangleq> getUserImpl"
                  by (auto simp add: S'e_def)

                have [simp]: "localState S'e i \<triangleq> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = stringval res_name, ls_mail = stringval res, ls_exists = True\<rparr>"
                  by (auto simp add: S'e_def)

                have [simp]: "currentTransaction S'e i \<triangleq> t" 
                  by (auto simp add: S'e_def)

                show "(checkCorrect2F ^^ 10) bot (progr, insert cb (insert ca (insert c vis')), S'e, i)"
                proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'f)
                  fix S'f
                  assume S'f_def: "S'f = S'e             \<lparr>localState := localState S'e(i \<mapsto> \<lparr>ls_pc = 6, ls_u = UserId u, ls_name = stringval res_name, ls_mail = stringval res, ls_exists = True\<rparr>),                currentTransaction := (currentTransaction S'e)(i := None), transactionStatus := transactionStatus S'e(t \<mapsto> Committed)\<rparr>"
                    and  "\<forall>t. transactionStatus S'f t \<noteq> Some Uncommitted"
                    and S'f_wf: "state_wellFormed S'f"


                  have [simp]: "c \<noteq> ca" and [simp]: "ca \<noteq> c"
                    using \<open>calls S'b ca = None\<close>
                    by (auto simp add: S'b_def)

                  have [simp]: "cb \<noteq> ca" and [simp]: "ca \<noteq> cb"
                    using \<open>calls S'd cb = None\<close>
                    by (auto simp add: S'd_def)

                  have [simp]: "c \<noteq> cb" and [simp]: "cb \<noteq> c"
                    using \<open>calls S'd cb = None\<close>
                    by (auto simp add: S'd_def S'b_def)

                  have [simp]: "calls S' c = None"
                    using \<open>calls S'a c = None\<close>
                    by (auto simp add: S'a_def)

                  have [simp]: "calls S' ca = None"
                    using \<open>calls S'b ca = None\<close>
                    by (auto simp add: S'b_def S'a_def)
                  have [simp]: "calls S' cb = None"
                    using \<open>calls S'd cb = None\<close>
                    by (auto simp add: S'd_def S'b_def S'a_def)

                  have [simp]: "callOrigin S' c = None"
                    and [simp]: "callOrigin S' ca = None"
                    and [simp]: "callOrigin S' cb = None"
                    by (auto simp add: S'_wf wellFormed_callOrigin_dom2)

                  have [simp]: "transactionOrigin S' t = None"
                    by (simp add: a17)

                  have [simp]: "\<And>t. transactionOrigin S' t \<noteq> Some i"
                    using Sa_wf a7 invoc_Sa wf_no_invocation_no_origin by blast

                  have [simp]: "\<And>c. callOrigin S' c \<noteq> Some t "
                    by (simp add: a16)



                  have ihb_simps:
                       "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) (updateHb (happensBefore S') vis' [c, ca, cb])
                      = invocation_happensBeforeH (i_callOriginI_h (callOrigin S') (transactionOrigin S')) (happensBefore S') \<union>
    {i'. \<exists>t' c'. c' \<in> vis' \<and> callOrigin S' c' \<triangleq> t' \<and> transactionOrigin S' t' \<triangleq> i' \<and> (\<forall>c'' t''. callOrigin S' c'' \<triangleq> t'' \<and> transactionOrigin S' t'' \<triangleq> i' \<longrightarrow> c'' \<in> vis')} \<times> {i}"
                  proof (rule invocation_happensBeforeH_one_transaction_simp[where co="callOrigin S'"], auto)
                    show "\<And>c t. callOrigin S' c \<triangleq> t \<Longrightarrow> \<exists>i. transactionOrigin S' t \<triangleq> i"
                      by (meson S'_wf option.exhaust wf_no_transactionStatus_origin_for_nothing wf_transactionOrigin_and_status)
                    show "\<And>c c'. (c, c') \<in> happensBefore S' \<Longrightarrow> \<exists>t. callOrigin S' c \<triangleq> t"
                      by (meson S'_wf not_None_eq wellFormed_happensBefore_calls_l wf_callOrigin_and_calls)
                    show "\<And>c c'. (c, c') \<in> happensBefore S' \<Longrightarrow> \<exists>t. callOrigin S' c' \<triangleq> t"
                      by (meson S'_wf option.exhaust wellFormed_happensBefore_calls_r wf_callOrigin_and_calls)
                  qed

                  show "example_userbase.inv (invContext' S'f)"
                  proof 
                    show "inv1 (invContext' S'f)"
                      using inv1_S' by (auto simp add: inv1_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def updateHb_chain insert_commute invContextH2_simps ihb_simps)


                    show "inv2 (invContext' S'f)"
                      using inv2_S'  apply (auto simp add: inv2_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def invContextH2_simps cong: conj_cong)
                      by (auto simp add: i_callOriginI_h_simps)

                    show "inv3 (invContext' S'f)"
                      using inv3_S' by (auto simp add: inv3_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def  updateHb_cons invContextH2_simps cong: conj_cong)
                  qed
                  then have "inv1 (invContext' S'f)" and "inv2 (invContext' S'f)" and "inv3 (invContext' S'f)"
                    using example_userbase.inv_def by auto




                  have [simp]: "currentProc S'f i \<triangleq> getUserImpl"
                    by (auto simp add: S'f_def)

                  have [simp]: "localState S'f i \<triangleq> \<lparr>ls_pc = 6, ls_u = UserId u, ls_name = stringval res_name, ls_mail = stringval res, ls_exists = True\<rparr>"
                    by (auto simp add: S'f_def)

                  have [simp]: "currentTransaction S'f i = None" 
                    by (auto simp add: S'f_def)


                  show "(checkCorrect2F ^^ 9) bot (progr, insert cb (insert ca (insert c vis')), S'f, i)"
                  proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'g)

                    fix S'g
                    assume S'g_def: "S'g = S'f             \<lparr>localState := (localState S'f)(i := None), currentProc := (currentProc S'f)(i := None), visibleCalls := (visibleCalls S'f)(i := None),                invocationRes := invocationRes S'f(i \<mapsto> Found (stringval res_name) (stringval res))\<rparr>"
                      and  "\<forall>t. transactionStatus S'g t \<noteq> Some Uncommitted"

                    have [simp]: "invocationOp S'f i \<triangleq> (getUser, [UserId u])"
                      by (auto simp add: S'f_def S'e_def S'd_def S'b_def S'a_def)

                    show "example_userbase.inv (invContext' S'g)"
                    proof
                      show "inv1 (invContext' S'g)"
                        using \<open>inv1 (invContext' S'f)\<close> apply (auto simp add: inv1_def S'g_def invContextH2_simps)
                        text \<open>There cannot be a remove before, since we got the result that the user exists.\<close> 
                      proof -
                        fix r
                        assume r_not_found: "\<forall>r g u.              invocationOp S'f r \<triangleq> (removeUser, [u]) \<longrightarrow>              invocationOp S'f g \<triangleq> (getUser, [u]) \<longrightarrow>              (r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'f) (transactionOrigin S'f)) (happensBefore S'f) \<longrightarrow>              (\<forall>g_res. invocationRes S'f g \<triangleq> g_res \<longrightarrow> g_res = NotFound)"
                          and r_removeUser: "invocationOp S'f r \<triangleq> (removeUser, [UserId u])"
                          and r_before_i: "(r, i) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'f) (transactionOrigin S'f)) (happensBefore S'f)"

                        have [simp]: "transactionOrigin S'f t \<triangleq> i"
                          by (auto simp add: S'f_def S'e_def S'd_def S'b_def S'a_def)
                        have [simp]: "callOrigin S'f c \<triangleq> t"
                          by (auto simp add: S'f_def S'e_def S'd_def S'b_def S'a_def)

                        text \<open>Because invocId r happened before i, there must be a call in r, that happened before:\<close>
                        from r_before_i
                        obtain cr cr_info cr_t
                          where cr_info: "calls S'f cr \<triangleq> cr_info"
                            and cr_t: "callOrigin S'f cr \<triangleq> cr_t"
                            and cr_t_r: "transactionOrigin S'f cr_t \<triangleq> r"
                             and cr_hb: "(cr, c)\<in>happensBefore S'f"
                          apply atomize_elim
                          apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits)
                          by (meson S'f_wf \<open>callOrigin S'f c \<triangleq> t\<close> \<open>transactionOrigin S'f t \<triangleq> i\<close> domD happensBefore_in_calls_left)


                        text \<open>By inv2 that call removed the user:\<close>
                        from \<open>inv2 (invContext' S'f)\<close>
                        have cr_info_def: "cr_info = Call users_remove [UserId u] Undef"
                          using r_removeUser cr_info cr_t cr_t_r by (auto simp add: inv2_def invContextH2_simps i_callOriginI_h_simp)



                        text \<open>By invariant 3 there is no assignment after the remove:\<close>
                        from \<open>inv3 (invContext' S'f)\<close>
                        thm \<open>inv3 (invContext' S'f)\<close>[simplified inv3_def,rule_format]
                        have cr_no_later_write: "\<nexists>write v.
                           (calls (invContext' S'f) write \<triangleq> Call users_name_assign [UserId u, v] Undef 
                          \<or> calls (invContext' S'f) write \<triangleq> Call users_mail_assign [UserId u, v] Undef) 
                         \<and>(cr, write) \<in> happensBefore (invContext' S'f)"
                          using \<open>cr_info = Call users_remove [UserId u] Undef\<close> cr_info  by (auto simp add: inv3_def invContextH2_simps)

                        have [simp]: "calls S'a c = None"
                          by (simp add: call_c_None)

                        have [simp]: "calls S'a ca = None"
                          using \<open>calls S'b ca = None\<close>
                          by (auto simp add: S'b_def)

                        have [simp]: "calls S'a cb = None"
                          using \<open>calls S'd cb = None\<close>
                          by (auto simp add: S'd_def S'b_def)



                        from cr_no_later_write
                        have cr_no_later_write': "\<nexists>write v.
                           (calls (invContext' S'a) write \<triangleq> Call users_name_assign [UserId u, v] Undef 
                          \<or> calls (invContext' S'a) write \<triangleq> Call users_mail_assign [UserId u, v] Undef) 
                         \<and>(cr, write) \<in> happensBefore (invContext' S'a)"
                          apply (auto simp add: S'f_def S'e_def S'd_def S'b_def hb'e_def hb'd_def hb'_def invContextH2_simps split: if_splits)
                           apply (drule_tac x="write" in spec)
                          apply auto
                          apply (auto simp add: updateHb_cons)
                          apply (drule_tac x="write" in spec)
                          apply (auto simp add: updateHb_cons)
                          done

                        from \<open>calls S'f cr \<triangleq> cr_info\<close>
                        have [simp]: "calls S'a cr = Some (Call users_remove [UserId u] Undef)"
                          by (auto simp add: cr_info_def S'f_def S'b_def S'c_def S'd_def S'e_def split: if_splits)

                        from \<open>(cr, c)\<in>happensBefore S'f\<close>
                        have "(cr, c) \<in> updateHb (happensBefore S'a) vis' [c, ca, cb]"
                          apply (auto simp add: S'f_def S'e_def hb'e_def S'd_def hb'd_def S'b_def hb'_def updateHb_chain)
                          apply (subst(asm) updateHb_chain)
                          by auto

                        then have [simp]: "cr \<in> vis'"
                          by (metis S'a_wf \<open>calls S'a ca = None\<close> \<open>calls S'a cr \<triangleq> Call users_remove [UserId u] Undef\<close> call_c_None in_sequence_cons option.distinct(1) single_invocation_correctness.updateHb_nil updateHb_cases wellFormed_happensBefore_calls_r)

                        text \<open>But that is not compatible with the result we got for the query:\<close>
                        from \<open>querySpec progr users_contains_key [UserId u] (getContextH (calls S'a) (happensBefore S'a) (Some vis')) res_contains\<close>
                        show False
                          using cr_no_later_write' by (auto simp add: progr_def crdtSpec_def getContextH_def restrict_map_def restrict_relation_def \<open>res_contains = Bool True\<close> invContextH2_simps split: if_splits)
                      qed

                      show "inv2 (invContext' S'g)"
                        using \<open>inv2 (invContext' S'f)\<close> by (auto simp add: inv2_def S'g_def invContextH2_simps)
                      show "inv3 (invContext' S'g)"
                        using \<open>inv3 (invContext' S'f)\<close> by (auto simp add: inv3_def S'g_def invContextH2_simps)
                  qed
                qed
              qed
            qed
          qed
            text \<open> Now the case that the user does not exist: \<close>
            show "(checkCorrect2F ^^ 12) bot (progr, insert c vis', S'c, i)"
              if res_False: "res_contains \<noteq> Bool True"
                and S'c_def: "S'c = S'b\<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 5, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>)\<rparr>"
              for  S'c
            proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'c)

              fix S'c
              assume S'c_def: "S'c = S'b             \<lparr>localState := localState S'b(i \<mapsto> \<lparr>ls_pc = 6, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>),                currentTransaction := (currentTransaction S'b)(i := None), transactionStatus := transactionStatus S'b(t \<mapsto> Committed)\<rparr>"
                and "\<forall>t. transactionStatus S'c t \<noteq> Some Uncommitted"


              have "invocationRes S' i = None"
                by auto

              from \<open>calls S'a c = None\<close>
              have [simp]: "callOrigin S' c = None"
                by (auto simp add: S'a_def S'_wf wf_callOrigin_and_calls)


              have [simp]: "transactionOrigin S' t = None"
                by (simp add: a17)

              have [simp]: "transactionOrigin S' t \<noteq> Some i" for i
                by simp

                find_theorems c

              show "example_userbase.inv (invContext' S'c)"
              proof
                show "inv1 (invContext' S'c)"
                  apply (auto simp add: inv1_def S'c_def S'b_def S'a_def hb'_def invContextH2_simps)
                  apply (subst(asm) invocation_happensBeforeH_one_transaction_simp)
                             apply auto
                  using Sa_wf a7 invoc_Sa wf_no_invocation_no_origin apply auto[1]
                  using a16 apply blast
                  apply (meson S'_wf not_None_eq wf_callOrigin_implies_transactionStatus_defined wf_transactionOrigin_and_status)
                  apply (meson S'_wf option.exhaust wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l)
                  apply (meson S'_wf option.exhaust wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_r)
                  using inv1_S' inv1_def by (auto simp add: invContextH2_simps)

                show "inv2 (invContext' S'c)"
                  using \<open>inv2 (invContext' S')\<close>  by (auto simp add: inv2_def S'c_def S'b_def S'a_def hb'_def i_callOriginI_h_simps invContextH2_simps)
                show "inv3 (invContext' S'c)"
                  using \<open>inv3 (invContext' S')\<close>  
                  by (auto simp add: inv3_def S'c_def S'b_def S'a_def hb'_def updateHb_cons invContextH2_simps)
              qed


              have [simp]: "currentProc S'c i \<triangleq> getUserImpl"
                by (auto simp add: S'c_def)

              have [simp]: "localState S'c i \<triangleq> \<lparr>ls_pc = 6, ls_u = UserId u, ls_name = [], ls_mail = [], ls_exists = False\<rparr>"
                by (auto simp add: S'c_def)

              have [simp]: "currentTransaction S'c i = None" 
                by (auto simp add: S'c_def)

              show "(checkCorrect2F ^^ 11) bot (progr, insert c vis', S'c, i)"
              proof (rule checkCorrect2F_step, auto simp add: getUserImpl_def lsInit_def S'c_def split: localAction.splits option.splits, unfold Def_def, rename_tac S'd)

                fix S'd
                assume S'd_def: "S'd = S'b             \<lparr>currentTransaction := (currentTransaction S'b)(i := None), transactionStatus := transactionStatus S'b(t \<mapsto> Committed), localState := (localState S'b)(i := None),                currentProc := (currentProc S'b)(i := None), visibleCalls := (visibleCalls S'b)(i := None), invocationRes := invocationRes S'b(i \<mapsto> NotFound)\<rparr>"
                  and "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommitted"

                show "example_userbase.inv (invContext' S'd)"
                proof
                  show "inv1 (invContext' S'd)"
                    using \<open>inv (invContext' S'c)\<close>
                    by (auto simp add: inv_def inv1_def S'd_def S'c_def invContextH2_simps)

                    show "inv2 (invContext' S'd)"
                    using \<open>inv (invContext' S'c)\<close>
                    by (auto simp add: inv_def inv2_def S'd_def S'c_def invContextH2_simps)

                  show "inv3 (invContext' S'd)"
                    using \<open>inv (invContext' S'c)\<close>
                    by (auto simp add: inv_def inv3_def S'd_def S'c_def invContextH2_simps)
                qed

              qed
            qed
          qed
        qed     
      qed
    qed
  qed
qed



lemma if_split_h: "\<lbrakk>c \<Longrightarrow> P x; \<not>c \<Longrightarrow> P y\<rbrakk>  \<Longrightarrow> P (if c then x else y)"
  by auto

lemma procedure_cases: "procedures procName args \<noteq> None \<Longrightarrow> procName \<in> {registerUser, updateMail, removeUser, getUser}"
  by (auto simp add: procedures_def split: if_splits)

lemma procedure_cases': "\<lbrakk>procedures procName args \<triangleq> x; procName \<noteq> registerUser; procName \<noteq> updateMail; procName \<noteq> removeUser\<rbrakk> \<Longrightarrow> procName = getUser"
  by (auto simp add: procedures_def split: if_splits)

lemma procedure_case_split: "\<lbrakk>procedures procName args \<triangleq> x; procName = registerUser \<Longrightarrow> P; procName = updateMail \<Longrightarrow> P; procName = removeUser \<Longrightarrow> P; procName = getUser \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using procedure_cases' by blast

(*
lemma procedure_cases2: "procedures procName args \<triangleq> (initState, impl) \<longleftrightarrow> (
  (\<exists>name mail. procName = registerUser \<and> args = [String name, String mail] \<and> initState = lsInit\<lparr>ls_name := name, ls_mail := mail \<rparr> \<and> impl = registerUserImpl)
\<or> (\<exists>u mail. procName = updateMail \<and> args = [UserId u, String mail] \<and> initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail \<rparr> \<and> impl = updateMailImpl)
\<or> (\<exists>u. procName = removeUser \<and> args = [UserId u] \<and> initState = lsInit\<lparr>ls_u := UserId u \<rparr> \<and> impl = removeUserImpl)
\<or> (\<exists>u. procName = getUser \<and> args = [UserId u] \<and> initState = lsInit\<lparr>ls_u := UserId u \<rparr> \<and> impl = getUserImpl))" (is "?Left \<longleftrightarrow> ?Right")
  by (auto simp add: procedures_def split: list.splits val.splits)
*)

lemma procedure_cases3[cases set,case_names 
    case_registerUser[procname args initiState impl] 
    case_updateMail[procname args initiState impl]  
    case_removeUser[procname args initiState impl]  
    case_get_User[procname args initiState impl] ]: 
  assumes impl: "procedures procName args \<triangleq> (initState, impl)"
and "\<And>name mail. \<lbrakk>procName = registerUser; args = [String name, String mail]; initState = registerUser_impl (String name) (String mail); impl = toImpl\<rbrakk> \<Longrightarrow> P" 
and "\<And>u mail. \<lbrakk>procName = updateMail; args = [UserId u, String mail]; initState = updateMail_impl (UserId u) (String mail); impl = toImpl\<rbrakk> \<Longrightarrow> P"
and "\<And>u.  \<lbrakk>procName = removeUser; args = [UserId u]; initState = removeUser_impl (UserId u); impl = toImpl\<rbrakk> \<Longrightarrow> P"
and "\<And>u.  \<lbrakk>procName = getUser; args = [UserId u]; initState = getUser_impl (UserId u); impl = toImpl\<rbrakk> \<Longrightarrow> P"
shows P
  using impl  by (auto simp add: procedures_def split: list.splits val.splits if_splits elim: assms(2-))


lemma StateDef_simps: 
  "S' ::= S ==> calls S' = calls S"
  "S' ::= S ==> happensBefore S' = happensBefore S"
  "S' ::= S ==> prog S' = prog S"
  "S' ::= S ==> callOrigin S' = callOrigin S"
  "S' ::= S ==> transactionOrigin S' = transactionOrigin S"
  "S' ::= S ==> generatedIds S' = generatedIds S"
  "S' ::= S ==> knownIds S' = knownIds S"
  "S' ::= S ==> invocationOp S' = invocationOp S"
  "S' ::= S ==> invocationRes S' = invocationRes S"
  "S' ::= S ==> transactionStatus S' = transactionStatus S"
  "S' ::= S ==> localState S' = localState S"
  "S' ::= S ==> currentProc S' = currentProc S"
  "S' ::= S ==> visibleCalls S' = visibleCalls S"
  "S' ::= S ==> currentTransaction S' = currentTransaction S"
  by (auto simp add: Def_def)



lemma IStateDef_simps: 
  "S' ::= S ==> i_callOrigin S' = i_callOrigin S"
  "S' ::= S ==> i_transactionOrigin S' = i_transactionOrigin S"
  "S' ::= S ==> i_knownIds S' = i_knownIds S"
  "S' ::= S ==> i_invocationOp S' = i_invocationOp S"
  "S' ::= S ==> i_invocationRes S' = i_invocationRes S"
  by (auto simp add: Def_def)


*)

end
