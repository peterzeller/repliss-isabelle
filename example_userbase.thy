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
             (* TODO  state_wellFormed should be for free here *)
          sorry


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
