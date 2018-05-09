theory example_userbase
imports invariant_simps
begin




(* ^^^^ *)

datatype val =
    String string
  | UserId int
  | Bool bool
  | Undef
  | Found string string
  | NotFound

fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"
  
record localState = 
  ls_pc :: nat
  ls_u :: val
  ls_name :: string
  ls_mail :: string
  ls_exists :: bool

definition lsInit :: "localState" where
"lsInit = \<lparr>
  ls_pc = 0,
  ls_u = Undef,
  ls_name = '''',
  ls_mail = '''',
  ls_exists = False
\<rparr>"
  
(*
  querySpec :: "operation \<Rightarrow> 'any list \<Rightarrow> 'any operationContext \<Rightarrow> 'any \<Rightarrow> bool"
  procedure :: "procedureName \<Rightarrow> 'any list \<rightharpoonup> ('localState \<times> ('localState, 'any) procedureImpl)"
  invariant :: "'any invariantContext \<Rightarrow> bool"
*)

(* define used names, to avoid typos and to help Isabelle*)

definition "users_name_assign \<equiv> ''users_name_assign''"
definition "users_mail_assign \<equiv> ''users_mail_assign''"
definition "users_contains_key \<equiv> ''users_contains_key''"
definition "users_remove \<equiv> ''users_remove''"
definition "users_name_get \<equiv> ''users_name_get''"
definition "users_mail_get \<equiv> ''users_mail_get''"
definition "registerUser \<equiv> ''registerUser''"
definition "updateMail \<equiv> ''updateMail''"
definition "removeUser \<equiv> ''removeUser''"
definition "getUser \<equiv> ''getUser''"

lemma names_distinct: "distinct [users_name_assign, users_mail_assign, users_contains_key, users_remove, users_name_get, users_mail_get, registerUser, updateMail, removeUser, getUser]"
  by eval

lemma distinct_perm1: "distinct [x,y] \<longleftrightarrow> x \<noteq> y \<and> y \<noteq> x"
  by auto

lemma distinct_perm2: "distinct (x#xs) \<longleftrightarrow> (\<forall>y\<in>set xs. x \<noteq> y \<and> y \<noteq> x) \<and> distinct xs"
  by auto

lemma distinct_perm3: "(\<forall>x\<in>set [x]. P x) \<longleftrightarrow> P x"
  by auto

lemma distinct_perm4: "(\<forall>x\<in>set (y#ys). P x) \<longleftrightarrow> (P y \<and> (\<forall>x\<in>set ys. P x))"
  by auto

schematic_goal name_distinct2[simp]: "?X"
  apply (insert names_distinct)
  apply (subst(asm) distinct_perm1 distinct_perm2)+
  apply (subst(asm) distinct_perm3 distinct_perm4)+
  apply assumption
  done

lemma "users_remove \<noteq> users_name_assign"
  by simp

find_theorems "op &&&"
thm conjI
thm name_distinct2[intro]

lemma names_distinct3[simp]:
"users_name_assign \<noteq> users_mail_assign"
"users_name_assign \<noteq> users_contains_key"
"users_name_assign \<noteq> users_remove"
"users_name_assign \<noteq> users_name_get"
"users_name_assign \<noteq> users_mail_get"
"users_name_assign \<noteq> registerUser "
"users_name_assign \<noteq> updateMail "
"users_name_assign \<noteq> removeUser "
"users_name_assign \<noteq> getUser"
"users_mail_assign \<noteq> users_contains_key"
"users_mail_assign \<noteq> users_remove"
"users_mail_assign \<noteq> users_name_get"
"users_mail_assign \<noteq> users_mail_get"
"users_mail_assign \<noteq> registerUser "
"users_mail_assign \<noteq> updateMail "
"users_mail_assign \<noteq> removeUser "
"users_mail_assign \<noteq> getUser "
"users_contains_key \<noteq> users_remove"
"users_contains_key \<noteq> users_name_get"
"users_contains_key \<noteq> users_mail_get"
"users_contains_key \<noteq> registerUser"
"users_contains_key \<noteq> updateMail"
"users_contains_key \<noteq> removeUser"
"users_contains_key \<noteq> getUser"
"users_remove \<noteq> users_name_get"
"users_remove \<noteq> users_mail_get"
"users_remove \<noteq> registerUser"
"users_remove \<noteq> updateMail"
"users_remove \<noteq> removeUser"
"users_remove \<noteq> getUser"
"users_name_get \<noteq> users_mail_get"
"users_name_get \<noteq> registerUser "
"users_name_get \<noteq> updateMail "
"users_name_get \<noteq> removeUser "
"users_name_get \<noteq> getUser "
"users_mail_get \<noteq> registerUser"
"users_mail_get \<noteq> updateMail "
"users_mail_get \<noteq> removeUser "
"users_mail_get \<noteq> getUser "
"registerUser \<noteq> updateMail"
"registerUser \<noteq> removeUser "
"registerUser \<noteq> getUser "
"updateMail \<noteq> removeUser "
"updateMail \<noteq> getUser "
"removeUser \<noteq> getUser"
  using name_distinct2 by auto

lemmas names_distinct4[simp] = names_distinct3[symmetric]


definition registerUserImpl :: "(localState, val) procedureImpl" where
"registerUserImpl ls \<equiv> [
   (* 0 *) NewId (\<lambda>x. (ls\<lparr>ls_u := x, ls_pc := 1\<rparr> :: localState)),
   (* 1 *) BeginAtomic (ls\<lparr>ls_pc := 2\<rparr>),
   (* 2 *) DbOperation users_name_assign [ls_u ls, String (ls_name ls)] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) DbOperation users_mail_assign [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) EndAtomic (ls\<lparr>ls_pc := 5\<rparr>),
   (* 5 *) Return (ls_u ls)
   ] ! ls_pc ls"

definition updateMailImpl :: "(localState, val) procedureImpl" where
"updateMailImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation users_contains_key [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   (* 2 *) LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 4\<rparr> ),
   (* 3 *) DbOperation users_mail_assign [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 5 *) EndAtomic  (ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) Return Undef
   ] ! ls_pc ls"   
   
definition removeUserImpl :: "(localState, val) procedureImpl" where
"removeUserImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation users_remove [ls_u ls] (\<lambda>r. ls\<lparr>ls_pc := 2 \<rparr>),
   (* 2 *) EndAtomic  (ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) Return Undef
   ] ! ls_pc ls"
   
definition getUserImpl :: "(localState, val) procedureImpl" where
"getUserImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation users_contains_key [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   (* 2 *) LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 5\<rparr> ),
   (* 3 *) DbOperation users_name_get [ls_u ls] (\<lambda>r. ls\<lparr>ls_name := stringval r, ls_pc := 4 \<rparr>),
   (* 4 *) DbOperation users_mail_get [ls_u ls] (\<lambda>r. ls\<lparr>ls_mail := stringval r, ls_pc := 5 \<rparr>),
   (* 5 *) EndAtomic  (ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) Return (if ls_exists ls then Found (ls_name ls) (ls_mail ls) else NotFound )
   ] ! ls_pc ls"      
   
   
definition procedures where
"procedures proc args \<equiv> 
  if proc = registerUser then
    case args of 
      [String name, String mail] \<Rightarrow> 
        Some (lsInit\<lparr>ls_name := name, ls_mail := mail \<rparr> , registerUserImpl)
      | _ \<Rightarrow> None
  else if proc = updateMail then 
    case args of 
      [UserId u, String mail] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u, ls_mail := mail \<rparr> , updateMailImpl)
      | _ \<Rightarrow> None
  else if proc = removeUser then 
    case args of 
      [UserId u] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u \<rparr> , removeUserImpl)
      | _ \<Rightarrow> None
  else if proc = getUser then 
    case args of 
      [UserId u] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u \<rparr> , getUserImpl)
      | _ \<Rightarrow> None  
  else 
    None"


definition latest_name_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
"latest_name_assign ctxt u \<equiv>  {v | c1 v. 
     calls ctxt c1 \<triangleq> Call users_name_assign [u, v] Undef
   \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call users_remove [u] Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call users_name_assign [u] v' \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"

definition latest_mail_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
"latest_mail_assign ctxt u \<equiv>  {v | c1 v. 
     calls ctxt c1 \<triangleq> Call users_mail_assign [u, v] Undef
   \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call users_remove [u] Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call users_mail_assign [u] v' \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"   
   
definition crdtSpec :: "operation \<Rightarrow> val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec oper args ctxt res \<equiv> 
  if oper \<in> {users_name_assign, users_mail_assign, users_remove} then
    (* update-operations always return Undef *)
    res = Undef
  else if oper = users_contains_key then
    res = Bool (\<exists>c1 v. (calls ctxt c1 \<triangleq> Call users_name_assign (args @ [v]) Undef
                 \<or> calls ctxt c1 \<triangleq> Call users_mail_assign (args @ [v]) Undef)
               \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call users_remove args Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt))
  else if oper = users_name_get then 
    if latest_name_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_name_assign ctxt (hd args)
  else if oper = users_mail_get then 
    if latest_mail_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_mail_assign ctxt (hd args)
  else
    False"
  
definition inv1 :: "val invariantContext \<Rightarrow> bool" where
"inv1 ctxt \<equiv> \<forall>r g u.
    i_invocationOp ctxt r \<triangleq> (removeUser, [u])
  \<and> i_invocationOp ctxt g \<triangleq> (getUser, [u])
  \<and> (r,g) \<in> invocation_happensBefore ctxt
  \<longrightarrow> i_invocationRes ctxt g \<triangleq> NotFound"
  
definition inv2 :: "val invariantContext \<Rightarrow> bool" where
"inv2 ctxt \<equiv> \<forall>u i.
    i_invocationOp ctxt i \<triangleq> (removeUser, [u])
  \<and> i_invocationRes ctxt i \<noteq> None
  \<longrightarrow> (\<exists>c. i_callOriginI ctxt c \<triangleq> i \<and> calls ctxt c \<triangleq> Call users_remove [u] Undef)"
  
definition inv3 :: "val invariantContext \<Rightarrow> bool" where
"inv3 ctxt \<equiv> \<not>(\<exists>write delete u v.
  (calls ctxt write \<triangleq> Call users_name_assign [u, v] Undef
    \<or> calls ctxt write \<triangleq> Call users_mail_assign [u, v] Undef)
  \<and> (calls ctxt delete \<triangleq> Call users_remove [u] Undef)
  \<and> (delete, write) \<in> happensBefore ctxt
  )"
  
definition inv :: "val invariantContext \<Rightarrow> bool" where
"inv ctxt \<equiv> inv1 ctxt \<and> inv2 ctxt \<and> inv3 ctxt"
  
definition progr :: "(localState, val) prog" where
"progr \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"

lemma procedure_progr[simp]: "procedure progr = procedures"
  by (simp add: progr_def)


lemma if_split_h: "\<lbrakk>c \<Longrightarrow> P x; \<not>c \<Longrightarrow> P y\<rbrakk>  \<Longrightarrow> P (if c then x else y)"
  by auto

lemma procedure_cases: "procedures procName args \<noteq> None \<Longrightarrow> procName \<in> {registerUser, updateMail, removeUser, getUser}"
  by (auto simp add: procedures_def split: if_splits)

lemma procedure_cases': "\<lbrakk>procedures procName args \<triangleq> x; procName \<noteq> registerUser; procName \<noteq> updateMail; procName \<noteq> removeUser\<rbrakk> \<Longrightarrow> procName = getUser"
  by (auto simp add: procedures_def split: if_splits)

lemma procedure_case_split: "\<lbrakk>procedures procName args \<triangleq> x; procName = registerUser \<Longrightarrow> P; procName = updateMail \<Longrightarrow> P; procName = removeUser \<Longrightarrow> P; procName = getUser \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using procedure_cases' by blast


lemma procedure_cases2: "procedures procName args \<triangleq> (initState, impl) \<longleftrightarrow> (
  (\<exists>name mail. procName = registerUser \<and> args = [String name, String mail] \<and> initState = lsInit\<lparr>ls_name := name, ls_mail := mail \<rparr> \<and> impl = registerUserImpl)
\<or> (\<exists>u mail. procName = updateMail \<and> args = [UserId u, String mail] \<and> initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail \<rparr> \<and> impl = updateMailImpl)
\<or> (\<exists>u. procName = removeUser \<and> args = [UserId u] \<and> initState = lsInit\<lparr>ls_u := UserId u \<rparr> \<and> impl = removeUserImpl)
\<or> (\<exists>u. procName = getUser \<and> args = [UserId u] \<and> initState = lsInit\<lparr>ls_u := UserId u \<rparr> \<and> impl = getUserImpl))" (is "?Left \<longleftrightarrow> ?Right")
  by (auto simp add: procedures_def split: list.splits val.splits)


theorem "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect)
  have [simp]: "invariant progr = inv" by (simp add: progr_def)

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)
  
  show "invariant_all' (repliss_sem.initialState progr)"
     by (auto simp add: initialState_def  inv_def inv1_def inv2_def inv3_def invContextH_def)
  
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
         and i6: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommited"
       for  i S' procName args initState impl
       using i1 proof (subst(asm) procedure_cases2, auto)
       

       show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (registerUser, [String name, String mail]))) (invocationRes S'))"
         if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
           and c1: "procName = registerUser"
           and c2: "args = [String name, String mail]"
           and c3: "impl = registerUserImpl"
           and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
         for  name mail
         using old_inv
         by (auto simp add: inv_def inv1_def inv2_def inv3_def)


       show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (updateMail, [UserId u, String mail]))) (invocationRes S'))"
         if c0: "procedures updateMail [UserId u, String mail] \<triangleq> (lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>, updateMailImpl)"
           and c1: "procName = updateMail"
           and c2: "args = [UserId u, String mail]"
           and c3: "impl = updateMailImpl"
           and c4: "initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>"
         for  u mail
         using old_inv
         by (auto simp add: inv_def inv1_def inv2_def inv3_def)


       show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u]))) (invocationRes S'))"
         if c0: "procedures removeUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, removeUserImpl)"
           and c1: "procName = removeUser"
           and c2: "args = [UserId u]"
           and c3: "impl = removeUserImpl"
           and c4: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
         for  u
       proof (auto simp add: inv_def)
         show "inv1 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
           using old_inv
           apply (auto simp add: inv_def inv1_def)[1]
           using i4 i5 new_invocation_cannot_happen_before by blast


          show "inv2 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"

            using old_inv
            apply (auto simp add: inv_def inv2_def)
            by (simp add: i4 i5 state_wellFormed_invocation_before_result)

          show "inv3 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
            using old_inv
            by (auto simp add: inv_def inv3_def)
        qed




        show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u]))) (invocationRes S'))"
          if c0: "procedures getUser [UserId u] \<triangleq> (lsInit\<lparr>ls_u := UserId u\<rparr>, getUserImpl)"
            and c1: "procName = getUser"
            and c2: "args = [UserId u]"
            and c3: "impl = getUserImpl"
            and c4: "initState = lsInit\<lparr>ls_u := UserId u\<rparr>"
          for  u
        proof (auto simp add: inv_def)

          from old_inv
          show "inv1 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
            apply (auto simp add: inv_def inv1_def)
            using i4 i5 new_invocation_cannot_happen_after by blast

          from old_inv
          show "inv2 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
            by (auto simp add: inv_def inv2_def)

          from old_inv
          show "inv3 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (getUser, [UserId u])))
             (invocationRes S'))"
            by (auto simp add: inv_def inv3_def)
        qed
      qed
    qed


    show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
      if c0: "S \<in> initialStates' progr i"
      for  S i

      using c0  apply (subst(asm) initialStates'_def)
    proof auto


      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>, i)"
        if c0: "S = Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>"
          and c1: "prog Sa = progr"
          and c2: "procedures procName args \<triangleq> (initState, impl)"
          and c3: "uniqueIdsInList args \<subseteq> knownIds Sa"
          and c4: "example_userbase.inv (invContext' Sa)"
          and c5: "state_wellFormed Sa"
          and c6: "invocationOp Sa i = None"
          and c7: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommited"
        for  Sa procName args initState impl
        using c2 proof (subst(asm) procedure_cases2, auto)

        have [simp]: "currentTransaction Sa i = None"
          by (simp add: c5 c6 wellFormed_invoc_notStarted(1))



        show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>), currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail]))\<rparr>, i)"
          if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
            and c1: "procName = registerUser"
            and c2: "args = [String name, String mail]"
            and c3: "impl = registerUserImpl"
            and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
          for  name mail
          apply (rule_tac x="10" in exI)
          apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
          apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
          apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
          apply (auto simp add: progr_def crdtSpec_def )[1]
          apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
           apply (auto simp add: progr_def crdtSpec_def )[1]
          apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
           defer
           apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)

        proof



















     
  show "programCorrect_s progr"
  proof (rule show_program_correct_single_invocation)
    show "\<And>S i. S \<in> initialStates progr i \<Longrightarrow> invariant_all S"
    proof (auto simp add: invariant_all_def inv_def)
      fix S i vis
      assume a0: "S \<in> initialStates progr i"
         and vis_cs: "consistentSnapshot S vis"
      
      
      from a0 
      obtain Spre procName args initState impl
        where S_def: "S = Spre\<lparr>localState := localState Spre(i \<mapsto> initState), currentProc := currentProc Spre(i \<mapsto> impl), visibleCalls := visibleCalls Spre(i \<mapsto> {}), invocationOp := invocationOp Spre(i \<mapsto> (procName, args))\<rparr>"
          and a1: "prog Spre = progr"
          and a2: "procedure progr procName args \<triangleq> (initState, impl)"
          and a3: "uniqueIdsInList args \<subseteq> knownIds Spre"
          and pre_inv_all: "invariant_all Spre"
          and pre_wf: "state_wellFormed Spre"
          and a6: "invocationOp Spre i = None"
      by (subst(asm) initialStates_def, auto)

      from `consistentSnapshot S vis` 
      have vis_cs_pre: "consistentSnapshot Spre vis"
        by (auto simp add: consistentSnapshot_def S_def)
      
      from pre_inv_all
      have pre_inv: "inv (invContextVis Spre vis)"
        by (auto simp add: invariant_all_def `prog Spre = progr` `consistentSnapshot Spre vis`)
        
      
      from pre_inv 
      have "inv1 (invContextVis Spre vis)"
        using example_userbase.inv_def by blast
      thus "inv1 (invContextVis S vis)"
        apply (auto simp add: inv1_def  split: if_splits)
        apply (auto simp add: invariant_simps)
        
        
        apply (auto simp add: invContextH_def invocation_happensBefore_def i_callOriginI_def )
        
        
        
        apply (subst(asm) invariantContext.simps)+
        apply (auto simp add: restrict_relation_def restrict_map_def)
        
        find_theorems i_transactionOrigin
        apply (drule_tac x=r in spec)
        apply (drule_tac x=g in spec)
        sorry (* apply (auto simp add: invocation_happensBefore_def) *)
       
        (* TODO add simplification rules for "i_invocationOp (invContextVis S vis)" and other fields *)
        
      
      show "inv2 (invContextVis S vis)"
        using a0 apply (subst(asm) initialStates_def)
        apply (auto simp add: inv2_def invContextH_def restrict_relation_def restrict_map_def i_callOriginI_def invariantContext.defs split: if_splits option.splits)
        apply (simp add: state_wellFormed_invocation_before_result)
        sorry
        
      show "inv3 (invContextVis S vis)"
        using a0 apply (subst(asm) initialStates_def)
        apply (auto simp add: inv3_def  invContextH_def restrict_relation_def restrict_map_def  split: if_splits)
        
        
      sorry
    
    show "\<And>bound S i. S \<in> initialStates progr i \<Longrightarrow> checkCorrect progr S i bound"
    
      
    
  
  apply (auto simp add: programCorrect_s_def)
  apply (auto simp add: prog_def step_s.simps)



end