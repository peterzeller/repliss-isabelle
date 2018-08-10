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

instantiation val :: valueType begin
definition uniqueIds_val where 
"uniqueIds_val x \<equiv> case x of UserId u \<Rightarrow> {UserId u} | _ \<Rightarrow> {}"
instance
proof               
qed
end

lemma "uniqueIds (Bool True) = {}"
  by (simp add: uniqueIds_val_def)


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

lemma in_img_simp: "y\<in>f`S \<longleftrightarrow> (\<exists>x\<in>S. f x = y)"
  by auto

definition "in_sequence xs x y \<equiv> \<exists>i j. i<j \<and> j<length xs \<and> xs!i = x \<and> xs!j=y "


lemma in_sequence_nil[simp]: "in_sequence [] = (\<lambda>x y. False)"
  apply (rule ext)+
  by (auto simp add: in_sequence_def)

lemma in_sequence_cons:
  "in_sequence (x # xs) a b \<longleftrightarrow> (x=a \<and> b\<in>set xs \<or> in_sequence xs a b)"
  apply (auto simp add: in_sequence_def)
  apply (metis (no_types, lifting) Suc_diff_eq_diff_pred Suc_less_eq Suc_pred gr_implies_not_zero not_gr_zero nth_Cons' zero_less_diff)
  apply (metis Suc_mono in_set_conv_nth nth_Cons_0 nth_Cons_Suc zero_less_Suc)
  by (meson Suc_mono nth_Cons_Suc)


lemma in_sequence_in1: "in_sequence xs x y \<Longrightarrow> x\<in>set xs"
  by (metis in_sequence_def in_set_conv_nth less_imp_le less_le_trans)


lemma in_sequence_in2: "in_sequence xs x y \<Longrightarrow> y\<in>set xs"
  by (metis in_sequence_def nth_mem)




lemma updateHb_cases: 
"(cx, cy) \<in> updateHb Hb vis cs \<longleftrightarrow> ((cx,cy)\<in>Hb \<or> cx\<in>vis \<and> cy\<in>set cs \<or> in_sequence cs cx cy)"
  by (induct cs arbitrary: Hb vis, auto simp add: updateHb_cons in_sequence_cons)



text {*
Updating the invocation happens-before in the first transaction of an invocation.

TODO Problem: second transaction could remove HB. Maybe just consider HB with finished invocations on the left (and on the right?)
*}
lemma invocation_happensBeforeH_update:
  assumes  Orig'_def: "\<And>c. Orig' c = (case Orig c of Some i \<Rightarrow> Some i | None \<Rightarrow> if c\<in>set cs then Some i else None)"
    and cs_no_orig: "\<And>c. c \<in> set cs \<Longrightarrow> Orig c = None"
    and cs_notin_vis: "\<And>c. c \<in> set cs \<Longrightarrow> c \<notin> vis"
    and cs_notin_hb1: "\<And>c x. c \<in> set cs \<Longrightarrow> (x,c) \<notin> Hb"
    and cs_notin_hb2: "\<And>c x. c \<in> set cs \<Longrightarrow> (c,x) \<notin> Hb"
    and invoc_fresh: "\<And>c. Orig c \<noteq> Some i"
    and cs_nonempty: "cs \<noteq> []"
  shows
    "invocation_happensBeforeH Orig' (updateHb Hb vis cs)
   = invocation_happensBeforeH Orig Hb \<union> {i'. (\<forall>c. Orig c \<triangleq> i' \<longrightarrow> c \<in> vis) \<and> (\<exists>c. Orig c \<triangleq> i') }  \<times>  {i} "
  using invoc_fresh  apply (auto simp add: invocation_happensBeforeH_def  in_img_simp updateHb_cases)
                apply (auto simp add: Orig'_def cs_notin_hb1  cs_notin_hb2 cs_notin_vis cs_no_orig  split: option.splits if_splits)
  using cs_no_orig in_sequence_in2 apply fastforce
  using cs_no_orig in_sequence_in1 apply fastforce
  apply (metis cs_no_orig in_sequence_in2 option.simps(3))
  apply (metis cs_no_orig in_sequence_in2 option.distinct(1))
  using cs_no_orig in_sequence_in2 apply fastforce
  apply (metis cs_no_orig option.distinct(1) option.sel)
  apply (metis cs_no_orig option.distinct(1) option.sel)
  using cs_notin_vis option.simps(3) apply fastforce
  using cs_nonempty last_in_set by blast




(*
  using cs_no_orig apply fastforce
  using cs_no_orig apply force
  using cs_def cs_no_orig apply fastforce
  apply (metis cs_no_orig option.distinct(1) option.sel)
  apply (metis cs_no_orig option.inject option.simps(3))
  using cs_notin_vis apply fastforce
  using cs_def apply auto[1]
   defer
  apply (simp add: cs_def)

  apply fastforce


  apply (metis option.sel option.simps(3))
  apply fastforce

  thm option.sel option.simps(3)

  using [[smt_solver=cvc4]]
                apply (smt Orig'_def cs_notin_hb2 cs_notin_vis option.case_eq_if option.exhaust_sel)
  apply (smt Orig'_def cs_notin_hb1 option.case_eq_if option.exhaust_sel option.sel)

  find_theorems "op`" "op\<in>" "\<exists>x. _ "


  apply (rename_tac i1 i2 c1 c2)
*)
theorem "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect)
  have [simp]: "invariant progr = inv" by (simp add: progr_def)

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)

  subsection {* Initial state *}

  text {* Show that the initial state satisfies the invariant *}
  show "invariant_all' (repliss_sem.initialState progr)"
    by (auto simp add: initialState_def  inv_def inv1_def inv2_def inv3_def invContextH_def)

  subsection {* Initial state of procedure invocations *}

  text {* Show that the initial state of procedure invocations satisfies the invariant.  *}
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

      text {* We consider the initial state for each procedure individually: *}

      paragraph {* Case registerUser *}
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (registerUser, [String name, String mail]))) (invocationRes S'))"
        if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
          and c1: "procName = registerUser"
          and c2: "args = [String name, String mail]"
          and c3: "impl = registerUserImpl"
          and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
        for  name mail
        using old_inv
        by (auto simp add: inv_def inv1_def inv2_def inv3_def)

      paragraph {* Case updateMail *}
      show "example_userbase.inv (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (updateMail, [UserId u, String mail]))) (invocationRes S'))"
        if c0: "procedures updateMail [UserId u, String mail] \<triangleq> (lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>, updateMailImpl)"
          and c1: "procName = updateMail"
          and c2: "args = [UserId u, String mail]"
          and c3: "impl = updateMailImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>"
        for  u mail
        using old_inv
        by (auto simp add: inv_def inv1_def inv2_def inv3_def)

      paragraph {* Case removeUser *}
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


      paragraph {* Case getUser *}
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

  subsection {* We check the implementation using the checkCorrect2F function. 
       This basically checks the implementation up to the given bound.
       We have to show that there exists a bound such that all reachable states are covered and proven correct.  *}
  show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    if c0: "S \<in> initialStates' progr i"
    for  S i

    text {* We unfold the definition of initial states. *}
    using c0  apply (subst(asm) initialStates'_def)
  proof auto


    show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>, i)"
      if c0: "S = Sa\<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>"
        and c1: "prog Sa = progr"
        and c2: "procedures procName args \<triangleq> (initState, impl)"
        and c3: "uniqueIdsInList args \<subseteq> knownIds Sa"
        and c4: "example_userbase.inv (invContext' Sa)"
        and Sa_wf: "state_wellFormed Sa"
        and c6: "invocationOp Sa i = None"
        and c7: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommited"
        and c8: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
      for  Sa procName args initState impl
      text {* We consider the case for each procedure separately:  *}
      using c2 proof (subst(asm) procedure_cases2, auto)

      have [simp]: "currentTransaction Sa i = None"
        by (simp add: Sa_wf c6 wellFormed_invoc_notStarted(1))

(* ony unfold definitions, when needed for evaluation: *)
      have h1[simp]:  "S' ::= S \<Longrightarrow> (currentProc S' i \<triangleq> x) \<longleftrightarrow> (currentProc S i \<triangleq> x)" for S' S i x  by (auto simp add: Def_def)
      have h2[simp]: "S' ::= S \<Longrightarrow>  ls_pc (the (localState S' i)) = ls_pc (the (localState S i))" for S' S i by (auto simp add: Def_def)
      have h3[simp]: "S' ::= S \<Longrightarrow>  (currentTransaction S' i = None) \<longleftrightarrow> (currentTransaction S i = None)" for S' S i by (auto simp add: Def_def)

      have queries_defined_users_name_assign[simp]: 
        "Ex (querySpec progr users_name_assign [u, n] ctxt)"
        for u n ctxt
        by (auto simp add: progr_def crdtSpec_def )

      have queries_defined_users_name_assign[simp]: 
        "Ex (querySpec progr users_mail_assign [u, n] ctxt)"
        for u n ctxt
        by (auto simp add: progr_def crdtSpec_def )

      paragraph {* Case register User: *}
      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>), currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail]))\<rparr>, i)"
        if c0: "procedures registerUser [String name, String mail] \<triangleq> (lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>, registerUserImpl)"
          and c1: "procName = registerUser"
          and c2: "args = [String name, String mail]"
          and c3: "impl = registerUserImpl"
          and c4: "initState = lsInit\<lparr>ls_name := name, ls_mail := mail\<rparr>"
        for  name mail
        text {* We start by unrolling the implementation. *}
        apply (rule_tac x="10" in exI)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
         defer
         apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
      proof (unfold Def_def)
        print_cases

        text {* Check invariant at end of invocation: *}
(*
fix uid S' t S'a newTxns S'' vis' ls x2 c res S'b vis'a hb' x2a ca resa S'c vis'b hb'a x2b S'd S'e
assume a0: "uid \<notin> generatedIds Sa"
   and a1: "S' = Sa\<lparr>currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),                   invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail])),                   localState := localState Sa(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = uid, ls_name = name, ls_mail = mail, ls_exists = False\<rparr>),                   generatedIds := insert uid (generatedIds Sa)\<rparr>"
   and a2: "localState S' i \<triangleq> ls"
   and a3: "transactionStatus S' t = None"
   and a4: "prog S'a = prog S'"
   and a5: "invariant (prog S') (invContext' S'a)"
   and a6: "\<forall>tx. transactionStatus S'a tx \<noteq> Some Uncommited"
   and a7: "state_wellFormed S'a"
   and a8: "state_wellFormed S''"
   and a9: "state_monotonicGrowth S' S'a"
   and a10: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S'a t \<triangleq> i"
   and a11: "localState S'a i \<triangleq> ls"
   and a12: "currentProc S'a i \<triangleq> registerUserImpl"
   and a13: "currentTransaction S'a i = None"
   and a14: "visibleCalls S' i \<triangleq> {}"
   and a15: "visibleCalls S'a i \<triangleq> {}"
   and a16: "vis' = callsInTransaction S'a newTxns \<down> happensBefore S'a"
   and a17: "newTxns \<subseteq> dom (transactionStatus S'a)"
   and a18: "consistentSnapshot S'a vis'"
   and a19: "transactionStatus S'a t = None"
   and a20: "\<forall>c. callOrigin S'a c \<noteq> Some t"
   and a21: "transactionOrigin S'a t = None"
   and a22: "S'' = S'a         \<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'a(t \<mapsto> i),            currentTransaction := currentTransaction S'a(i \<mapsto> t), localState := localState S'a(i \<mapsto> ls\<lparr>ls_pc := 2\<rparr>), visibleCalls := visibleCalls S'a(i \<mapsto> vis')\<rparr>"
   and a23: "currentTransaction S'' i \<triangleq> x2"
   and a24: "calls S'' c = None"
   and a25: "querySpec progr users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))]          (getContextH (calls S'') (happensBefore S'') (Some vis')) res"
   and a26: "visibleCalls S'' i \<triangleq> vis'"
   and a27: "vis'a = visibleCalls S''(i \<mapsto> insert c vis')"
   and a28: "hb' = updateHb (happensBefore S'') vis' [c]"
   and a29: "S'b = S''         \<lparr>localState := localState S''(i \<mapsto> the (localState S'' i)\<lparr>ls_pc := 3\<rparr>),            calls := calls S''(c \<mapsto> Call users_name_assign [ls_u (the (localState S'' i)), String (ls_name (the (localState S'' i)))] res),            callOrigin := callOrigin S''(c \<mapsto> x2), visibleCalls := vis'a, happensBefore := hb'\<rparr>"
   and a30: "currentTransaction S'b i \<triangleq> x2a"
   and a31: "calls S'b ca = None"
   and a32: "querySpec progr users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))]          (getContextH (calls S'b) (happensBefore S'b) (Some (insert c vis'))) resa"
   and a33: "visibleCalls S'b i \<triangleq> insert c vis'"
   and a34: "vis'b = visibleCalls S'b(i \<mapsto> insert ca (insert c vis'))"
   and a35: "hb'a = updateHb (happensBefore S'b) (insert c vis') [ca]"
   and a36: "S'c = S'b         \<lparr>localState := localState S'b(i \<mapsto> the (localState S'b i)\<lparr>ls_pc := 4\<rparr>),            calls := calls S'b(ca \<mapsto> Call users_mail_assign [ls_u (the (localState S'b i)), String (ls_mail (the (localState S'b i)))] resa),            callOrigin := callOrigin S'b(ca \<mapsto> x2a), visibleCalls := vis'b, happensBefore := hb'a\<rparr>"
   and a37: "currentTransaction S'c i \<triangleq> x2b"
   and a38: "S'd = S'c         \<lparr>localState := localState S'c(i \<mapsto> the (localState S'c i)\<lparr>ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S'c)(i := None),            transactionStatus := transactionStatus S'c(x2b \<mapsto> Commited)\<rparr>"
   and a39: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommited"
   and a40: "example_userbase.inv (invContext' S'd)"
   and a41: "S'e = S'd         \<lparr>localState := (localState S'd)(i := None), currentProc := (currentProc S'd)(i := None), visibleCalls := (visibleCalls S'd)(i := None),            invocationRes := invocationRes S'd(i \<mapsto> ls_u (the (localState S'd i))), knownIds := knownIds S'd \<union> uniqueIds (ls_u (the (localState S'd i)))\<rparr>"
   and a42: "\<forall>t. transactionStatus S'e t \<noteq> Some Uncommited"
*)


        fix uid S' t S'a newTxns S'' vis' ls x2 c res S'b vis'a hb' x2a ca resa S'c vis'b hb'a x2b S'd S'e
        assume a0: "uid \<notin> generatedIds Sa"
          and S'_def: "S' = Sa         \<lparr>currentProc := currentProc Sa(i \<mapsto> registerUserImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}),            invocationOp := invocationOp Sa(i \<mapsto> (registerUser, [String name, String mail])),            localState := localState Sa(i \<mapsto> \<lparr>ls_pc = Suc 0, ls_u = uid, ls_name = name, ls_mail = mail, ls_exists = False\<rparr>),            generatedIds := insert uid (generatedIds Sa)\<rparr>"
          and a2: "localState S' i \<triangleq> ls"
          and a3: "transactionStatus S' t = None"
          and a4: "prog S'a = prog S'"
          and old_inv: "invariant (prog S') (invContext' S'a)"
          and a6: "\<forall>tx. transactionStatus S'a tx \<noteq> Some Uncommited"
          and S'a_wf: "state_wellFormed S'a"
          and S''_wf: "state_wellFormed S''"
          and S'a_mono: "state_monotonicGrowth S' S'a"
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
          and S''_def: "S'' = S'a         \<lparr>transactionStatus := transactionStatus S'a(t \<mapsto> Uncommited), transactionOrigin := transactionOrigin S'a(t \<mapsto> i),            currentTransaction := currentTransaction S'a(i \<mapsto> t), localState := localState S'a(i \<mapsto> ls\<lparr>ls_pc := 2\<rparr>), visibleCalls := visibleCalls S'a(i \<mapsto> vis')\<rparr>"
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
          and S'd_def: "S'd = S'c         \<lparr>localState := localState S'c(i \<mapsto> the (localState S'c i)\<lparr>ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S'c)(i := None),            transactionStatus := transactionStatus S'c(x2b \<mapsto> Commited)\<rparr>"
          and a38: "\<forall>t. transactionStatus S'd t \<noteq> Some Uncommited"
          and a39: "example_userbase.inv (invContext' S'd)"
          and S'e_def: "S'e = S'd         \<lparr>localState := (localState S'd)(i := None), currentProc := (currentProc S'd)(i := None), visibleCalls := (visibleCalls S'd)(i := None),            invocationRes := invocationRes S'd(i \<mapsto> ls_u (the (localState S'd i))), knownIds := knownIds S'd \<union> uniqueIds (ls_u (the (localState S'd i)))\<rparr>"
          and a41: "\<forall>t. transactionStatus S'e t \<noteq> Some Uncommited"
          and tranactionOriginUnchanged: "\<forall>t. transactionOrigin S' t \<triangleq> i = transactionOrigin S'a t \<triangleq> i"


        have invocationOp_unchanged: "invocationOp S'e = invocationOp S'a"
          by (subst S'e_def S'd_def S'c_def S'b_def S''_def, simp)+

        find_theorems hb'

        text {* Same transcation TODO: remember in verification condition generation  *}
        have[simp]: "x2a = t"
          using `currentTransaction S'b i \<triangleq> x2a` S''_def by (auto simp add: S'b_def)
        have [simp]: "x2 = t"
          using `currentTransaction S'' i \<triangleq> x2` S''_def by (auto simp add: S'b_def)

        have [simp]: "c \<noteq> ca" "ca \<noteq> c"
          using `calls S'b ca = None` by (auto simp add: S'b_def)


        have i_callOriginI_h_update:
            "(i_callOriginI_h (callOrigin S'e) (transactionOrigin S'e))
           = (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a))(c \<mapsto> i, ca \<mapsto> i)"
          apply (rule ext)
          apply (subst S'e_def S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: i_callOriginI_h_def t_origin split: option.splits if_splits)


        have happensBefore_update:
             "happensBefore S'e = updateHb (happensBefore S'a) vis' [c, ca]"
          apply (subst S'e_def S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: updateHb_chain) (* TODO add updateHb_chain lemma above *)


        hence happensBefore_update2:
             "happensBefore S'e = (happensBefore S'a \<union> (vis' \<times> {c, ca}) \<union> {(c, ca)})"
          by (auto simp add: updateHb_cons)


        from `calls S'' c = None`
        have "calls S'a c = None"
          by (auto simp add: S''_def)

        hence [simp]: "callOrigin S'a c = None"
          by (simp add: S'a_wf)

        from S''_def `calls S'b ca = None` S'b_def
        have "calls S'a ca = None"
          by auto

        hence [simp]: "callOrigin S'a ca = None"
          by (simp add: S'a_wf)

        have [simp]: "c \<notin> vis'"
          using S''_wf calls_S'' visibleCalls_S'' wellFormed_visibleCallsSubsetCalls_h(2) by fastforce
        have [simp]: "ca \<notin> vis'"
          using `calls S'b ca = None` `visibleCalls S'b i \<triangleq> insert c vis'`
            S''_wf visibleCalls_S'' wellFormed_visibleCallsSubsetCalls2
          by (auto simp add: S'b_def)


        from `invocationOp Sa i = None`
        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: Sa_wf wf_no_invocation_no_origin)


        have "transactionOrigin Sa tx \<noteq> Some i" for tx
          by (simp add: c8)
        hence "transactionOrigin S' tx \<noteq> Some i" for tx
          by (simp add: S'_def)
        hence "transactionOrigin S'a tx \<noteq> Some i" for tx
          using tranactionOriginUnchanged by blast


        have invocationHb_update:
          "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'e) (transactionOrigin S'e)) (happensBefore S'e)
            = invocation_happensBeforeH (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a)) (happensBefore S'a)
             \<union> {i'. (\<forall>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i') }  \<times> {i}"
          (* {i'. (\<forall>c. ?Orig c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. ?Orig c \<triangleq> i')} \<times> {?i} *)
          apply (subst happensBefore_update)
          apply (rule invocation_happensBeforeH_update)
                apply (auto simp add: i_callOriginI_h_update split: option.splits)
                    apply (auto simp add: i_callOriginI_h_def split: option.splits)
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_r apply blast
          using S'a_wf \<open>calls S'a c = None\<close> wellFormed_happensBefore_calls_l apply blast
          using S'a_wf \<open>calls S'a ca = None\<close> wellFormed_happensBefore_calls_l apply blast
          using \<open>\<And>tx. transactionOrigin S'a tx \<noteq> Some i\<close> by blast

        from `prog Sa = progr` 
        have "prog S' = progr"
          by (auto simp add: S'_def)


        from `invariant (prog S') (invContext' S'a)`
        have old_inv1: "inv1 (invContext' S'a)"
          by (simp add: \<open>prog S' = progr\<close> example_userbase.inv_def)

        have invocationRes_S'e: "invocationRes S'e i' \<triangleq> r" if "invocationRes S'a i' \<triangleq> r" for i' r
          using that state_wellFormed_no_result_when_running[OF S'a_wf a10] by (auto simp add: S'e_def S'd_def S'c_def S'b_def S''_def)

        have invocationRes_S'e2: "invocationRes S'e = (invocationRes S'a)(i \<mapsto> ls_u ls)"
          by (auto simp add: S'e_def S'd_def S'c_def S'b_def S''_def)

        have "invocationOp S' i \<triangleq> (registerUser, [String name, String mail])"
          by (auto simp add: S'_def)
        hence [simp]: "invocationOp S'a i \<triangleq> (registerUser, [String name, String mail])"
          using S'a_mono state_monotonicGrowth_invocationOp by blast
        hence [simp]: "invocationOp S'e i \<triangleq> (registerUser, [String name, String mail])"
          using invocationOp_unchanged by auto

        show "example_userbase.inv (invContext' S'e)"
        proof (auto simp add: inv_def)

          show "inv1 (invContext' S'e)"
            apply (auto simp add: inv1_def invocationOp_unchanged invocationHb_update)
            using old_inv1 by (auto simp add: inv1_def invocationRes_S'e2)

          have "inv2 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto


          thus "inv2 (invContext' S'e)"
            apply (auto simp add: inv2_def invocationOp_unchanged invocationRes_S'e2)
            apply (auto simp add: S'e_def S'd_def S'c_def S'b_def S''_def)
            apply (drule_tac x=u in spec)
            apply (drule_tac x=ia in spec)
            apply auto
            apply (rule_tac x=cb in exI)
            apply (auto simp add: \<open>calls S'a c = None\<close> \<open>calls S'a ca = None\<close>)
            apply (auto simp add:  i_callOriginI_h_def split: option.splits)
            using t_origin by blast

          have "inv3 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto



          thus "inv3 (invContext' S'e)"
            apply (auto simp add: inv3_def invocationOp_unchanged invocationRes_S'e2)
             apply (auto simp add: S'e_def split: if_splits)
             apply (auto simp add: S'd_def split: if_splits)
             apply (auto simp add: S'c_def split: if_splits)
              apply (auto simp add: S'b_def split: if_splits)
               apply (auto simp add: S''_def split: if_splits)
               apply (auto simp add: hb'a_def updateHb_cons S'b_def hb'_def S''_def)
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
          from `localState S' i \<triangleq> ls`
          have "ls_u ls = uid"
            by (auto simp add: S'_def)


          from `uid \<notin> generatedIds Sa`
          have "ls_u ls \<notin> generatedIds S'a" 
(* TODO because it was generated *)
            sorry



          show x: "False"
            if c0: "\<forall>write delete u. calls S'a delete \<triangleq> Call users_remove [u] Undef \<longrightarrow> (\<forall>v. calls S'a write \<noteq> Some (Call users_name_assign [u, v] Undef) \<and> calls S'a write \<noteq> Some (Call users_mail_assign [u, v] Undef)) \<or> (delete, write) \<notin> happensBefore S'a"
              and c1: "delete \<noteq> ca"
              and c2: "delete \<noteq> c"
              and c3: "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
              and c4: "res = Undef"
              and c5: "delete \<in> vis'"
            for  delete
            find_theorems knownIds
              (* TODO if the delete is in vis, then it must have used a differt userId, because ls_u was just created and not returned yet *)
            sorry


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

              (* same as above (x) *)
            sorry
        qed
      qed










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