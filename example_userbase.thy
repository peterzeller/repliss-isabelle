theory example_userbase
  imports invariant_simps unique_ids
begin




\<comment> \<open>  ^^^^  \<close>

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
instance by standard
end

definition "isUserId x \<equiv> case x of UserId _ \<Rightarrow> True | _ \<Rightarrow> False"

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

\<comment> \<open>  define used names, to avoid typos and to help Isabelle \<close>

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

fun pickLine where 
  "pickLine ls list =
  (case list of 
    [] \<Rightarrow> LocalStep ls
  | (x#xs) \<Rightarrow>
    (case ls_pc ls of
        0 \<Rightarrow> x
      | Suc n \<Rightarrow>  pickLine (ls\<lparr>ls_pc := n\<rparr>) xs))"

find_consts "val \<Rightarrow> bool"

definition registerUserImpl :: "(localState, val) procedureImpl" where
  "registerUserImpl ls \<equiv> pickLine ls [
   \<comment> \<open>  0  \<close> NewId (\<lambda>x. if isUserId x then Some (ls\<lparr>ls_u := x, ls_pc := 1\<rparr> :: localState) else None),
   \<comment> \<open>  1  \<close> BeginAtomic (ls\<lparr>ls_pc := 2\<rparr>),
   \<comment> \<open>  2  \<close> DbOperation users_name_assign [ls_u ls, String (ls_name ls)] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  3  \<close> DbOperation users_mail_assign [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   \<comment> \<open>  4  \<close> EndAtomic (ls\<lparr>ls_pc := 5\<rparr>),
   \<comment> \<open>  5  \<close> Return (ls_u ls)
   ]"

definition updateMailImpl :: "(localState, val) procedureImpl" where
  "updateMailImpl ls \<equiv> pickLine ls [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation users_contains_key [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   \<comment> \<open>  2  \<close> LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 4\<rparr> ),
   \<comment> \<open>  3  \<close> DbOperation users_mail_assign [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   \<comment> \<open>  4  \<close> EndAtomic  (ls\<lparr>ls_pc := 5\<rparr>),
   \<comment> \<open>  5  \<close> Return Undef
   ]"   

definition removeUserImpl :: "(localState, val) procedureImpl" where
  "removeUserImpl ls \<equiv> pickLine ls [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation users_remove [ls_u ls] (\<lambda>r. ls\<lparr>ls_pc := 2 \<rparr>),
   \<comment> \<open>  2  \<close> EndAtomic  (ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  3  \<close> Return Undef
   ]"

definition getUserImpl :: "(localState, val) procedureImpl" where
  "getUserImpl ls \<equiv> pickLine ls [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation users_contains_key [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   \<comment> \<open>  2  \<close> LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 5\<rparr> ),
   \<comment> \<open>  3  \<close> DbOperation users_name_get [ls_u ls] (\<lambda>r. ls\<lparr>ls_name := stringval r, ls_pc := 4 \<rparr>),
   \<comment> \<open>  4  \<close> DbOperation users_mail_get [ls_u ls] (\<lambda>r. ls\<lparr>ls_mail := stringval r, ls_pc := 5 \<rparr>),
   \<comment> \<open>  5  \<close> EndAtomic  (ls\<lparr>ls_pc := 6\<rparr>),
   \<comment> \<open>  6  \<close> Return (if ls_exists ls then Found (ls_name ls) (ls_mail ls) else NotFound )
   ]"      


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
    \<comment> \<open>  update-operations always return Undef  \<close>
    res = Undef
  else if oper = users_contains_key then
    res = Bool (\<exists>c1 v. (calls ctxt c1 \<triangleq> Call users_name_assign (args @ [v]) Undef
                 \<or> calls ctxt c1 \<triangleq> Call users_mail_assign (args @ [v]) Undef)
               \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call users_remove args Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt))
  else if oper = users_name_get \<and> length args = 1 then 
    if latest_name_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_name_assign ctxt (hd args)
  else if oper = users_mail_get \<and> length args = 1 then 
    if latest_mail_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_mail_assign ctxt (hd args)
  else
    False"

definition inv1 :: "val invariantContext \<Rightarrow> bool" where
  "inv1 ctxt \<equiv> \<forall>r g u g_res.
    invocationOp ctxt r \<triangleq> (removeUser, [u])
  \<longrightarrow> invocationOp ctxt g \<triangleq> (getUser, [u])
  \<longrightarrow> (r,g) \<in> invocation_happensBefore ctxt
  \<longrightarrow> invocationRes ctxt g \<triangleq> g_res
  \<longrightarrow> g_res = NotFound"

definition inv2 :: "val invariantContext \<Rightarrow> bool" where
  "inv2 ctxt \<equiv> \<forall>u i c.
    invocationOp ctxt i \<triangleq> (removeUser, [u])
  \<longrightarrow> i_callOriginI ctxt c \<triangleq> i
  \<longrightarrow> calls ctxt c \<triangleq> Call users_remove [u] Undef"

definition inv3 :: "val invariantContext \<Rightarrow> bool" where
  "inv3 ctxt \<equiv> \<not>(\<exists>write delete u v.
  (calls ctxt write \<triangleq> Call users_name_assign [u, v] Undef
    \<or> calls ctxt write \<triangleq> Call users_mail_assign [u, v] Undef)
  \<and> (calls ctxt delete \<triangleq> Call users_remove [u] Undef)
  \<and> (delete, write) \<in> happensBefore ctxt
  )"

definition inv :: "val invariantContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> inv1 ctxt \<and> inv2 ctxt \<and> inv3 ctxt"

lemma show_inv[intro]:
  assumes "inv1 S" and "inv2 S" and "inv3 S"
  shows "inv S"
  using assms  by (auto simp add: inv_def)

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



lemma uniqueIds_simp[simp]:
  shows "uniqueIds (String x) = {}"
    and "uniqueIds (Bool b) = {}"
    and "uniqueIds Undef = {}"
    and "uniqueIds (Found x y) = {}"
    and "uniqueIds NotFound = {}"
  by (auto simp add: uniqueIds_val_def)

lemma uniqueId_no_nested: "x \<in> uniqueIds uid \<Longrightarrow> x = (uid :: val)"
  by (auto simp add: uniqueIds_val_def split: val.splits)

lemma uniqueId_no_nested2: "x \<in> uniqueIds uid \<longleftrightarrow> (\<exists>u. x = UserId u \<and> uid = UserId u)"
  by (auto simp add: uniqueIds_val_def split: val.splits)

definition "progr_uids  ls \<equiv> uniqueIds (ls_u ls)"

lemma progr_wf: "program_wellFormed progr_uids progr"
proof (auto simp add: program_wellFormed_def)
  show "procedures_cannot_guess_ids progr_uids procedures"
    apply (rule show_procedures_cannot_guess_ids )
    apply (auto simp add: procedures_cannot_guess_ids_def procedures_def progr_uids_def split: localAction.splits)
    by (auto simp add: uniqueIdsInList_def getUserImpl_def removeUserImpl_def updateMailImpl_def registerUserImpl_def  lsInit_def uniqueId_no_nested  split: list.splits val.splits if_splits nat.splits)

  show "queries_cannot_guess_ids (querySpec progr)"
    apply (auto simp add: progr_def queries_cannot_guess_ids_def2 crdtSpec_def; case_tac args)
           apply (auto simp add: uniqueId_no_nested2)
       apply (auto simp add: uniqueId_no_nested2 latest_mail_assign_def latest_name_assign_def uniqueIdsInList_def)
    by (meson list.set_intros(1) list.set_intros(2))+


qed



text {*
Updating the invocId happens-before in the first transaction of an invocId.

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
        and i6: "\<forall>tx. transactionStatus S' tx \<noteq> Some Uncommitted"
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
      proof 
        show "inv1 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
          using old_inv
          apply (auto simp add: inv_def inv1_def)[1]
          using i4 i5 new_invocation_cannot_happen_before by blast


        show "inv2 (invContextH2 (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S') (knownIds S') (invocationOp S'(i \<mapsto> (removeUser, [UserId u])))
           (invocationRes S'))"
          using old_inv
          apply (auto simp add: inv_def inv2_def)
          using i4 i5 wf_no_invocation_no_origin  by (auto simp add: i_callOriginI_h_def split: option.splits)


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
      proof

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
      text {* We consider the case for each procedure separately:  *}
      using procedures proof (subst(asm) procedure_cases2, auto)

      have [simp]: "currentTransaction Sa i = None"
        by (simp add: Sa_wf invoc_Sa wellFormed_invoc_notStarted(1))

\<comment> \<open>  ony unfold definitions, when needed for evaluation:  \<close>
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



      from ` example_userbase.inv (invContext' Sa)`
      have inv1_Sa: "inv1 (invContext' Sa)"
        and inv2_Sa: "inv2 (invContext' Sa)"
        and inv3_Sa: "inv3 (invContext' Sa)"
        by (auto simp add: inv_def)


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

        text {* Check invariant at end of invocId: *}
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

        text {* Same transcation TODO: remember in verification condition generation  *}
        have[simp]: "x2a = t"
          using `currentTransaction S'b i \<triangleq> x2a` S''_def by (auto simp add: S'b_def)
        have [simp]: "x2 = t"
          using `currentTransaction S'' i \<triangleq> x2` S''_def by (auto simp add: S'b_def)

        have [simp]: "c \<noteq> ca" "ca \<noteq> c"
          using `calls S'b ca = None` by (auto simp add: S'b_def)


        have i_callOriginI_h_update:
          "(i_callOriginI_h (callOrigin S'd) (transactionOrigin S'd))
           = (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a))(c \<mapsto> i, ca \<mapsto> i)"
          apply (rule ext)
          apply (subst S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: i_callOriginI_h_simps t_origin)


        have happensBefore_update:
          "happensBefore S'd = updateHb (happensBefore S'a) vis' [c, ca]"
          apply (subst S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: updateHb_chain) \<comment> \<open>  TODO add updateHb_chain lemma above  \<close>


        hence happensBefore_update2:
          "happensBefore S'd = (happensBefore S'a \<union> (vis' \<times> {c, ca}) \<union> {(c, ca)})"
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
          by (simp add: transactionOriginSa)
        hence "transactionOrigin S' tx \<noteq> Some i" for tx
          by (simp add: S'_def)
        hence "transactionOrigin S'a tx \<noteq> Some i" for tx
          using tranactionOriginUnchanged by blast


        have invocationHb_update:
          "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'd) (transactionOrigin S'd)) (happensBefore S'd)
            = invocation_happensBeforeH (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a)) (happensBefore S'a)
             \<union> {i'. (\<forall>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i') }  \<times> {i}"
          \<comment> \<open>  {i'. (\<forall>c. ?Orig c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. ?Orig c \<triangleq> i')} \<times> {?i}  \<close>
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

        have invocationRes_S'e: "invocationRes S'd i' \<triangleq> r" if "invocationRes S'a i' \<triangleq> r" for i' r
          using that state_wellFormed_no_result_when_running[OF S'a_wf a10] by (auto simp add: S'd_def S'c_def S'b_def S''_def)

        have invocationRes_S'e2: "invocationRes S'd = (invocationRes S'a)"
          by (auto simp add: S'd_def S'c_def S'b_def S''_def)

        have "invocationOp S' i \<triangleq> (registerUser, [String name, String mail])"
          by (auto simp add: S'_def)
        hence [simp]: "invocationOp S'a i \<triangleq> (registerUser, [String name, String mail])"
          using S'a_mono state_monotonicGrowth_invocationOp by blast
        hence [simp]: "invocationOp S'd i \<triangleq> (registerUser, [String name, String mail])"
          using invocationOp_unchanged by auto

        show "example_userbase.inv (invContext' S'd)"
        proof

          show "inv1 (invContext' S'd)"
            apply (auto simp add: inv1_def invocationOp_unchanged invocationHb_update)
            using old_inv1 by (auto simp add: inv1_def invocationRes_S'e2)


          have "inv2 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto


          thus "inv2 (invContext' S'd)"
            by (auto simp add: inv2_def invocationOp_unchanged S'd_def S'c_def S'b_def S''_def i_callOriginI_h_simps  split: option.splits if_splits)

          have "inv3 (invContext' S'a)"
            using \<open>prog S' = progr\<close> example_userbase.inv_def old_inv by auto



          thus "inv3 (invContext' S'd)"
            apply (auto simp add: inv3_def invocationOp_unchanged invocationRes_S'e2)
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


            from `generatedIds Sa uid = None` `localState S' i \<triangleq> ls`
            have "generatedIds Sa (ls_u ls) = None" 
              by (auto simp add: S'_def)



            from `generatedIds Sa uid = None`
            have "uid \<notin> knownIds Sa"
              using Sa_wf \<open>prog Sa = progr\<close> progr_wf wf_knownIds_subset_generatedIds2 by fastforce

            hence "uid \<notin> knownIds S'"
              by (simp add: S'_def)

            have "generatedIds S' uid \<triangleq> i"
              by (auto simp add: S'_def)

            from S'a_mono
            obtain tr
              where "S' ~~ tr \<leadsto>* S'a"
                and "\<forall>(i',a)\<in>set tr. i' \<noteq> i" 
                and "\<forall>i. (i, AFail) \<notin> set tr"
              by (auto simp add: state_monotonicGrowth_def)


            from `S' ~~ tr \<leadsto>* S'a` \<open>generatedIds S' uid \<triangleq> i\<close> `uid \<notin> knownIds S'`
            thm steps_private_uniqueIds_h
            have "uid \<notin> knownIds S'a  
              \<and> (\<forall>i' ls. localState S'a i' \<triangleq> ls \<longrightarrow> i' \<noteq> i \<longrightarrow> uid \<notin> progr_uids ls) \<and> (\<forall>c opr args r. calls S'a c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args)"
              (* the uid is not written to the database and not known and it cannot be generated again, so
    it cannot become known in the monotonic growth step.
       TODO: this could be a general lemma in the framework for monotonicGrowth  *)

            proof (rule steps_private_uniqueIds_h)
              show " \<forall>c opr args r. calls S' c \<triangleq> Call opr args r \<longrightarrow> uid \<notin> uniqueIdsInList args"
                apply (auto simp add: S'_def)
                using `generatedIds Sa uid = None` \<comment> \<open>id did not exist in Sa, so it cannot be in a call\<close>
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
                using `generatedIds Sa uid = None` \<comment> \<open>id did not exist in Sa, so it cannot be in a local state\<close>
                using Sa_wf \<open>prog Sa = progr\<close> progr_wf wf_onlyGeneratedIdsInLocalState by fastforce
            qed
            hence S'a_uid_not_known: "uid \<notin> knownIds S'a"  
              and S'a_uid_not_in_ls:"\<And>i' ls. localState S'a i' \<triangleq> ls \<Longrightarrow> i' \<noteq> i \<Longrightarrow> uid \<notin> progr_uids ls"
              and S'a_uid_not_in_calls: "\<And>c opr args r. calls S'a c \<triangleq> Call opr args r \<Longrightarrow> uid \<notin> uniqueIdsInList args"
              by blast+


            have not_deleted: "calls S'a delete \<noteq> Some (Call users_remove [ls_u ls] Undef)" for delete
            proof (rule ccontr, simp)
              assume "calls S'a delete \<triangleq> Call users_remove [ls_u ls] Undef"
              hence "uid \<notin> uniqueIdsInList [ls_u ls]"
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
          by (auto simp add: i_callOriginI_h_simps t_origin split: option.splits if_splits)


        have happensBefore_update:
          "happensBefore S'e = updateHb (happensBefore S'a) vis' [c, ca]"
          apply (subst S'e_def S'd_def S'c_def S'b_def S''_def hb'a_def hb'_def, simp?)+
          by (auto simp add: updateHb_chain) \<comment> \<open>  TODO add updateHb_chain lemma above  \<close>


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
          by (simp add: transactionOriginSa)
        hence "transactionOrigin S' tx \<noteq> Some i" for tx
          by (simp add: S'_def)
        hence "transactionOrigin S'a tx \<noteq> Some i" for tx
          using tranactionOriginUnchanged by blast


        have invocationHb_update:
          "invocation_happensBeforeH (i_callOriginI_h (callOrigin S'e) (transactionOrigin S'e)) (happensBefore S'e)
            = invocation_happensBeforeH (i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a)) (happensBefore S'a)
             \<union> {i'. (\<forall>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. i_callOriginI_h (callOrigin S'a) (transactionOrigin S'a) c \<triangleq> i') }  \<times> {i}"
          \<comment> \<open>  {i'. (\<forall>c. ?Orig c \<triangleq> i' \<longrightarrow> c \<in> vis') \<and> (\<exists>c. ?Orig c \<triangleq> i')} \<times> {?i}  \<close>
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


        from `example_userbase.inv (invContext' S'd)`
        have old_inv1: "inv1 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        from `example_userbase.inv (invContext' S'd)`
        have old_inv2: "inv2 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        from `example_userbase.inv (invContext' S'd)`
        have old_inv3: "inv3 (invContext' S'd)"
          by (simp add: example_userbase.inv_def)

        have [simp]: "invocationOp S'd i \<triangleq> (registerUser, [String name, String mail])" 
          by (auto simp add: S'd_def S'c_def S'b_def S''_def S'_def intro!: state_monotonicGrowth_invocationOp[OF `state_monotonicGrowth i S' S'a`])

        show "example_userbase.inv (invContext' S'e)"
        proof

          show "inv1 (invContext' S'e)"
            using old_inv1 by (auto simp add: S'e_def inv1_def)


          show "inv2 (invContext' S'e)"
            using old_inv2
            by (auto simp add: inv2_def S'e_def)

          show "inv3 (invContext' S'e)"
            using old_inv3 
            by (auto simp add: inv3_def S'e_def)
        qed
      qed

      paragraph {* Procedure updateMail *}



      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>), currentProc := currentProc Sa(i \<mapsto> updateMailImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (updateMail, [UserId u, String mail]))\<rparr>, i)"
        if c0: "procedures updateMail [UserId u, String mail] \<triangleq> (lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>, updateMailImpl)"
          and c1: "procName = updateMail"
          and c2: "args = [UserId u, String mail]"
          and c3: "impl = updateMailImpl"
          and c4: "initState = lsInit\<lparr>ls_u := UserId u, ls_mail := mail\<rparr>"
        for  u mail
        text {* We start by unrolling the implementation. *}
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


          from `invariant (prog Sa) (invContext' S')`
          have "inv (invContext' S')"
            by (simp add: prog_Sa)
          hence old_inv1: "inv1 (invContext' S')"
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
            hence userExists_query3:  
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
                  using `calls S'b ca = None`
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
                    proof (auto simp add: inv1_def S'd_def S'c_def S'b_def S'a_def S''_def)

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
                        hence [simp]: "i \<noteq> r" and [simp]: "i \<noteq> g"
                          by blast+
                            \<comment> \<open> Alternatively, we could prove that they are not equal because there are no call in i and we need calls for i-happens-before \<close>


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
                          using `calls S'' c = None` by (simp add: S''_def)
                        hence [simp]: "callOrigin S' c = None"
                          by (simp add: S'_wf)

                        have [simp]: "calls S' ca = None"
                          using `calls S'b ca = None` by (simp add: S''_def S'b_def S'a_def)
                        hence [simp]: "callOrigin S' ca = None"
                          by (simp add: S'_wf)

                        have [simp]: "transactionOrigin S' t = None"
                          by (simp add: a17)


                        have cx': "i_callOriginI_h (callOrigin S') (transactionOrigin S') cx \<triangleq> r"
                          using cx by (auto simp add: i_callOriginI_h_simps split: if_splits option.splits)

                        have cy': "i_callOriginI_h (callOrigin S') (transactionOrigin S') cy \<triangleq> g"
                          using cy by (auto simp add: i_callOriginI_h_simps split: if_splits option.splits)

                        have "(r, g) \<in> invocation_happensBefore (invContext' S')"
                          using c2 apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def split: option.splits if_splits)
                          apply (drule_tac x=cx in spec)
                          apply auto
                          apply (drule_tac x=cy in spec)
                          apply (auto simp add: hb'c_def S'a_def updateHb_cons S'b_def S''_def)
                          done
                        thus ?thesis
                          using old_inv1[simplified inv1_def] c0 c1 c3 by auto

                      qed
                    qed

                    show "inv2 (invContext' S'd)"
                      using old_inv2
                      apply (auto simp add: inv2_def S'd_def S'c_def S'b_def S'a_def S''_def)
                      by (auto simp add: i_callOriginI_h_simps split: if_splits)

                    from userExists_query3 and `res_userExists = Bool True`
                    obtain cw
                      where existsWrite: "(\<exists>v. calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_name_assign [UserId u, v] Undef
                           \<or> calls (getContextH (calls S') (happensBefore S') (Some vis')) cw \<triangleq> Call users_mail_assign [UserId u, v] Undef)"
                        and writeNotOverridden: "\<And>crr. calls (getContextH (calls S') (happensBefore S') (Some vis')) crr \<triangleq> Call users_remove [UserId u] Undef \<Longrightarrow>
                           (crr, cw) \<in> happensBefore (getContextH (calls S') (happensBefore S') (Some vis'))"
                      by auto
                    find_theorems res_userExists

                    show "inv3 (invContext' S'd)"
                      using old_inv3
                      apply (auto simp add: hb'c_def updateHb_cons inv3_def S'd_def S'c_def S'b_def S'a_def S''_def)
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
                        hence "(delete, cw) \<in> happensBefore S'"
                          by (auto simp add: getContextH_def  restrict_relation_def)
                        thus False
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
                        using S'd_inv1 by (auto simp add: S'e_def inv1_def)

                      show "inv2 (invContext' S'e)"
                        using S'd_inv2 by (auto simp add: S'e_def inv2_def)

                      show "inv3 (invContext' S'e)"
                        using S'd_inv3 by (auto simp add: S'e_def inv3_def)
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
                  proof (auto simp add: inv1_def S'c_def S'b_def S'a_def S''_def)



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
                        apply (auto simp add:  invocation_happensBeforeH_def  i_callOriginI_h_def updateHb_cons split: option.splits if_splits)
                        by (metis S'_wf \<open>calls S' c = None\<close> a15 option.distinct(1) wellFormed_callOrigin_dom2 wellFormed_state_callOrigin_transactionStatus)

                      show "invocationRes S' g \<triangleq> g_res"
                        using c3 .
      
                    qed
                  qed
                  have no_co_t: "\<And>c. callOrigin S' c \<noteq> Some t"
                    by (simp add: a16)


                  show "inv2 (invContext' S'c)"
                    using old_inv2
                    apply (auto simp add: inv2_def S'c_def S'b_def S'a_def S''_def)
                    by (auto simp add: i_callOriginI_h_simps no_co_t)

                  show "inv3 (invContext' S'c)"
                    using old_inv3
                    by (auto simp add: inv3_def S'c_def S'b_def S'a_def S''_def updateHb_cons)
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
                    using `inv (invContext' S'c)`
                    by  (auto simp add: inv_def inv1_def inv2_def inv3_def S'd_def)
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


        from `invariant (prog Sa) (invContext' S')`
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

            from `calls S'' c = None`
            have "calls S' c = None"
              by (auto simp add: S''_def)
            hence [simp]: "callOrigin S' c = None"
              using S'_growth state_monotonicGrowth_wf2 wellFormed_callOrigin_dom3 by blast

            from ` transactionOrigin S' t = None`
            have no_tx_in_i: "transactionOrigin S' x \<noteq> Some i" for x
              using no_transaction_in_i_Sa transactionOriginSa by blast

            have no_call_in_t_S'_h: "x\<noteq>t" if "callOrigin S' c \<triangleq> x" for c x
              using no_call_in_t_S' that by blast

            from `calls S'' c = None`
            have "calls S' c = None"
              by (simp add: S''_def)

            hence c_no_hb: "(c, c') \<notin> happensBefore S'" for c'
              using wf_S' wellFormed_happensBefore_calls_l by blast

            show "example_userbase.inv (invContext' S'b)"
            proof
              show "inv1 (invContext' S'b)"
              proof (auto simp add: inv1_def S'b_def S'a_def S''_def)




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
                  hence [simp]: "i \<noteq> g" by blast

                  have "r\<noteq>i"
                  proof 
                    assume [simp]: "r = i"
                    text \<open>This case is not possible, as there cannot be any calls that happened after the new call c. \<close>






                    from `(r, g) \<in> invocation_happensBeforeH (i_callOriginI_h (callOrigin S'(c \<mapsto> t)) (transactionOrigin S'(t \<mapsto> i))) hb'`
                    show False
                      apply (auto simp add: invocation_happensBeforeH_def i_callOriginI_h_def hb'_def updateHb_cons S''_def  split: option.splits if_splits)
                      by (auto simp add: no_tx_in_i no_call_in_t_S' no_call_in_t_S'_h c_no_hb)
                  qed
                  hence [simp]: "i\<noteq> r" and [simp]: "r \<noteq>i" by blast+





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
                    apply (auto simp add: h1 h2 invocation_happensBeforeH_def hb'_def updateHb_cons S''_def)
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
                apply (auto simp add: inv2_def S'b_def S'a_def S''_def)
                using no_call_in_t_S'   by (auto simp add: i_callOriginI_h_simps split: if_splits)

              show "inv3 (invContext' S'b) "
                using inv3_S'
                using c_no_hb by (auto simp add: inv3_def S'b_def S'a_def S''_def hb'_def updateHb_cons)
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
                by (auto simp add: S'c_def S'a_def S''_def)
              have [simp]: "calls S'c c \<triangleq> Call users_remove [UserId u] Undef"
                apply (auto simp add: S'c_def S'a_def)
                using a1 by (auto simp add: progr_def crdtSpec_def)

              show "inv (invContext' S'd)"
              proof 
                show "inv1 (invContext' S'd)"
                  using `inv (invContext' S'c)`
                  by (auto simp add: inv_def inv1_def S'd_def)

                show "inv2 (invContext' S'd)"
                  using `inv (invContext' S'c)`
                  by (auto simp add: inv_def inv2_def S'd_def)

                show "inv3 (invContext' S'd)"
                  using `inv (invContext' S'c)`
                  by (auto simp add: inv_def inv3_def S'd_def)
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



        from `invariant (prog Sa) (invContext' S')`
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
                    using `calls S'b ca = None`
                    by (auto simp add: S'b_def)

                  have [simp]: "cb \<noteq> ca" and [simp]: "ca \<noteq> cb"
                    using `calls S'd cb = None`
                    by (auto simp add: S'd_def)

                  have [simp]: "c \<noteq> cb" and [simp]: "cb \<noteq> c"
                    using `calls S'd cb = None`
                    by (auto simp add: S'd_def S'b_def)

                  have [simp]: "calls S' c = None"
                    using `calls S'a c = None`
                    by (auto simp add: S'a_def)

                  have [simp]: "calls S' ca = None"
                    using `calls S'b ca = None`
                    by (auto simp add: S'b_def S'a_def)
                  have [simp]: "calls S' cb = None"
                    using `calls S'd cb = None`
                    by (auto simp add: S'd_def S'b_def S'a_def)

                  have [simp]: "callOrigin S' c = None"
                    and [simp]: "callOrigin S' ca = None"
                    and [simp]: "callOrigin S' cb = None"
                    by (auto simp add: S'_wf)

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
                      using inv1_S' apply (auto simp add: inv1_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def updateHb_chain)
                      apply (subst(asm) updateHb_chain, force, simp)
                      apply (subst(asm) ihb_simps)
                      by auto


                    show "inv2 (invContext' S'f)"
                      using inv2_S'  apply (auto simp add: inv2_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def cong: conj_cong)
                      by (auto simp add: i_callOriginI_h_simps)

                    show "inv3 (invContext' S'f)"
                      using inv3_S' by (auto simp add: inv3_def S'f_def S'e_def hb'e_def S'd_def hb'd_def hb'_def S'b_def S'a_def  updateHb_cons cong: conj_cong)
                  qed
                  hence "inv1 (invContext' S'f)" and "inv2 (invContext' S'f)" and "inv3 (invContext' S'f)"
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
                        using `inv1 (invContext' S'f)` apply (auto simp add: inv1_def S'g_def)
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
                        from `inv2 (invContext' S'f)`
                        have cr_info_def: "cr_info = Call users_remove [UserId u] Undef"
                          using r_removeUser cr_info cr_t cr_t_r by (auto simp add: inv2_def)


                        text \<open>By invariant 3 there is no assignment after the remove:\<close>
                        from `inv3 (invContext' S'f)`
                        thm `inv3 (invContext' S'f)`[simplified inv3_def,rule_format]
                        have cr_no_later_write: "\<nexists>write v.
                           (calls (invContext' S'f) write \<triangleq> Call users_name_assign [UserId u, v] Undef 
                          \<or> calls (invContext' S'f) write \<triangleq> Call users_mail_assign [UserId u, v] Undef) 
                         \<and>(cr, write) \<in> happensBefore (invContext' S'f)"
                          using \<open>cr_info = Call users_remove [UserId u] Undef\<close> cr_info  by (auto simp add: inv3_def)

                        have [simp]: "calls S'a c = None"
                          by (simp add: call_c_None)

                        have [simp]: "calls S'a ca = None"
                          using `calls S'b ca = None`
                          by (auto simp add: S'b_def)

                        have [simp]: "calls S'a cb = None"
                          using `calls S'd cb = None`
                          by (auto simp add: S'd_def S'b_def)



                        from cr_no_later_write
                        have cr_no_later_write': "\<nexists>write v.
                           (calls (invContext' S'a) write \<triangleq> Call users_name_assign [UserId u, v] Undef 
                          \<or> calls (invContext' S'a) write \<triangleq> Call users_mail_assign [UserId u, v] Undef) 
                         \<and>(cr, write) \<in> happensBefore (invContext' S'a)"
                          apply (auto simp add: S'f_def S'e_def S'd_def S'b_def hb'e_def hb'd_def hb'_def split: if_splits)
                           apply (drule_tac x="write" in spec)
                          apply auto
                          apply (auto simp add: updateHb_cons)
                          apply (drule_tac x="write" in spec)
                          apply (auto simp add: updateHb_cons)
                          done

                        from `calls S'f cr \<triangleq> cr_info`
                        have [simp]: "calls S'a cr = Some (Call users_remove [UserId u] Undef)"
                          by (auto simp add: cr_info_def S'f_def S'b_def S'c_def S'd_def S'e_def split: if_splits)

                        from `(cr, c)\<in>happensBefore S'f`
                        have "(cr, c) \<in> updateHb (happensBefore S'a) vis' [c, ca, cb]"
                          apply (auto simp add: S'f_def S'e_def hb'e_def S'd_def hb'd_def S'b_def hb'_def updateHb_chain)
                          apply (subst(asm) updateHb_chain)
                          by auto

                        hence [simp]: "cr \<in> vis'"
                          by (metis S'a_wf \<open>calls S'a ca = None\<close> \<open>calls S'a cr \<triangleq> Call users_remove [UserId u] Undef\<close> call_c_None in_sequence_cons option.distinct(1) single_invocation_correctness.updateHb_nil updateHb_cases wellFormed_happensBefore_calls_r)

                        text \<open>But that is not compatible with the result we got for the query:\<close>
                        from `querySpec progr users_contains_key [UserId u] (getContextH (calls S'a) (happensBefore S'a) (Some vis')) res_contains`
                        show False
                          using cr_no_later_write' by (auto simp add: progr_def crdtSpec_def getContextH_def restrict_map_def restrict_relation_def `res_contains = Bool True` split: if_splits)
                      qed

                      show "inv2 (invContext' S'g)"
                        using `inv2 (invContext' S'f)` by (auto simp add: inv2_def S'g_def)
                      show "inv3 (invContext' S'g)"
                        using `inv3 (invContext' S'f)` by (auto simp add: inv3_def S'g_def)
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

              from `calls S'a c = None`
              have [simp]: "callOrigin S' c = None"
                by (auto simp add: S'a_def S'_wf)

              have [simp]: "transactionOrigin S' t = None"
                by (simp add: a17)

              have [simp]: "transactionOrigin S' t \<noteq> Some i" for i
                by simp

                find_theorems c

              show "example_userbase.inv (invContext' S'c)"
              proof
                show "inv1 (invContext' S'c)"
                  apply (auto simp add: inv1_def S'c_def S'b_def S'a_def hb'_def)
                  apply (subst(asm) invocation_happensBeforeH_one_transaction_simp)
                             apply auto
                  using Sa_wf a7 invoc_Sa wf_no_invocation_no_origin apply auto[1]
                  using a16 apply blast
                  apply (meson S'_wf not_None_eq wf_callOrigin_implies_transactionStatus_defined wf_transactionOrigin_and_status)
                  apply (meson S'_wf option.exhaust wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_l)
                  apply (meson S'_wf option.exhaust wellFormed_callOrigin_dom3 wellFormed_happensBefore_calls_r)
                  using inv1_S' inv1_def by auto

                show "inv2 (invContext' S'c)"
                  using `inv2 (invContext' S')`  by (auto simp add: inv2_def S'c_def S'b_def S'a_def hb'_def i_callOriginI_h_simps)
                show "inv3 (invContext' S'c)"
                  using `inv3 (invContext' S')`  
                  by (auto simp add: inv3_def S'c_def S'b_def S'a_def hb'_def updateHb_cons)
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
                    using `inv (invContext' S'c)`
                    by (auto simp add: inv_def inv1_def S'd_def S'c_def)

                    show "inv2 (invContext' S'd)"
                    using `inv (invContext' S'c)`
                    by (auto simp add: inv_def inv2_def S'd_def S'c_def)

                  show "inv3 (invContext' S'd)"
                    using `inv (invContext' S'c)`
                    by (auto simp add: inv_def inv3_def S'd_def S'c_def)
                qed

              qed
            qed
          qed
        qed     
      qed
    qed
  qed
qed

end