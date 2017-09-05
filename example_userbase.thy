theory example_userbase
imports approach
begin


definition 
"i_callOriginI ctxt c \<equiv> 
  case i_callOrigin ctxt c of Some t \<Rightarrow> i_transactionOrigin ctxt t | None \<Rightarrow> None"

text {* lifting the happensBefore relation on database-calls to the level of invocations. *}
definition 
"invocation_happensBefore ctxt \<equiv> 
  {(x,y). (\<exists>c. i_callOriginI ctxt c \<triangleq> x) 
        \<and> (\<exists>c. i_callOriginI ctxt c \<triangleq> y) 
        \<and> (\<forall>cx cy. i_callOriginI ctxt cx \<triangleq> x
                 \<and> i_callOriginI ctxt cy \<triangleq> y
                 \<longrightarrow> (cx,cy)\<in>happensBefore ctxt)}"


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

definition registerUserImpl :: "(localState, val) procedureImpl" where
"registerUserImpl ls \<equiv> [
   (* 0 *) NewId (\<lambda>x. (ls\<lparr>ls_u := x, ls_pc := 1\<rparr> :: localState)),
   (* 1 *) BeginAtomic (ls\<lparr>ls_pc := 2\<rparr>),
   (* 2 *) DbOperation ''users_name_assign'' [ls_u ls, String (ls_name ls)] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) DbOperation ''users_mail_assign'' [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) EndAtomic (ls\<lparr>ls_pc := 5\<rparr>),
   (* 5 *) Return (ls_u ls)
   ] ! ls_pc ls"

definition updateMailImpl :: "(localState, val) procedureImpl" where
"updateMailImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation ''users_contains_key'' [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   (* 2 *) LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 4\<rparr> ),
   (* 3 *) DbOperation ''users_mail_assign'' [ls_u ls, String (ls_mail ls)] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 5 *) EndAtomic  (ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) Return Undef
   ] ! ls_pc ls"   
   
definition removeUserImpl :: "(localState, val) procedureImpl" where
"removeUserImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation ''users_remove'' [ls_u ls] (\<lambda>r. ls\<lparr>ls_pc := 2 \<rparr>),
   (* 2 *) EndAtomic  (ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) Return Undef
   ] ! ls_pc ls"      
   
definition getUserImpl :: "(localState, val) procedureImpl" where
"getUserImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation ''users_contains_key'' [ls_u ls] (\<lambda>r. ls\<lparr>ls_exists := (r = Bool True), ls_pc := 2 \<rparr>),
   (* 2 *) LocalStep (if ls_exists ls then ls\<lparr>ls_pc := 3\<rparr> else ls\<lparr>ls_pc := 5\<rparr> ),
   (* 3 *) DbOperation ''users_name_get'' [ls_u ls] (\<lambda>r. ls\<lparr>ls_name := stringval r, ls_pc := 4 \<rparr>),
   (* 4 *) DbOperation ''users_mail_get'' [ls_u ls] (\<lambda>r. ls\<lparr>ls_mail := stringval r, ls_pc := 5 \<rparr>),
   (* 5 *) EndAtomic  (ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) Return (if ls_exists ls then Found (ls_name ls) (ls_mail ls) else NotFound )
   ] ! ls_pc ls"      
   
   
definition procedures where
"procedures proc args \<equiv> 
  if proc = ''registerUser'' then
    case args of 
      [String name, String mail] \<Rightarrow> 
        Some (lsInit\<lparr>ls_name := name, ls_mail := mail \<rparr> , registerUserImpl)
      | _ \<Rightarrow> None
  else if proc = ''updateMail'' then 
    case args of 
      [UserId u, String mail] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u, ls_mail := mail \<rparr> , updateMailImpl)
      | _ \<Rightarrow> None
  else if proc = ''removeUser'' then 
    case args of 
      [UserId u] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u \<rparr> , removeUserImpl)
      | _ \<Rightarrow> None
  else if proc = ''getUser'' then 
    case args of 
      [UserId u] \<Rightarrow> 
        Some (lsInit\<lparr>ls_u := UserId u \<rparr> , getUserImpl)
      | _ \<Rightarrow> None  
  else 
    None"


definition latest_name_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
"latest_name_assign ctxt u \<equiv>  {v | c1 v. 
     calls ctxt c1 \<triangleq> Call ''users_name_assign'' [u, v] Undef
   \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call ''users_remove'' [u] Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call ''users_name_assign'' [u] v' \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"

definition latest_mail_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
"latest_mail_assign ctxt u \<equiv>  {v | c1 v. 
     calls ctxt c1 \<triangleq> Call ''users_mail_assign'' [u, v] Undef
   \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call ''users_remove'' [u] Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call ''users_mail_assign'' [u] v' \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"   
   
definition crdtSpec :: "operation \<Rightarrow> val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec oper args ctxt res \<equiv> 
  if oper \<in> {''users_name_assign'', ''users_mail_assign'', ''users_remove''} then
    (* update-operations always return Undef *)
    res = Undef
  else if oper = ''users_contains_key'' then
    res = Bool (\<exists>c1 v. (calls ctxt c1 \<triangleq> Call ''users_name_assign'' (args @ [v]) Undef
                 \<or> calls ctxt c1 \<triangleq> Call ''users_mail_assign'' (args @ [v]) Undef)
               \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call ''users_remove'' args Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt))
  else if oper = ''users_name_get'' then 
    if latest_name_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_name_assign ctxt (hd args)
  else if oper = ''users_mail_get'' then 
    if latest_mail_assign ctxt (hd args) = {} then 
      res = Undef
    else
      res \<in> latest_mail_assign ctxt (hd args)
  else
    False"
  
definition inv1 :: "val invariantContext \<Rightarrow> bool" where
"inv1 ctxt \<equiv> \<forall>r g u.
    i_invocationOp ctxt r \<triangleq> (''removeUser'', [u])
  \<and> i_invocationOp ctxt g \<triangleq> (''getUser'', [u])
  \<and> (r,g) \<in> invocation_happensBefore ctxt
  \<longrightarrow> i_invocationRes ctxt g \<triangleq> NotFound"
  
definition inv2 :: "val invariantContext \<Rightarrow> bool" where
"inv2 ctxt \<equiv> \<forall>u i.
    i_invocationOp ctxt i \<triangleq> (''removeUser'', [u])
  \<and> i_invocationRes ctxt i \<noteq> None
  \<longrightarrow> (\<exists>c. i_callOriginI ctxt c \<triangleq> i \<and> calls ctxt c \<triangleq> Call ''users_remove'' [u] Undef)"
  
definition inv3 :: "val invariantContext \<Rightarrow> bool" where
"inv3 ctxt \<equiv> \<not>(\<exists>write delete u v.
  (calls ctxt write \<triangleq> Call ''users_name_assign'' [u, v] Undef
    \<or> calls ctxt write \<triangleq> Call ''users_mail_assign'' [u, v] Undef)
  \<and> (calls ctxt delete \<triangleq> Call ''users_remove'' [u] Undef)
  \<and> (delete, write) \<in> happensBefore ctxt
  )"
  
definition inv :: "val invariantContext \<Rightarrow> bool" where
"inv ctxt \<equiv> inv1 ctxt \<and> inv2 ctxt \<and> inv3 ctxt"
  
definition prog :: "(localState, val) prog" where
"prog \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"

theorem "programCorrect prog"
proof (rule show_correctness_via_single_session)
  show "invariant_all (replissSem1.initialState prog)"
     by (auto simp add: initialState_def invariant_all_def prog_def inv_def inv1_def inv2_def inv3_def invContextH_def)
  
  show "programCorrect_s example_userbase.prog"
  apply (auto simp add: programCorrect_s_def)
  apply (auto simp add: prog_def step_s.simps)



end