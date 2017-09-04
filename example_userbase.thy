theory example_userbase
imports approach
begin

datatype val =
    String string
  | UserId int
  | Bool bool
  | Undef

record localState = 
  ls_pc :: nat
  ls_u :: val
  ls_name :: string
  ls_mail :: string
  ls_exists :: bool

definition initialState :: "localState" where
"initialState = \<lparr>
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
   
definition procedures where
"procedures proc args \<equiv> 
  if proc = ''registerUser'' then
    case args of 
      [String name, String mail] \<Rightarrow> 
        Some (initialState\<lparr>ls_name := name, ls_mail := mail \<rparr> , registerUserImpl)
      | _ \<Rightarrow> None
  else 
    None"

    
    
definition prog :: "(localState, val) prog" where
"prog \<equiv> \<lparr>
  querySpec = ???,
  procedure = procedures,
  invariant = ???
\<rparr>"



end