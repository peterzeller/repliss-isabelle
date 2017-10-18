theory example_chat
imports invariant_simps
begin




(* ^^^^ *)

datatype val =
      String string
    | ChatId int
    | MessageId int
    | Bool bool
    | Undef
    

fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"
  
record localState = 
  ls_pc :: nat
  ls_t :: val
  ls_from :: val
  ls_content :: val
  ls_to :: val
  ls_id :: val

definition lsInit :: "localState" where
"lsInit = \<lparr>
  ls_pc = 0,
  ls_t = Undef,
  ls_from = Undef,
  ls_content = Undef,
  ls_to = Undef,
  ls_id = Undef
\<rparr>"
  

definition sendMessageImpl :: "(localState, val) procedureImpl" where
"sendMessageImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) NewId (\<lambda>x. (ls\<lparr>ls_t := x, ls_pc := 2\<rparr> :: localState)),
   (* 2 *) DbOperation ''message_author_assign'' [ls_t ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) DbOperation ''message_author_assign'' [ls_t ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) DbOperation ''message_author_assign'' [ls_t ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 5\<rparr>),
   (* 5 *) EndAtomic (ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) Return (ls_t ls)
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
  
definition progr :: "(localState, val) prog" where
"progr \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"


theorem "programCorrect progr"
proof (rule show_correctness_via_single_session)
  have [simp]: "invariant progr = inv" by (simp add: progr_def)

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)
  
  show "invariant_all (replissSem1.initialState progr)"
     by (auto simp add: initialState_def invariant_all_def inv_def inv1_def inv2_def inv3_def invContextH_def)
  
     
     
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