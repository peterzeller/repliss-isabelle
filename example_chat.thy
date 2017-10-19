theory example_chat
imports invariant_simps
begin




(* ^^^^ *)

datatype val =
      String string
    | UserId int
    | ChatId int
    | MessageId int
    | Bool bool
    | Undef
    | ListVal "val list"
    

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
  ls_c :: val

definition lsInit :: "localState" where
"lsInit = \<lparr>
  ls_pc = 0,
  ls_t = Undef,
  ls_from = Undef,
  ls_content = Undef,
  ls_to = Undef,
  ls_id = Undef,
  ls_c = Undef
\<rparr>"
  

definition sendMessageImpl :: "(localState, val) procedureImpl" where
"sendMessageImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) NewId (\<lambda>x. (ls\<lparr>ls_t := x, ls_pc := 2\<rparr> :: localState)),
   (* 2 *) DbOperation ''message_author_assign'' [ls_t ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) DbOperation ''message_content_assign'' [ls_t ls, ls_content ls] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) DbOperation ''message_chat_assign'' [ls_t ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 5\<rparr>),
   (* 5 *) DbOperation ''chat_add'' [ls_to ls, ls_t ls] (\<lambda>r. ls\<lparr>ls_pc := 6\<rparr>),
   (* 6 *) EndAtomic (ls\<lparr>ls_pc := 6\<rparr>),
   (* 7 *) Return (ls_t ls)
   ] ! ls_pc ls"

definition editMessageImpl :: "(localState, val) procedureImpl" where
"editMessageImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation ''message_exists'' [ls_id ls] (\<lambda>r. if r = Bool True then ls\<lparr>ls_pc := 2\<rparr> else ls\<lparr>ls_pc := 3\<rparr>),
   (* 2 *) DbOperation ''message_content_assign'' [ls_id ls, ls_content ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) EndAtomic  (ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) Return Undef
   ] ! ls_pc ls"   
   
definition deleteMessageImpl :: "(localState, val) procedureImpl" where
"deleteMessageImpl ls \<equiv> [
   (* 0 *) BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   (* 1 *) DbOperation ''message_chat_read'' [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 2, ls_c := r\<rparr>),
   (* 2 *) DbOperation ''chat_remove'' [ls_c ls, ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   (* 3 *) DbOperation ''message_delete'' [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   (* 4 *) EndAtomic  (ls\<lparr>ls_pc := 5\<rparr>),
   (* 5 *) Return Undef
   ] ! ls_pc ls"      
   
   
definition procedures where
"procedures proc args \<equiv> 
  if proc = ''sendMessage'' then
    case args of 
      [UserId from, String content, ChatId to] \<Rightarrow> 
        Some (lsInit\<lparr>ls_from := UserId from, ls_content := String content, ls_to := ChatId to \<rparr> , sendMessageImpl)
      | _ \<Rightarrow> None
  else if proc = ''editMessage'' then 
    case args of 
      [MessageId i] \<Rightarrow> 
        Some (lsInit\<lparr>ls_id := MessageId i \<rparr> , editMessageImpl)
      | _ \<Rightarrow> None
  else if proc = ''deleteMessage'' then 
    case args of 
      [MessageId i] \<Rightarrow> 
        Some (lsInit\<lparr>ls_id := MessageId i \<rparr> , deleteMessageImpl)
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

definition crdtSpec_message_chat_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec_message_chat_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
   (\<exists>c1. calls ctxt c1 \<triangleq> Call ''message_chat_assign'' (args@[v]) Undef
     \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call ''message_chat_assign'' (args@[v']) Undef \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call ''message_delete'' args Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)))"

definition crdtSpec_message_author_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec_message_author_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
   (\<exists>c1. calls ctxt c1 \<triangleq> Call ''message_author_assign'' (args@[v]) Undef
     \<and> (\<forall>c2 v'. calls ctxt c2 \<triangleq> Call ''message_author_assign'' (args@[v']) Undef \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2. calls ctxt c2 \<triangleq> Call ''message_delete'' args Undef \<longrightarrow> (c2,c1)\<in>happensBefore ctxt)))"

definition is_message_updateH  where
 (*:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where *)
"is_message_updateH state_calls c mid \<equiv> 
  case state_calls c of 
     Some (Call upd (mid'#args) _) \<Rightarrow> upd \<in> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''} \<and> mid = mid' 
   | _ \<Rightarrow> False"


abbreviation is_message_update :: "(val, 'b) operationContext_scheme \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where
 (*:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where *)
"is_message_update ctxt \<equiv> is_message_updateH (calls ctxt)"

definition crdtSpec_message_exists_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
"crdtSpec_message_exists_h args ctxt \<equiv> 
  \<exists>mId.
  args = [mId]
 \<and> (\<exists>c. is_message_update ctxt c mId)
 \<and> (\<forall>c. calls ctxt c \<triangleq> Call ''message_delete'' args Undef 
        \<longrightarrow> (\<exists>c'. (c,c')\<in>happensBefore ctxt \<and> is_message_update ctxt c mId))"

definition crdtSpec_message_exists :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec_message_exists args ctxt res \<equiv> 
  res = Bool (crdtSpec_message_exists_h args ctxt)"

(* ignores map-deletes as they are not used *)
definition crdtSpec_chat_contains_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
"crdtSpec_chat_contains_h args ctxt \<equiv> 
  (\<exists>c. calls ctxt c \<triangleq> Call ''chat_add'' args Undef
      \<and> (\<nexists>c'. calls ctxt c \<triangleq> Call ''chat_remove'' args Undef \<and> (c,c') \<in> happensBefore ctxt))"

definition crdtSpec_chat_contains :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec_chat_contains args ctxt res \<equiv> 
  res = Bool (crdtSpec_chat_contains_h args ctxt)"


definition crdtSpec :: "operation \<Rightarrow> val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
"crdtSpec oper  \<equiv> 
  if oper = ''message_chat_read'' then crdtSpec_message_chat_read
  else if oper = ''message_author_read'' then crdtSpec_message_author_read
  else if oper = ''chat_contains'' then crdtSpec_chat_contains
  else if oper = ''message_exists'' then crdtSpec_message_exists
  else 
    (* other operations are updates and don't have a result *)
    (\<lambda>args ctxt res. res = Undef)"


definition mkContext :: "'a invariantContext \<Rightarrow> 'a operationContext" where
"mkContext ctxt \<equiv> \<lparr>
  calls = calls ctxt |` i_visibleCalls ctxt,
  happensBefore = happensBefore ctxt  |r i_visibleCalls ctxt
\<rparr>"

lemma mkContext_calls_simps: "calls (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) 
= state_calls |` (commitedCallsH state_callOrigin state_transactionStatus \<inter> (vis orElse {}))"
  by (auto simp add: mkContext_def invContextH_def )

lemma mkContext_calls_eq_simps: "calls (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) c \<triangleq> x
\<longleftrightarrow> (isCommittedH state_callOrigin state_transactionStatus c \<and> c \<in> vis orElse {} \<and> state_calls c \<triangleq> x)"
  by (auto simp add: mkContext_def invContextH_def commitedCallsH_def  restrict_map_def)

lemma mkContext_happensBefore_simps: "happensBefore (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) 
= state_happensBefore |r commitedCallsH state_callOrigin state_transactionStatus |r (vis orElse {})"
  by (auto simp add: mkContext_def invContextH_def )

lemma mkContext_happensBefore_contains_simps: "(c1,c2) \<in> happensBefore (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) 
= ( (c1, c2) \<in> state_happensBefore 
    \<and> isCommittedH state_callOrigin state_transactionStatus c1 \<and> c1 \<in> vis orElse {} 
    \<and> isCommittedH state_callOrigin state_transactionStatus c2 \<and> c2 \<in> vis orElse {}
            )"
  by (auto simp add: mkContext_def invContextH_def commitedCallsH_def restrict_map_def restrict_relation_def)

lemmas mkContext_simps = mkContext_happensBefore_contains_simps mkContext_calls_eq_simps

(* property 1 *)
definition inv1 :: "val invariantContext \<Rightarrow> bool" where
"inv1 ctxt \<equiv> \<forall>c m. crdtSpec_chat_contains_h [c,m] (mkContext ctxt) \<longrightarrow> crdtSpec_message_exists_h [m] (mkContext ctxt)"

(* property 2 *)
definition inv2 :: "val invariantContext \<Rightarrow> bool" where
"inv2 ctxt \<equiv> \<forall>m. crdtSpec_message_exists_h [m] (mkContext ctxt) \<longrightarrow> (\<exists>a. crdtSpec_message_author_read [m] (mkContext ctxt) (ListVal [a]))"

definition inv2_h1 :: "val invariantContext \<Rightarrow> bool" where
"inv2_h1 ctxt \<equiv> (\<forall>c mId. calls ctxt c \<triangleq> Call ''message_delete'' [mId] Undef \<longrightarrow> (\<nexists>c'. is_message_update ctxt c' mId \<and> (c,c')\<in>happensBefore ctxt ))"
  
  
definition inv :: "val invariantContext \<Rightarrow> bool" where
"inv ctxt \<equiv> inv1 ctxt \<and> inv2 ctxt \<and> inv2_h1 ctxt"
  
definition progr :: "(localState, val) prog" where
"progr \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"

lemma [simp]: "querySpec progr = crdtSpec" by (simp add: progr_def)
lemma [simp]: "procedure progr = procedures" by (simp add: progr_def)
lemma [simp]: "invariant progr = inv" by (simp add: progr_def)

(*
definition initialStates :: "('localState, 'any) prog \<Rightarrow> invocation \<Rightarrow> ('localState, 'any) state set"  where
"initialStates progr i \<equiv> {
    (S\<lparr>localState := (localState S)(i \<mapsto> initState),
       currentProc := (currentProc S)(i \<mapsto> impl),
       visibleCalls := (visibleCalls S)(i \<mapsto> {}),
       invocationOp := (invocationOp S)(i \<mapsto> (procName, args))\<rparr>) 
 | S procName args initState impl.
    prog S = progr
  \<and> procedure progr procName args \<triangleq> (initState, impl)  
  \<and> uniqueIdsInList args \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> state_wellFormed S (*  TODO add wellformed? *)
  \<and> invocationOp S i = None
}"
*)

lemma initialStates_impl:
  assumes "S \<in> initialStates program i"
  shows "\<exists>procName args initState impl S_pre.  
      procedure program procName args \<triangleq> (initState, impl) 
   \<and> localState S i \<triangleq> initState 
   \<and> currentProc S i \<triangleq> impl 
   \<and> invocationOp  S i \<triangleq> (procName, args) 
   \<and> uniqueIdsInList args \<subseteq> knownIds S
"
  using assms by (auto simp add: initialStates_def)

lemma initialStates_prog:
  assumes "S \<in> initialStates program i"
  shows "prog S = program"
  using assms by (auto simp add: initialStates_def)

lemma initialStates_vis:
  assumes "S \<in> initialStates program i"
  shows "visibleCalls S i \<triangleq> {}"
  using assms by (auto simp add: initialStates_def)

lemma initialStates_currentTransaction:
  assumes "S \<in> initialStates program i"
  shows "currentTransaction S i = None"
  using assms apply (auto simp add: initialStates_def)
  using wellFormed_invoc_notStarted(1) by blast





schematic_goal [simp]: "procedure progr = ?p"
  by (simp add: progr_def)

lemma pc_init[simp]: "ls_pc lsInit = 0"
  by (simp add: lsInit_def)


theorem "programCorrect progr"
proof (rule show_correctness_via_single_session)
  have [simp]: "invariant progr = inv" by (simp add: progr_def)

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)
  
  show "invariant_all (replissSem1.initialState progr)"
    by (auto simp add: initialState_def invariant_all_def inv_def inv1_def inv2_def inv2_h1_def invContextH_def crdtSpec_message_exists_h_def crdtSpec_chat_contains_h_def mkContext_def is_message_updateH_def)
  
     
     
  show "programCorrect_s progr"
  proof (rule show_program_correct_single_invocation)

    text {* First show that the invariant holds for the initial states (beginning of procedures) *}
    show "\<And>S i. S \<in> initialStates progr i \<Longrightarrow> invariant_all S"
    proof (auto simp add: invariant_all_def inv_def)
      fix S i vis
      assume a0: "S \<in> initialStates progr i"
         and vis_cs: "consistentSnapshot S vis"

      have [simp]: "prog S = progr"
        using a0 by auto
  
      
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
        using inv_def by blast
      thus "inv1 (invContextVis S vis)"
        apply (auto simp add: inv1_def  split: if_splits)
        apply (auto simp add:  crdtSpec_chat_contains_h_def crdtSpec_message_exists_h_def)
             apply (auto simp add: mkContext_simps  S_def)
            apply (auto simp add: mkContext_calls_simps )
        by fastforce+

      from pre_inv 
      have "inv2 (invContextVis Spre vis)"
        using inv_def by blast
      thus "inv2 (invContextVis S vis)"
        apply (auto simp add: inv2_def  split: if_splits)
        apply (auto simp add:  crdtSpec_message_exists_h_def crdtSpec_message_author_read_def)
        by (auto simp add: mkContext_simps  S_def mkContext_calls_simps)


         from pre_inv 
      have "inv2_h1 (invContextVis Spre vis)"
        using inv_def by blast
      thus "inv2_h1 (invContextVis S vis)"
        apply (auto simp add: inv2_h1_def  split: if_splits)
        by (auto simp add: S_def invContextH_def)
    qed




    text {* Next, check each procedure: *}
    show "checkCorrectAll progr S i" if "S \<in> initialStates progr i" for S i
    proof -
      from initialStates_impl[OF `S \<in> initialStates progr i`]
      have "checkCorrectAll progr S i" 
      proof (auto simp add: procedures_def split: if_splits list.splits val.splits)
        text {* Procedure editMessage *}
        fix mId
        assume a0: "invocationOp S i \<triangleq> (''editMessage'', [MessageId mId])"
          and a1[simp]: "currentProc S i \<triangleq> editMessageImpl"
          and a2[simp]: "localState S i \<triangleq> lsInit\<lparr>ls_id := MessageId mId\<rparr>"
          and a3: "uniqueIdsInList [MessageId mId] \<subseteq> knownIds S"

        have progS[simp]: "prog S = progr"
          using that by auto 
        have sameProg[simp]: "prog S' = progr" if "state_monotonicGrowth S S'" for S'
          using state_monotonicGrowth_prog that by force
        have [simp]: "currentTransaction S i = None" 
          using `S \<in> initialStates progr i`  initialStates_currentTransaction by blast 
        show "checkCorrectAll progr S i"
        proof (auto simp add: checkCorrectAll_simps editMessageImpl_def; (subst invariant_all_def)?; auto? )
          text {* We have to show that progress can be made for the query. This is not really necessary for partial correctness but otherwise the program could get stuck.  *}
          show "\<And>t S'. \<lbrakk>transactionStatus S t = None; invariant_all S'; state_wellFormed S'; state_monotonicGrowth S S'; localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>;
             currentProc S' i \<triangleq> editMessageImpl; currentTransaction S' i \<triangleq> t; transactionOrigin S' t \<triangleq> i\<rbrakk>
            \<Longrightarrow> Ex (crdtSpec ''message_exists'' [MessageId mId] (getContext S' i))"
            by (auto simp add: crdtSpec_def crdtSpec_message_exists_def)
          show "\<And>t S' c vis.
             \<lbrakk>transactionStatus S t = None; invariant_all S'; state_wellFormed S'; state_monotonicGrowth S S'; localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>;
              currentProc S' i \<triangleq> editMessageImpl; currentTransaction S' i \<triangleq> t; transactionOrigin S' t \<triangleq> i; calls S' c = None;
              crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True); visibleCalls S' i \<triangleq> vis\<rbrakk>
             \<Longrightarrow> Ex (crdtSpec ''message_content_assign'' [MessageId mId, ls_content lsInit]
                      (getContextH (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True))) (happensBefore S' \<union> vis \<times> {c}) (Some (insert c vis))))"
            by (auto simp add: crdtSpec_def)



          show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c8: "calls S' c = None"
              and c9: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)"
              and c10: "visibleCalls S' i \<triangleq> vis"
              and c11: "ca \<noteq> c"
              and c12: "calls S' ca = None"
              and c13: "crdtSpec ''message_content_assign'' [MessageId mId, ls_content lsInit] (getContextH (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True))) (happensBefore S' \<union> vis \<times> {c}) (Some (insert c vis))) resa"
              and c14: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)), happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
            for  t S' c vis ca resa visa
          proof (auto simp add: inv_def)
            have [simp]: "prog S' = progr"
              by (simp add: c3)

            have "consistentSnapshot S' (visa - {c,ca})"
            proof (auto simp add: consistentSnapshot_def)
              show "\<And>x. \<lbrakk>x \<in> visa; calls S' x = None; x \<noteq> c\<rbrakk> \<Longrightarrow> x = ca"
                using c14 by (auto simp add: consistentSnapshot_def)

              from c14 have cc: "causallyConsistent (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) visa"
                by (auto simp add: consistentSnapshot_def)
              from c14 have tc: "transactionConsistent (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) visa"
                by (auto simp add: consistentSnapshot_def)

              show "causallyConsistent (happensBefore S') (visa - {c, ca})"
              proof (auto simp add: causallyConsistent_def)
                show "\<And>c1 c2. \<lbrakk>c1 \<in> visa; c1 \<noteq> c; c1 \<noteq> ca; (c2, c1) \<in> happensBefore S'\<rbrakk> \<Longrightarrow> c2 \<in> visa"
                  by (meson UnCI causallyConsistent_def cc insert_iff)
                show "\<And>c1. \<lbrakk>c1 \<in> visa; c1 \<noteq> c; c1 \<noteq> ca; (c, c1) \<in> happensBefore S'\<rbrakk> \<Longrightarrow> False"
                  using c2 c8 wellFormed_happensBefore_calls_l by blast
                show "\<And>c1. \<lbrakk>c1 \<in> visa; c1 \<noteq> c; c1 \<noteq> ca; (ca, c1) \<in> happensBefore S'\<rbrakk> \<Longrightarrow> False"
                  using c12 c2 wellFormed_happensBefore_calls_l by blast
              qed

              show "transactionConsistent (callOrigin S') (transactionStatus S') (visa - {c, ca})"
              proof (auto simp add: transactionConsistent_def)

                show "transactionStatus S' tx \<triangleq> Commited"
                  if c0: "cb \<in> visa"
                    and c1: "cb \<noteq> c"
                    and c2: "cb \<noteq> ca"
                    and c3: "callOrigin S' cb \<triangleq> tx"
                  for  cb tx
                proof - 
                  from `callOrigin S' cb \<triangleq> tx` 
                  have "transactionStatus S tx \<noteq> None"
                    (* TODO this should be a wf-invariant *)
                    sorry

                  with `transactionStatus S t = None`
                  have "tx \<noteq> t"
                    by blast

                  have "(transactionStatus S'(t \<mapsto> Commited)) tx \<triangleq> Commited"
                  proof (rule transactionConsistent_Commited[OF tc `cb \<in> visa`])
                    show "(callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) cb \<triangleq> tx"
                      by (simp add: c1 c2 c3)
                    show "(callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) cb \<triangleq> tx"
                      by (simp add: that)
                  qed
                  
                  with `tx \<noteq> t`
                  show "transactionStatus S' tx \<triangleq> Commited"
                    by auto
                qed

                show "c2 \<in> visa"
                  if c0: "c1 \<in> visa"
                    and c1: "c1 \<noteq> c"
                    and c2: "c1 \<noteq> ca"
                    and c3: "callOrigin S' c1 = callOrigin S' c2"
                  for  c1 c2
                  sorry

                show "False"
                  if c0: "c1 \<in> visa"
                    and c1: "c1 \<noteq> c"
                    and c2: "c1 \<noteq> ca"
                    and c3: "callOrigin S' c1 = callOrigin S' c"
                  for  c1
                  sorry

                show "False"
                  if c0: "c1 \<in> visa"
                    and c1: "c1 \<noteq> c"
                    and c2: "c1 \<noteq> ca"
                    and c3: "callOrigin S' c1 = callOrigin S' ca"
                  for  c1
                  sorry
              qed



            from `invariant_all S'` have "inv (invContextVis S' (visa - {c,ca}))"
              apply (auto simp add: invariant_all_def)

            show "inv1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S') (invocationOp S')
           (invocationRes S') (Some visa))"
              apply (auto simp add: inv1_def crdtSpec_chat_contains_h_def  crdtSpec_message_exists_h_def mkContext_simps)
              
              find_theorems calls mkContext



          show "invariant (prog S') (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c8: "calls S' c = None"
              and c9: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)"
              and c10: "visibleCalls S' i \<triangleq> vis"
              and c11: "ca \<noteq> c"
              and c12: "calls S' ca = None"
              and c13: "crdtSpec ''message_content_assign'' [MessageId mId, ls_content lsInit] (getContextH (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True))) (happensBefore S' \<union> vis \<times> {c}) (Some (insert c vis))) resa"
              and c14: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)), happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
            for  t S' c vis ca resa visa
          proof (auto simp add: )



          show "invariant_all
                  (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa),
                        callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)),
                        happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>),
                        currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>)"  (is "invariant_all ?newS")
            if "transactionStatus S t = None" 
              "invariant_all S'" 
              "state_wellFormed S'" 
              "state_monotonicGrowth S S'" 
              "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              "currentProc S' i \<triangleq> editMessageImpl" 
              "currentTransaction S' i \<triangleq> t" 
              "transactionOrigin S' t \<triangleq> i" 
              "calls S' c = None"
              "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)" "visibleCalls S' i \<triangleq> vis" "ca \<noteq> c" "calls S' ca = None"
              "crdtSpec ''message_content_assign'' [MessageId mId, ls_content lsInit]
              (getContextH (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True))) (happensBefore S' \<union> vis \<times> {c}) (Some (insert c vis))) resa"
            for t S' c vis ca resa
          proof (auto simp add: invariant_all_def)
            fix vis'
            assume "consistentSnapshot ?newS vis'"
            show "invariant (prog S')
             (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
               (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S')
               (invocationOp S') (invocationRes S') (Some vis'))"
              apply (auto simp add: 


        
  qed

end