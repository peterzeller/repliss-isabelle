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

definition "callsOfOp ctxt opName = {(c,args). calls ctxt c \<triangleq> Call opName args Undef}"

definition "callsWithOpArgs ctxt opName args = {c. calls ctxt c \<triangleq> Call opName args Undef}"


definition latest_name_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
  "latest_name_assign ctxt u \<equiv>  {v | c1 v. 
     (c1, [u, v]) \<in> callsOfOp ctxt ''users_name_assign''
   \<and> (\<forall>c2\<in>callsWithOpArgs ctxt ''users_remove'' [u]. (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>(c2, args) \<in> callsOfOp ctxt ''users_name_assign''. args!0 = u \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"

definition latest_mail_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
  "latest_mail_assign ctxt u \<equiv>  {v | c1 v. 
     (c1, [u, v]) \<in> callsOfOp ctxt ''users_mail_assign''
   \<and> (\<forall>c2\<in>callsWithOpArgs ctxt ''users_remove'' [u]. (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>(c2, args) \<in> callsOfOp ctxt ''users_mail_assign''. args!0 = u \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"   

definition crdtSpec_message_chat_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_chat_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
   (\<exists>c1\<in>callsWithOpArgs ctxt ''message_chat_assign'' (args@[v]).
       (\<forall>(c2,args')\<in>callsOfOp ctxt ''message_chat_assign''. take 1 args' = args \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2\<in>callsWithOpArgs ctxt ''message_delete'' args. (c2,c1)\<in>happensBefore ctxt)))"

definition crdtSpec_message_author_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_author_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
    (\<exists>c1\<in>callsWithOpArgs ctxt ''message_author_assign'' (args@[v]).
       (\<forall>(c2,args')\<in>callsOfOp ctxt ''message_author_assign''. take 1 args' = args \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2\<in>callsWithOpArgs ctxt ''message_delete'' args. (c2,c1)\<in>happensBefore ctxt)))"

definition is_message_updateH  where
  (*:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where *)
  "is_message_updateH mid c \<equiv> 
  case c of 
     Call upd (mid'#args) _ \<Rightarrow> upd \<in> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''} \<and> mid = mid' 
   | _ \<Rightarrow> False"

lemma is_message_updateH_simp: "is_message_updateH mid (Call upd (mid'#args) res) \<longleftrightarrow> upd \<in> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''} \<and> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp1[simp]: "is_message_updateH mid (Call ''message_author_assign'' (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp2[simp]: "is_message_updateH mid (Call ''message_content_assign'' (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp3[simp]: "is_message_updateH mid (Call ''message_chat_assign'' (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp4[simp]: "  \<not>is_message_updateH mid (Call upd (mid'#args) res)" if "upd \<notin> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''}"
  using that  by (auto simp add: is_message_updateH_def )

definition is_message_update :: "(val, 'b) operationContext_scheme \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where
  (*:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where *)
  "is_message_update ctxt c mId \<equiv> case calls ctxt c of Some call \<Rightarrow> is_message_updateH mId call | None \<Rightarrow> False "

definition crdtSpec_message_exists_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
  "crdtSpec_message_exists_h args ctxt \<equiv> 
  \<exists>mId.
  args = [mId]
 \<and> (\<exists>c. is_message_update ctxt c mId)
 \<and> (\<forall>c\<in>callsWithOpArgs ctxt ''message_delete'' args. 
          (\<exists>c'. (c,c')\<in>happensBefore ctxt \<and> is_message_update ctxt c mId))"

schematic_goal crdtSpec_message_exists_h_def2:
"crdtSpec_message_exists_h [mId] ctxt = ((\<exists>c. is_message_update ctxt c mId)
 \<and> (\<forall>c\<in>callsWithOpArgs ctxt ''message_delete'' [mId]. 
          (\<exists>c'. (c,c')\<in>happensBefore ctxt \<and> is_message_update ctxt c mId)))"
  by (auto simp add: crdtSpec_message_exists_h_def)

definition crdtSpec_message_exists :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_exists args ctxt res \<equiv> 
  res = Bool (crdtSpec_message_exists_h args ctxt)"

(* ignores map-deletes as they are not used *)
definition crdtSpec_chat_contains_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
  "crdtSpec_chat_contains_h args ctxt \<equiv> 
  (callsWithOpArgs ctxt ''chat_add'' args \<noteq> {})
  \<and> (\<forall>cr\<in>callsWithOpArgs  ctxt ''chat_remove'' args. (\<exists>ca\<in>callsWithOpArgs ctxt ''chat_add'' args. (cr,ca) \<in> happensBefore ctxt))"

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

lemma mkContext_calls[simp]:
"calls (mkContext ctxt) = calls ctxt |` i_visibleCalls ctxt"
  by (auto simp add: mkContext_def)

lemma mkContext_happensBefore[simp]:
"happensBefore (mkContext ctxt) = happensBefore ctxt  |r i_visibleCalls ctxt"
  by (auto simp add: mkContext_def)


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


lemma is_message_update_vis_simps:
  "is_message_update (mkContext (invContextH co   to  ts  hb  cs  kids  iop  ires (Some vis))) c m
\<longleftrightarrow> (\<exists>call. cs c \<triangleq> call \<and>  is_message_updateH m call \<and> isCommittedH co ts c \<and> c \<in> vis)"
  by (auto simp add: is_message_update_def mkContext_def invContextH_def restrict_map_def is_message_updateH_def commitedCallsH_def split: option.splits)



lemma inv1_unchanged:
  assumes "inv1 (invContextH co to ts hb cs kIds iOp iRes (Some visa))"
  shows "inv1 (invContextH co to' ts hb cs kIds' iOp' iRes' (Some visa))"
  using assms  by (auto simp add: inv1_def mkContext_def invContextH_def)

lemma inv2_unchanged:
  assumes "inv2 (invContextH co to ts hb cs kIds iOp iRes (Some visa))"
  shows "inv2 (invContextH co to' ts hb cs kIds' iOp' iRes' (Some visa))"
  using assms  by (auto simp add: inv2_def mkContext_def invContextH_def)


lemma inv2_h1_unchanged:
  assumes "inv2_h1 (invContextH co to ts hb cs kIds iOp iRes (Some visa))"
  shows "inv2_h1 (invContextH co to' ts hb cs kIds' iOp' iRes' (Some visa))"
  using assms  by (auto simp add: is_message_update_def inv2_h1_def mkContext_def invContextH_def)


lemma consistentSnapshot_subset:
  assumes cs: "consistentSnapshotH S'_calls S'_happensBefore S'_callOrigin S'_transactionStatus vis"
    and calls1: "\<And>c. c\<notin>txCalls \<Longrightarrow> S'_calls c = S_calls c"
    and hb1: "\<And>c1 c2. c2\<notin>txCalls \<Longrightarrow>  (c1,c2)\<in>S'_happensBefore \<longleftrightarrow> (c1,c2)\<in>S_happensBefore"
    and hb2: "\<And>c1 c2. \<lbrakk>c1\<in>txCalls; c2\<notin>txCalls\<rbrakk> \<Longrightarrow>  (c1,c2)\<notin>S_happensBefore"
    and co1: "\<And>c. c\<notin>txCalls \<Longrightarrow> S'_callOrigin c = S_callOrigin c"
    and co3: "\<And>c. c\<in>txCalls \<Longrightarrow> S_callOrigin c = None"
    and co4: "\<And>c. S_callOrigin c \<noteq> Some tx"
    and ts1: "\<And>t. t\<noteq>tx \<Longrightarrow> S'_transactionStatus t = S_transactionStatus t" 
    and wf: "\<And>c. S_calls c \<noteq> None \<Longrightarrow> S_callOrigin c \<noteq> None"
  shows "consistentSnapshotH S_calls S_happensBefore S_callOrigin S_transactionStatus (vis - txCalls)"
proof (auto simp add: consistentSnapshotH_def)
  show vis_subset_calls: "\<And>x. \<lbrakk>x \<in> vis; x \<notin> txCalls\<rbrakk> \<Longrightarrow> \<exists>y. S_calls x \<triangleq> y"
    by (metis basic_trans_rules(31) calls1 consistentSnapshotH_def cs domD)

  from cs
  have cc: "causallyConsistent (S'_happensBefore) vis"
    by (simp add: consistentSnapshotH_def)
  show "causallyConsistent S_happensBefore (vis - txCalls)"
  proof (auto simp add: causallyConsistent_def)

    show "c2 \<in> vis"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "(c2, c1) \<in> S_happensBefore"
      for  c1 c2
      using that
      by (meson causallyConsistent_def cc hb1) 


    show "False"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "(c2, c1) \<in> S_happensBefore"
        and c3: "c2 \<in> txCalls"
      for  c1 c2
      using c1 c2 c3 hb2 by auto
  qed

  from cs
  have tc: "transactionConsistent S'_callOrigin S'_transactionStatus vis"
    by (simp add: consistentSnapshotH_def)


  show "transactionConsistent S_callOrigin S_transactionStatus (vis - txCalls)"
  proof (auto simp add: transactionConsistent_def)

    show "S_transactionStatus t \<triangleq> Commited"
      if c0: "c \<in> vis"
        and c1: "c \<notin> txCalls"
        and c2: "S_callOrigin c \<triangleq> t"
      for  c t
      using that co1 co4 tc transactionConsistent_Commited ts1 by fastforce 

    show "c2 \<in> vis"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "S_callOrigin c1 = S_callOrigin c2"
      for  c1 c2
      using that
      by (metis co1 co3 local.wf option.distinct(1) tc transactionConsistent_all_from_same vis_subset_calls) 

    show "False"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "S_callOrigin c1 = S_callOrigin c2"
        and c3: "c2 \<in> txCalls"
      for  c1 c2
      using that
      using co3 local.wf vis_subset_calls by force 
  qed
qed

lemma Ex_quantor: "\<exists>x. P x \<Longrightarrow>  Ex P"
  by simp

lemma finite_list_exists:
  assumes a: "finite {v. P v}"
  shows "\<exists>l. \<forall>v. (v \<in> set l) = (P v)"
  using assms finite_list by fastforce

lemma finite_mapping:
  assumes "finite A" 
    and "\<And>x. x\<in>B \<Longrightarrow> \<exists>y\<in>A. f y = x"
  shows "finite B"
  using assms proof (induct arbitrary: B rule: finite_induct)
  case empty
  hence "B = {}"
    by blast
  thus ?case by simp
next
  case (insert x F)

  find_theorems name: "insert."

  have "finite (B - {f x})"
  proof (rule insert.hyps)
    show "\<And>xa. xa \<in> B - {f x} \<Longrightarrow> \<exists>y\<in>F. f y = xa"
      using insert.prems by blast
  qed
  then show ?case
    by simp 
qed


lemma finite_mapping2:
  assumes "finite (dom m)"
  shows "finite {f v | v. \<exists>x. m x = Some v}"
  using assms proof (rule finite_mapping)
  show "\<And>x. x \<in> {f v |v. \<exists>x. m x \<triangleq> v} \<Longrightarrow> \<exists>y\<in>dom m. f(the (m y)) = x"
    by force
qed

lemma finite_mapping3:
  assumes "finite (dom m)"
    and inj: "inj f"
  shows "finite {v. \<exists>x. m x = Some (f v)}"
  using `finite (dom m)` proof (rule finite_mapping)
  show "\<And>x. x \<in> {v. \<exists>x. m x \<triangleq> f v} \<Longrightarrow> \<exists>y\<in>dom m. (SOME v. the (m y) = f v) = x"
    apply auto
    apply (rule_tac x=xa in bexI)
     apply auto
    apply (rule someI2_ex)
     apply force
    by (simp add: inj inj_eq)
qed



lemma every_query_has_result_message_chat_read:
  assumes "finite (dom (calls ctxt))"
  shows  "\<exists>res. crdtSpec ''message_chat_read'' args ctxt res"
  apply (auto simp add: crdtSpec_def)
  apply (rule Ex_quantor)
  apply (auto simp add: crdtSpec_message_chat_read_def )
  apply (rule finite_list_exists)

  apply (rule_tac B="{v. \<exists>c. calls ctxt c \<triangleq> Call ''message_chat_assign'' (args @ [v]) Undef}" in finite_subset)
   apply (auto simp add: callsWithOpArgs_def)
  apply (rule finite_mapping3[OF `finite (dom (calls ctxt))`])
  by (meson append1_eq_conv call.inject injI)


lemma every_query_has_result_message_author_read:
  assumes "finite (dom (calls ctxt))"
  shows  "\<exists>res. crdtSpec ''message_author_read'' args ctxt res"
  apply (auto simp add: crdtSpec_def)
  apply (rule Ex_quantor)
  apply (auto simp add: crdtSpec_message_author_read_def)
  apply (rule finite_list_exists)
  apply (rule_tac B="{v. \<exists>c. calls ctxt c \<triangleq> Call ''message_author_assign'' (args @ [v]) Undef}" in finite_subset)
   apply (auto simp add: callsWithOpArgs_def)
  apply (rule finite_mapping3[OF `finite (dom (calls ctxt))`])
  by (meson append1_eq_conv call.inject injI)

lemma every_query_has_result_chat_contains[simp]:
  shows  "\<exists>res. crdtSpec ''chat_contains'' args ctxt res"
  apply (auto simp add: crdtSpec_def)
  by (auto simp add: crdtSpec_chat_contains_def)

lemma every_query_has_result_message_exists[simp]:
  shows  "\<exists>res. crdtSpec ''message_exists'' args ctxt res"
  apply (auto simp add: crdtSpec_def)
  by (auto simp add: crdtSpec_message_exists_def)

lemma every_query_has_result_assign[simp]:
  shows "crdtSpec ''message_author_assign'' args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec ''message_content_assign'' args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec ''message_chat_assign'' args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec ''chat_add'' args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec ''chat_remove'' args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec ''message_delete'' args ctxt res \<longleftrightarrow> res = Undef"
  by (auto simp add: crdtSpec_def)

lemma every_query_has_result:
  assumes fin: "finite (dom (calls ctxt))"
  shows  "\<exists>res. crdtSpec procName args ctxt res"
  apply (case_tac "procName = ''message_chat_read''"; case_tac "procName = ''message_author_read''"; case_tac "procName = ''chat_contains''"; case_tac "procName = ''message_exists''")
                 apply (auto simp add: every_query_has_result_message_chat_read[OF fin] every_query_has_result_message_author_read[OF fin])
  apply (auto simp add: crdtSpec_def )
  done


lemma commitedCalls_simps[simp]:
  assumes noUncommitted: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
    and wf: "state_wellFormed S"
  shows "commitedCalls S = dom (calls S)"
  using assms apply (auto simp add: commitedCallsH_def isCommittedH_def domD domIff wellFormed_callOrigin_dom3)
  by (smt not_Some_eq transactionStatus.exhaust wellFormed_callOrigin_dom3 wf_no_transactionStatus_origin_for_nothing)

lemma consistentSnapshot_vis_subset[dest]:
  assumes "consistentSnapshot S vis"
  shows "vis \<subseteq> dom (calls S)"
using assms by (auto simp add: consistentSnapshotH_def)

lemma consistentSnapshot_vis_subset2[simp]:
  assumes "consistentSnapshot S vis"
and "c \<in> vis"
shows "\<exists>call. calls S c \<triangleq> call"
using assms by (auto simp add: consistentSnapshotH_def)


lemma consistentSnapshot_vis_intersect[simp]:
  assumes "consistentSnapshot S vis"
  shows "dom (calls S) \<inter> vis = vis"
  using assms   by auto




  
lemma invariant_all_def2:
"invariant_all state =
 (\<forall>vis. vis \<subseteq> dom (calls state) \<and> consistentSnapshot state vis
 \<longrightarrow> invariant (prog state) (invContextVis state vis))"
  by (auto simp add: invariant_all_def)


lemma calls_restrict_simps[simp]:
"((calls S |` vis) c \<triangleq> ci) = (c \<in> vis \<and> calls S c \<triangleq> ci)"
  by (simp add: restrict_map_def)

lemma commitedCallsH_true:
  assumes "cOrig c \<triangleq> t" and "tStatus t \<triangleq> Commited"
  shows "c \<in> commitedCallsH cOrig tStatus"
  using assms  by (auto simp add: commitedCallsH_def isCommittedH_def)

lemma commitedCallsH_simp:
  assumes "tStatus t \<triangleq> Commited"
  shows "commitedCallsH (cOrig(c \<mapsto> t)) (tStatus) = insert c (commitedCallsH cOrig tStatus)"
  using assms  by (auto simp add: commitedCallsH_def isCommittedH_def)

lemma callsWithOpArgs_simps:
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommited"
  shows "callsWithOpArgs (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  )) opName args = {c\<in>vis. state_calls c \<triangleq> Call opName args Undef}"
  apply (auto simp add: callsWithOpArgs_def)
    apply (auto simp add: commitedCallsH_def isCommittedH_def restrict_map_def  split: if_splits)
  by (metis consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Commited)

lemmas wellFormed_callOrigin_dom[simp]



lemma wellFormed_callOrigin_transactionStatus[simp]:
  assumes wf: "state_wellFormed S"
  shows  "Option.these (range (callOrigin S)) \<subseteq> dom (transactionStatus S)"

  using wf apply (induct rule: wellFormed_induct)
   apply (simp add: initialState_def)

  apply (erule step.cases)
          apply (auto split: if_splits)
  by (metis (no_types, lifting) domD domIff image_iff in_these_eq wf_no_transactionStatus_origin_for_nothing)





lemma callsOfOp_simps:
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommited"
  shows "callsOfOp (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  )) opName = {(c,args). c\<in>vis \<and> state_calls c \<triangleq> Call opName args Undef}"
  apply (auto simp add: callsOfOp_def)
    apply (auto simp add: commitedCallsH_def isCommittedH_def restrict_map_def  split: if_splits)
  by (metis consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Commited)

lemma is_message_update_simps1: 
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
  shows "is_message_update (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  )) c mId \<longleftrightarrow> c\<in>vis \<and> (\<exists>call.  state_calls c = Some call \<and> is_message_updateH mId call)"
  apply (auto simp add: is_message_update_def simp add: restrict_map_def split: option.splits)
  by (metis commitedCallsH_true consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Commited)


lemma is_message_update_simps2: 
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and wf2: "Option.these (range state_callOrigin) \<subseteq> dom state_transactionStatus"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommited"
shows "is_message_update
         (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  ) c mId \<longleftrightarrow>(\<exists>call. state_calls c = Some call \<and> is_message_updateH mId call)"
  apply (auto simp add: is_message_update_def commitedCallsH_def  isCommittedH_def  simp add: restrict_map_def split: option.splits)
  by (smt domD domI in_these_eq less_eq_transactionStatus_def local.wf noUncommitted order_refl rangeI set_rev_mp wf2)

lemmas is_message_update_simps = is_message_update_simps1 is_message_update_simps2

lemma happensBefore_restrict_wf[simp]:
  assumes wf: "state_wellFormed S"
  shows "happensBefore S |r dom (calls S) = happensBefore S"
  apply (auto simp add: restrict_relation_def)
  apply (simp add: domD happensBefore_in_calls_left local.wf)
  by (simp add: domD happensBefore_in_calls_right local.wf)

lemma restrict_case_simps: 
"(case (m |` S) x of None \<Rightarrow> False | Some x \<Rightarrow> P x) \<longleftrightarrow> x\<in>S \<and> (case m x of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (metis option.simps(4) restrict_in restrict_out)


lemma invContextH_simps_allCommitted:
  assumes no_uncommitted: "\<And>tx. state_transactionStatus tx \<noteq> Some Uncommited"
    and wf1: "dom state_callOrigin = dom state_calls"
    and wf2: "Option.these (range state_callOrigin) \<subseteq> dom state_transactionStatus"
    and wf3a: "fst ` state_happensBefore \<subseteq> dom state_calls"
    and wf3b: "snd ` state_happensBefore \<subseteq> dom state_calls"
    and wf4: "dom state_transactionOrigin = dom state_transactionStatus"
  shows
 "invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore
   state_calls state_knownIds state_invocationOp state_invocationRes vis = \<lparr>
        calls = state_calls , 
        happensBefore = state_happensBefore , 
        i_visibleCalls = (case vis of None \<Rightarrow> {} | Some vis \<Rightarrow> vis),
        i_callOrigin  = state_callOrigin,
        i_transactionOrigin = state_transactionOrigin,
        i_knownIds = state_knownIds,
        i_invocationOp = state_invocationOp,
        i_invocationRes = state_invocationRes
      \<rparr>"
proof -

  have h1: "isCommittedH state_callOrigin state_transactionStatus c" if "state_calls c \<triangleq> someCall" for c someCall
    using that    apply (auto simp add: isCommittedH_def)
    by (smt domD domI dual_order.refl in_these_eq less_eq_transactionStatus_def no_uncommitted rangeI subsetCE wf1 wf2)


  show ?thesis
    apply (auto simp add: invContextH_def restrict_map_def restrict_relation_def commitedCallsH_def  no_uncommitted intro!: ext split: if_splits)
    using h1 apply force
    using wf3a h1 apply auto[1]
    using wf3b h1 apply auto[1]
    apply (metis domD domIff h1 wf1)
    by (metis (full_types) domD domIff no_uncommitted transactionStatus.exhaust wf4)
qed


lemmas wellFormed_visibleCallsSubsetCalls_prod[simp] = wellFormed_visibleCallsSubsetCalls_h(1)
lemmas wf_transaction_status_iff_origin_dom_simp[simp] = wf_transaction_status_iff_origin_dom

lemma wellFormed_happensBefore_calls_l'[simp]: "state_wellFormed S \<Longrightarrow> fst ` happensBefore S \<subseteq> dom (calls S)"
  using wellFormed_happensBefore_calls_l by fastforce

lemma wellFormed_happensBefore_calls_r'[simp]: "state_wellFormed S \<Longrightarrow> snd ` happensBefore S \<subseteq> dom (calls S)"
  using wellFormed_happensBefore_calls_r by fastforce

lemma invContextH_simps_allCommitted2:
  assumes no_uncommitted[simp]: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommited"
    and wf[simp]: "state_wellFormed S"
  shows
 "invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S)
   (calls S) (knownIds S) (invocationOp S) (invocationRes S) vis = \<lparr>
        calls = calls S, 
        happensBefore = happensBefore S, 
        i_visibleCalls = (case vis of None \<Rightarrow> {} | Some vis \<Rightarrow> vis),
        i_callOrigin  = callOrigin S,
        i_transactionOrigin = transactionOrigin S,
        i_knownIds = knownIds S,
        i_invocationOp = invocationOp S,
        i_invocationRes = invocationRes S
      \<rparr>"
  by (simp add: invContextH_simps_allCommitted)


lemma these_range_update[simp]: "f x = None \<Longrightarrow> Option.these ( range (f(x \<mapsto> y))) = insert y (Option.these (range f))"
  apply (auto simp add: fun_upd_def image_iff in_these_eq)
  by force

lemma updateHb_fst[simp]: "fst ` updateHb hb vis cs = (if cs = [] then fst`hb else fst ` hb \<union> vis \<union> set (butlast cs))"
  by (induct cs arbitrary: hb vis, auto simp add: updateHb_cons image_Un)

lemma updateHb_snd[simp]: "snd ` updateHb hb vis cs = (snd ` hb \<union> (if vis={} then set (tl cs) else set cs))"
  by (induct cs arbitrary: hb vis, auto simp add: updateHb_cons image_Un)



theorem "programCorrect progr"
proof (rule show_correctness_via_single_session)
  have [simp]: "invariant progr = inv" by simp

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)

  show "invariant_all (initialState progr)"
    by (auto simp add: is_message_update_def initialState_def invariant_all_def inv_def inv1_def inv2_def inv2_h1_def invContextH_def crdtSpec_message_exists_h_def crdtSpec_chat_contains_h_def mkContext_def is_message_updateH_def callsWithOpArgs_def)



  show "programCorrect_s progr"
  proof (rule show_program_correct_single_invocation)

    text {* First show that the invariant holds for the initial states (beginning of procedures) *}
    show "\<And>S i. S \<in> initialStates progr i \<Longrightarrow> invariant_all S"
      apply  (subst(asm) initialStates_def)
      apply (auto simp add: invariant_all_def  inv_def)
        apply (auto simp add: invContextH_simps_allCommitted)
        apply (auto simp add: inv1_def mkContext_def crdtSpec_chat_contains_h_def crdtSpec_message_exists_h_def callsWithOpArgs_def)[1]
       apply (auto simp add: inv2_def inv2_h1_def mkContext_def   callsWithOpArgs_def)[1]
      apply (auto simp add: inv2_def inv2_h1_def mkContext_def crdtSpec_message_author_read_def crdtSpec_message_exists_h_def callsWithOpArgs_def callsOfOp_def is_message_update_def)[1]
      done
      


(*

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
        by (auto simp add: mkContext_calls_simps )

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
*)



    text {* Next, check each procedure: *}
    show "checkCorrect progr S i" if "S \<in> initialStates progr i" for S i
    proof -
      from initialStates_impl[OF `S \<in> initialStates progr i`]
      have "checkCorrect progr S i" 
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
        show "checkCorrect progr S i"
        proof (auto simp add: checkCorrect_simps editMessageImpl_def updateHb_chain; (subst invariant_all_def)?; auto? )

          show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca]) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] Undef)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2[simp]: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c15: "\<forall>c. callOrigin S' c \<noteq> Some t"
              and c8[simp]: "calls S' c = None"
              and c9: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)"
              and c10: "visibleCalls S' i \<triangleq> vis"
              and c11[simp]: "ca \<noteq> c"
              and c12[simp]: "calls S' ca = None"
              and no_uncommitted[simp]: "\<forall>ta. ta \<noteq> t \<longrightarrow> transactionStatus S' ta \<noteq> Some Uncommited"
              and c14[simp]: "consistentSnapshotH (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] Undef)) (updateHb (happensBefore S') vis [c, ca]) (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) visa"
            for  t S' c vis ca visa
          proof (subst invContextH_simps_allCommitted; simp?)
            show "Option.these (range (callOrigin S')) \<subseteq> insert t (dom (transactionStatus S'))"
              by (simp add: subset_insertI2)

            have vis_subset[simp]: "vis \<subseteq> insert ca (insert c (dom (calls S')))"
              by (meson c10 c2 subset_insertI2 wellFormed_visibleCallsSubsetCalls_h(2))

            show "fst ` happensBefore S' \<subseteq> insert ca (insert c (dom (calls S'))) \<and> vis \<subseteq> insert ca (insert c (dom (calls S')))"
              by (simp add: subset_insertI2)

            show "snd ` happensBefore S' \<subseteq> insert ca (insert c (dom (calls S')))"
              by (simp add: subset_insertI2)

            have [simp]: "t\<in>dom (transactionStatus S')"
              by (metis c2 c7 domI wf_transaction_status_iff_origin_dom_simp)

            show "dom (transactionStatus S') = insert t (dom (transactionStatus S'))"
              by (metis c2 c7 insert_dom wf_transaction_status_iff_origin_dom_simp)

            show "example_chat.inv
               \<lparr>calls = calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] Undef),
                  happensBefore = updateHb (happensBefore S') vis [c, ca], i_visibleCalls = visa, i_callOrigin = callOrigin S'(c \<mapsto> t, ca \<mapsto> t), i_transactionOrigin = transactionOrigin S',
                  i_knownIds = knownIds S', i_invocationOp = invocationOp S', i_invocationRes = invocationRes S'\<rparr>" (is "inv ?state")
            proof (auto simp add: inv_def)
              show "inv1 ?state"
                apply (simp only: inv1_def mkContext_def operationContext.simps invariantContext.simps)
                apply clarify
                apply clarsimp (* WHY DOES THIS LOOP? *)
                find_theorems i_visibleCalls
                apply clarify
                sorry

              show "inv2 ?state"
                sorry

              show "inv2_h1 ?state"
                sorry



          proof (auto simp add: inv_def)
            have [simp]: "prog S' = progr"
              by (simp add: c3)


            hence no_calls_in_t: "callOrigin S' c \<noteq> Some t" for c
              using c15 by blast

            have "consistentSnapshot S' (visa - {c,ca})"
              apply (rule consistentSnapshot_subset[OF c14], auto)
              using c2 c8 wellFormed_happensBefore_calls_l apply blast
              using c12 c2 wellFormed_happensBefore_calls_l apply blast
              using c2 c8 wellFormed_callOrigin_dom2 apply blast
                apply (simp add: c12 c2)
              using no_calls_in_t apply blast
              by (simp add: c2 domD domI )



            find_theorems name: consistentSnapshot

            with `invariant_all S'` 
            have oldInv: "inv (invContextVis S' (visa - {c,ca}))"
              by (auto simp add: invariant_all_def)
            hence old_inv1: "inv1 (invContextVis S' (visa - {c, ca}))"
              and  old_inv2: "inv2 (invContextVis S' (visa - {c, ca}))"
              and old_inv2_h1: "inv2_h1 (invContextVis S' (visa - {c, ca}))"
              by (auto simp add: inv_def)

            thm c14 

            have domEq[simp]: "dom (callOrigin S') = dom (calls S')"
              by (simp add: c2)

            have "insert ca (insert c (dom (callOrigin S'))) = insert ca (insert c (dom (calls S')))"
              by simp

            thm invContextH_update_calls


            have [simp]: "c \<noteq> ca"
              using c11 by blast 

            

            show "inv1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca])
               (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] Undef)) (knownIds S')
               (invocationOp S') (invocationRes S') (Some visa))"
              apply (auto simp add: inv1_def)
              apply (subst crdtSpec_message_exists_h_def2)
              apply (auto simp add: is_message_update_simps cong: conj_cong)
                     apply (auto simp add: crdtSpec_chat_contains_h_def callsWithOpArgs_simps split: if_splits cong: conj_cong)


              apply (subst(asm) callsWithOpArgs_simps)
              apply simp
                apply simp
              apply simp
              using c2 domD apply fastforc
                apply auto[1]


            proof (auto simp add: inv1_def)
              fix cb m
              assume a0: "crdtSpec_chat_contains_h [cb, m]
                       (mkContext
                         (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                           (updateHb (happensBefore S') vis [c, ca])
                           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] Undef))
                           (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"



(*
 \<lbrakk>\<forall>cr. isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<longrightarrow>
                   cr \<in> visa \<longrightarrow>
                   calls S' cr \<triangleq> Call ''chat_remove'' [cb, m] Undef \<longrightarrow>
                   cr = c \<or> cr = ca \<or> (\<exists>caa. caa \<noteq> c \<and>
                                              (caa = c \<or>
                                               caa \<noteq> ca \<and>
                                               (caa = ca \<or>
                                                isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                                                caa \<in> visa \<and>
                                                (cr = c \<and> caa = ca \<or> (cr, caa) \<in> happensBefore S' \<or> cr \<in> vis \<and> caa = c \<or> cr \<in> vis \<and> caa = ca) \<and>
                                                calls S' caa \<triangleq> Call ''chat_add'' [cb, m] Undef)));
              ; ; ; 
              \<rbrakk>
*)

              have commitedCallsH_t_simp: "commitedCallsH (callOrigin S') (transactionStatus S'(t \<mapsto> Commited)) 
                  = commitedCalls S'"
                apply (auto simp add: commitedCallsH_def isCommittedH_def)
                using no_calls_in_t by blast


              have isCommittedH_simp1: "isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cx" if "calls S' cx \<triangleq> someCall" for cx someCall
                apply (auto simp add: isCommittedH_def)
                by (metis (full_types) c2 domIff no_uncommitted not_Some_eq that transactionStatus.exhaust wellFormed_callOrigin_dom wellFormed_state_callOrigin_transactionStatus)


              find_theorems "calls S' ca"

              find_theorems invContextH 
              find_theorems name: cong "op\<longrightarrow>"

              have notC: "cr \<noteq> c" if "calls S' cr \<triangleq> someCall" for cr someCall
                using that `calls S' c = None` by auto 
              have notCa: "cr \<noteq> ca" if "calls S' cr \<triangleq> someCall" for cr someCall
                using that `calls S' ca = None` by auto 

              from a0 have ???
                apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps commitedCallsH_true split: if_splits)
                apply (simp_all add: commitedCallsH_simp commitedCallsH_t_simp notC notCa cong: conj_cong imp_cong)
                     apply (auto simp add: `calls S' ca = None` `calls S' c = None` )[1]
                sorry

              from a0 obtain c_add 
                where [simp]: "c_add \<noteq> c"
                  and [simp]: "c_add \<noteq> ca"
                  and cc3: "calls S' c_add \<triangleq> Call ''chat_add'' [cb, m] Undef"
                  and cc2: "c_add \<in> visa"
                  and cc1: "isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) c_add"
                  and cc4: "\<forall>cr. isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<longrightarrow>
                   cr \<in> visa \<longrightarrow>
                   calls S' cr \<triangleq> Call ''chat_remove'' [cb, m] Undef \<longrightarrow>
                   cr = c \<or> cr = ca \<or> (\<exists>caa. caa \<noteq> c \<and>
                                              (caa = c \<or>
                                               caa \<noteq> ca \<and>
                                               (caa = ca \<or>
                                                isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                                                caa \<in> visa \<and>
                                                (cr = c \<and> caa = ca \<or> (cr, caa) \<in> happensBefore S' \<or> cr \<in> vis \<and> caa = c \<or> cr \<in> vis \<and> caa = ca) \<and>
                                                calls S' caa \<triangleq> Call ''chat_add'' [cb, m] Undef)))"
apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps commitedCallsH_true isCommittedH_simp1 split: if_splits)
                     apply (simp_all add: commitedCallsH_simp commitedCallsH_t_simp  notC notCa isCommittedH_simp1  cong: conj_cong imp_cong)
                     apply atomize_elim
                     apply (rule_tac x=" caa" in exI)
                     apply safe[1]
                apply (smt commitedCallsH_def fun_upd_apply isCommittedH_def mem_Collect_eq)
                     apply (drule_tac x=cr in spec)
                     apply safe[1]
                apply (smt c12 c8 commitedCallsH_t_simp commitedCallsH_true domI domIff fun_upd_other isCommittedH_def)



                sorry

              hence "crdtSpec_chat_contains_h [cb, m] (mkContext (invContextVis S' (visa - {c, ca})))"
                apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps)
                apply (rule_tac x=c_add in exI)
                apply (auto simp add: cc2 cc3)
                using cc1 apply (auto simp add: isCommittedH_def no_calls_in_t split: if_splits)
                apply (drule_tac x=cr in spec)
                apply auto
                using no_calls_in_t by blast

              with old_inv1
              have "crdtSpec_message_exists_h [m] (mkContext (invContextVis S' (visa - {c, ca})))"
                by (auto simp add: inv1_def)

              thus "crdtSpec_message_exists_h [m]
             (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                          (updateHb (happensBefore S') vis [c, ca])
                          (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
                          (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"
                apply (auto simp add: crdtSpec_message_exists_h_def mkContext_simps is_message_update_vis_simps)
                 apply (auto simp add: is_message_updateH_def isCommittedH_def split: option.splits)
                 apply fastforce
                by (metis no_calls_in_t)
            qed

            show "inv2 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca])
           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S')
           (invocationOp S') (invocationRes S') (Some visa))"
            proof (auto simp add: inv2_def)
              fix m
              assume a_message_exists: "crdtSpec_message_exists_h [m]
          (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                       (updateHb (happensBefore S') vis [c, ca])
                       (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
                       (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"


              {
                assume [simp]: "m = MessageId mId" and "vis \<subseteq> visa"
                from `crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)`
                have "crdtSpec_message_exists_h [m] (mkContext (invContextVis S' (visa - {c, ca})))"
                  apply (auto simp add: crdtSpec_def crdtSpec_message_exists_def crdtSpec_message_exists_h_def mkContext_simps is_message_update_vis_simps)

                   apply (auto simp add: is_message_updateH_simp isCommittedH_def  split: option.splits if_splits)
                   apply (rule_tac x=cb in exI)
                   apply (rule_tac x=x2 in exI)
                   apply (auto simp add: getContextH_def restrict_map_def split: option.splits if_splits)[1]
                      apply (metis c10 c15 c2 c6 domIff not_None_eq wellFormed_callOrigin_dom wellFormed_state_transaction_consistent(1))(* TODO general*)
                  using \<open>vis \<subseteq> visa\<close> apply auto[1]
                    apply (simp add: `calls S' c = None`)
                   apply (simp add: `calls S' ca = None`) 
                  apply (auto simp add: getContextH_def restrict_map_def split: option.splits if_splits)[1]
                  sorry
              }


              show "\<exists>a. crdtSpec_message_author_read [m]
              (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                           (updateHb (happensBefore S') vis [c, ca])
                           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
                           (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))
              (ListVal [a])"
                sorry
            qed


            show "inv2_h1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca])
              (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S')
              (invocationOp S') (invocationRes S') (Some visa))"
              sorry

          qed

          text {* editMessage, case message does exist, return from procedure  *}
          show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca]) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
              and c9: "calls S' c = None"
              and c10: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) (Bool True)"
              and c11: "visibleCalls S' i \<triangleq> vis"
              and c12: "ca \<noteq> c"
              and c13: "calls S' ca = None"
              and c15: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), happensBefore := updateHb (happensBefore S') vis [c, ca], currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited), localState := (localState S')(i := None), currentProc := (currentProc S')(i := None), visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> Undef), knownIds := knownIds S' \<union> uniqueIds Undef\<rparr>) visa"
            for  t S' c vis ca resa visa
          proof -
            from c15
            have c15': "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)), happensBefore := updateHb (happensBefore S') vis [c, ca], localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
              by (auto simp add: consistentSnapshot_def)

            from h[OF c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 c13 c15' c8]
            show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (updateHb (happensBefore S') vis [c, ca]) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
              by (meson example_chat.inv_def inv1_unchanged inv2_h1_unchanged inv2_unchanged)
          qed

          text {* editMessage, case message does not exist  *}
          show h: "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c}) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
              and c9: "res \<noteq> Bool True"
              and c10: "calls S' c = None"
              and c11: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) res"
              and c12: "visibleCalls S' i \<triangleq> vis"
              and c13: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res), callOrigin := callOrigin S'(c \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert c vis), happensBefore := happensBefore S' \<union> vis \<times> {c}, localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
            for  t S' c res vis visa
          proof -
            have [simp]: "prog S' = progr"
              by (simp add: c3)


            hence no_calls_in_t: "callOrigin S' c \<noteq> Some t" for c
              by (simp add: c8)

            have "consistentSnapshot S' (visa - {c})"
              apply (rule consistentSnapshot_subset[OF c13], auto)
              using c10 c2 wellFormed_happensBefore_calls_l apply blast
              using c10 c2 wellFormed_callOrigin_dom2 apply blast
              using no_calls_in_t apply blast
              by (simp add: c2 domD domI wellFormed_callOrigin_dom)


            with `invariant_all S'` 
            have oldInv: "inv (invContextVis S' (visa - {c}))"
              by (auto simp add: invariant_all_def)
            hence old_inv1: "inv1 (invContextVis S' (visa - {c}))"
              and  old_inv2: "inv2 (invContextVis S' (visa - {c}))"
              and old_inv2_h1: "inv2_h1 (invContextVis S' (visa - {c}))"
              by (auto simp add: inv_def)

            show ?thesis
            proof (auto simp add: inv_def)
              show " inv1 (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c})
                 (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
              proof (auto simp add: inv1_def)
                fix ca m
                assume "crdtSpec_chat_contains_h [ca, m]
             (mkContext (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c})
                          (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"

(*
\<And>c_add. \<lbrakk>\<forall>cr. calls S' cr \<triangleq> Call ''chat_remove'' [ca, m] Undef \<longrightarrow>
                   cr \<in> visa \<longrightarrow>
                   isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<longrightarrow>
                   cr = c \<or>
                   (\<exists>caa. caa \<noteq> c \<and>
                          (caa = c \<or>
                           isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                           caa \<in> visa \<and> ((cr, caa) \<in> happensBefore S' \<or> cr \<in> vis \<and> caa = c) \<and> calls S' caa \<triangleq> Call ''chat_add'' [ca, m] Undef));
              ; ; ; \<rbrakk>
*)

                from this obtain c_add 
                  where cc4: "c_add \<noteq> c"
                    and cc3: "calls S' c_add \<triangleq> Call ''chat_add'' [ca, m] Undef"
                    and cc2: "c_add \<in> visa"
                    and cc1: "isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) c_add"
                    and cc5: "\<forall>cr. calls S' cr \<triangleq> Call ''chat_remove'' [ca, m] Undef \<longrightarrow>
                         cr \<in> visa \<longrightarrow>
                         isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<longrightarrow>
                         cr = c \<or>
                         (\<exists>caa. caa \<noteq> c \<and>
                                (caa = c \<or>
                                 isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                                 caa \<in> visa \<and> ((cr, caa) \<in> happensBefore S' \<or> cr \<in> vis \<and> caa = c) \<and> calls S' caa \<triangleq> Call ''chat_add'' [ca, m] Undef))"
                  by (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps split: if_splits)


                hence "crdtSpec_chat_contains_h [ca, m] (mkContext (invContextVis S' (visa - {c})))"
                  apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps)
                  apply (rule_tac x=c_add in exI)
                  apply (auto simp add: cc2 cc3)
                  using cc1 apply (auto simp add: isCommittedH_def no_calls_in_t split: if_splits)
                  apply (drule_tac x=cr in spec)
                  apply auto
                  using c8 by blast

                with old_inv1
                have "crdtSpec_message_exists_h [m] (mkContext (invContextVis S' (visa - {c})))"
                  by (auto simp add: inv1_def)

                thus "crdtSpec_message_exists_h [m]
                   (mkContext (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c})
                                (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"
                  apply (auto simp add: crdtSpec_message_exists_h_def mkContext_simps is_message_update_vis_simps)
                   apply (auto simp add: is_message_updateH_def isCommittedH_def split: option.splits)
                   apply fastforce
                  by (metis no_calls_in_t)
              qed

              show "inv2 (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c})
           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
                sorry

              show "inv2_h1 (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c})
              (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
                sorry

            qed

          qed

          text {* editMessage, case message does not exist, return from procedure  *}
          show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c}) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
            if c0: "transactionStatus S t = None"
              and c1: "invariant_all S'"
              and c2: "state_wellFormed S'"
              and c3: "state_monotonicGrowth S S'"
              and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId mId, ls_pc := Suc 0\<rparr>"
              and c5: "currentProc S' i \<triangleq> editMessageImpl"
              and c6: "currentTransaction S' i \<triangleq> t"
              and c7: "transactionOrigin S' t \<triangleq> i"
              and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
              and c9: "res \<noteq> Bool True"
              and c10: "calls S' c = None"
              and c11: "crdtSpec ''message_exists'' [MessageId mId] (getContextH (calls S') (happensBefore S') (Some vis)) res"
              and c12: "visibleCalls S' i \<triangleq> vis"
              and c13: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res), callOrigin := callOrigin S'(c \<mapsto> t), happensBefore := happensBefore S' \<union> vis \<times> {c}, currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited), localState := (localState S')(i := None), currentProc := (currentProc S')(i := None), visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> Undef), knownIds := knownIds S' \<union> uniqueIds Undef\<rparr>) visa"
            for  t S' c res vis visa
          proof -
            from c13
            have c13': "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res), callOrigin := callOrigin S'(c \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert c vis), happensBefore := happensBefore S' \<union> vis \<times> {c}, localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
              by (auto simp add: consistentSnapshot_def)

            from h[OF c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13']
            show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (happensBefore S' \<union> vis \<times> {c}) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] res)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
              by (meson example_chat.inv_def inv1_unchanged inv2_h1_unchanged inv2_unchanged)
          qed
        qed
      next

        show "checkCorrectAll progr S i"
          if c0: "invocationOp S i \<triangleq> (''deleteMessage'', [MessageId x4])"
            and c1[simp]: "currentProc S i \<triangleq> deleteMessageImpl"
            and c2[simp]: "localState S i \<triangleq> lsInit\<lparr>ls_id := MessageId x4\<rparr>"
            and c3: "uniqueIdsInList [MessageId x4] \<subseteq> knownIds S"
          for  x4
        proof -
          have progS[simp]: "prog S = progr"
            using \<open>S \<in> initialStates progr i\<close> \<open>\<And>i S. S \<in> initialStates progr i \<Longrightarrow> prog S = progr\<close> by blast
            
          have sameProg[simp]: "prog S' = progr" if "state_monotonicGrowth S S'" for S'
            using state_monotonicGrowth_prog that by force
          have [simp]: "currentTransaction S i = None" 
            using `S \<in> initialStates progr i`  initialStates_currentTransaction by blast 


          from every_query_has_result

          show "checkCorrectAll progr S i"
          proof (auto simp add: checkCorrectAll_simps deleteMessageImpl_def; (subst invariant_all_def)?; auto? )

            show "Ex (crdtSpec ''message_chat_read'' [MessageId x4] (getContext S' i))"
              if c0: "transactionStatus S t = None"
                and c1: "invariant_all S'"
                and c2: "state_wellFormed S'"
                and c3: "state_monotonicGrowth S S'"
                and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId x4, ls_pc := Suc 0\<rparr>"
                and c5: "currentProc S' i \<triangleq> deleteMessageImpl"
                and c6: "currentTransaction S' i \<triangleq> t"
                and c7: "transactionOrigin S' t \<triangleq> i"
                and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
                and c9: "\<And>ctxt procName args. finite (dom (calls ctxt)) \<Longrightarrow> Ex (crdtSpec procName args ctxt)"
              for  t S'
              apply (rule every_query_has_result)
              apply (auto simp add: getContextH_def split: option.split)
              by (simp add: c2 wf_finite_calls)


            show h: "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb})))) (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
              if c0: "transactionStatus S t = None"
                and c1: "invariant_all S'"
                and c2: "state_wellFormed S'"
                and c3: "state_monotonicGrowth S S'"
                and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId x4, ls_pc := Suc 0\<rparr>"
                and c5: "currentProc S' i \<triangleq> deleteMessageImpl"
                and c6: "currentTransaction S' i \<triangleq> t"
                and c7: "transactionOrigin S' t \<triangleq> i"
                and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
                and c9: "calls S' c = None"
                and c10: "crdtSpec ''message_chat_read'' [MessageId x4] (getContextH (calls S') (happensBefore S') (Some vis)) res"
                and c11: "visibleCalls S' i \<triangleq> vis"
                and c12: "ca \<noteq> c"
                and c13: "calls S' ca = None"
                and c14: "cb \<noteq> c"
                and c15: "cb \<noteq> ca"
                and c16: "calls S' cb = None"
                and c17: "\<And>ctxt procName args. finite (dom (calls ctxt)) \<Longrightarrow> Ex (crdtSpec procName args ctxt)"
                and c18: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert cb (insert ca (insert c vis))), happensBefore := insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId x4, ls_c := res, ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
              for  t S' c res vis ca cb visa
            proof (auto simp add: inv_def)
              have [simp]: "prog S' = progr"
                by (simp add: c3)


              hence no_calls_in_t: "callOrigin S' c \<noteq> Some t" for c
                using c8 by blast
              
              have "consistentSnapshot S' (visa - {c,ca,cb})"
                apply (rule consistentSnapshot_subset[OF c18], auto)
                using c2 c9 wellFormed_happensBefore_calls_l apply blast
                using c13 c2 wellFormed_happensBefore_calls_l apply blast
                using c16 c2 wellFormed_happensBefore_calls_l apply blast
                    apply (simp add: c2 c9)
                   apply (simp add: c13 c2)
                using c16 c2 wellFormed_callOrigin_dom2 apply blast
                using c8 apply auto[1]
                by (simp add: c2 domD domI wellFormed_callOrigin_dom)
              with `invariant_all S'` 
              have oldInv: "inv (invContextVis S' (visa - {c,ca,cb}))"
                by (auto simp add: invariant_all_def)
              hence old_inv1: "inv1 (invContextVis S' (visa - {c, ca, cb}))"
                and old_inv2: "inv2 (invContextVis S' (visa - {c, ca, cb}))"
                and old_inv2_h1: "inv2_h1 (invContextVis S' (visa - {c, ca, cb}))"
                by (auto simp add: inv_def)


              show "inv1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                       (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                       (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef))
                       (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
              proof (auto simp add: inv1_def)
                fix cc m
                assume a0: "crdtSpec_chat_contains_h [cc, m] (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))                           
                                            (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb})))) (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto>                            Call ''message_delete'' [MessageId x4] Undef))                           (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"

                define new_hb where "new_hb \<equiv> (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))"
                define new_calls where "new_calls = (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto>                            Call ''message_delete'' [MessageId x4] Undef))"

                from a0 
                have a0': "crdtSpec_chat_contains_h [cc, m] (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))                           
                                            new_hb new_calls             (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"
                  by (auto simp add: new_hb_def new_calls_def)

                from a0' obtain c_add
                  where cd1: "isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) c_add"
                    and cd2: "c_add \<in> visa"
                    and cd3: "new_calls c_add \<triangleq> Call ''chat_add'' [cc, m] Undef"
                    and cd4: "\<And>cr. isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<and>
                       cr \<in> visa \<and> new_calls cr \<triangleq> Call ''chat_remove'' [cc, m] Undef \<longrightarrow>
                       (\<exists>caa. (cr, caa) \<in> new_hb \<and>
                              isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                              caa \<in> visa \<and>
                              isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) caa \<and>
                              caa \<in> visa \<and> new_calls caa \<triangleq> Call ''chat_add'' [cc, m] Undef)"
                  by (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps split: if_splits)

                have  [simp]: "c_add \<noteq> ca" 
                  and [simp]: "c_add \<noteq> c"
                  and [simp]: "c_add \<noteq> cb"
                  using cd3 by (auto simp add: new_calls_def split: if_splits)

                have "c_add \<in> commitedCalls S'"
                  using cd1 by (auto simp add: isCommittedH_def commitedCallsH_def no_calls_in_t split: if_splits)


              (*we removed a chat message, so if something exists afterwards it should exist before: *)
                have "crdtSpec_chat_contains_h [cc, m] (mkContext (invContextVis S' (visa - {c, ca, cb})))"
                  apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_def) 
                   apply (rule_tac x=c_add in exI)
                  using cd3 apply (auto simp add: new_calls_def  invContextH_def restrict_map_def restrict_relation_def cd2 `c_add \<in> commitedCalls S'`)[1]
                proof -
                  show " \<exists>caa. (cr, caa) \<in> happensBefore (invContextVis S' (visa - {c, ca, cb})) |r (visa - {c, ca, cb}) \<and>
                    (calls (invContextVis S' (visa - {c, ca, cb})) |` (visa - {c, ca, cb})) caa \<triangleq> Call ''chat_add'' [cc, m] Undef "
                    if "(calls (invContextVis S' (visa - {c, ca, cb})) |` (visa - {c, ca, cb})) cr \<triangleq> Call ''chat_remove'' [cc, m] Undef" 
                    for cr
                  proof (cases "isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cr \<and>
                       cr \<in> visa \<and> new_calls cr \<triangleq> Call ''chat_remove'' [cc, m] Undef")
                    case True
                    then show ?thesis 
                      using cd4[where cr=cr] apply auto
                      apply (rule_tac x=caa in exI)
                      apply (auto simp add: restrict_map_def restrict_relation_def commitedCallsH_def invContextH_def split: if_splits)[1]


                  next
                    case False
                    then show ?thesis sorry
                  qed

                    
                    apply auto
                       apply (auto simp add: restrict_map_def restrict_relation_def commitedCallsH_def invContextH_def split: if_splits)[1]


                qed

                with old_inv1 
                have "crdtSpec_message_exists_h [m] (mkContext (invContextVis S' (visa - {c, ca, cb})))"
                  by (auto simp add: inv1_def)

                from this obtain cc 
                  where [simp]: "cc \<noteq> c" 
                    and [simp]: "cc \<noteq> ca"
                    and [simp]: "cc \<noteq> cb"
                    and allDeletesOverridden: "\<And>cc. cc \<in> visa \<longrightarrow>
                calls S' cc \<triangleq> Call ''message_delete'' [m] Undef \<longrightarrow>
                isCommitted S' cc \<longrightarrow>
                cc = c \<or> cc = ca \<or> cc = cb \<or> (\<exists>c'. (cc, c') \<in> happensBefore S' |r Collect (isCommitted S') |r (visa - {c, ca, cb})) \<and>
                                              is_message_updateH m (Call ''message_delete'' [m] Undef)"
                    and [simp]: "cc \<in> visa"
                    and "isCommitted S' cc"
                    and "is_message_update S' cc m"
                  by (auto simp add: crdtSpec_message_exists_h_def is_message_update_vis_simps mkContext_def invContextH_def  restrict_map_def commitedCallsH_def split: if_splits)

                have "(c, cb) \<notin> happensBefore S'" for c
                  using c16 c2 wellFormed_happensBefore_calls_r by blast






                show "crdtSpec_message_exists_h [m]              (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))                           (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))                           (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto>                            Call ''message_delete'' [MessageId x4] Undef))                           (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"
                proof (simp add: crdtSpec_message_exists_h_def, intro conjI exI allI; clarsimp?)
                  show "is_message_update
                     (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                                  (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                                  (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef))
                                  (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))
                     cc m"
                    using `is_message_update S' cc m`  apply (auto simp add: is_message_update_vis_simps is_message_updateH_simp split: option.splits)
                    by (smt \<open>isCommitted S' cc\<close> fun_upd_other fun_upd_same isCommittedH_def)

                  show " (\<exists>c'. (cc, c') \<in> happensBefore
                                               (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                                                            (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                                                            (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto>
                                                             Call ''message_delete'' [MessageId x4] Undef))
                                                            (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))) \<and>
                            is_message_updateH m (Call ''message_delete'' [m] Undef)" 
                    if "calls (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                             (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                             (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto>
                              Call ''message_delete'' [MessageId x4] Undef))
                             (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))
                             cc \<triangleq>  Call ''message_delete'' [m] Undef"
                    for cc
                  proof -
                    from that have ???
                      apply (auto simp add: mkContext_def invContextH_def commitedCallsH_def split: if_splits)

                    using allDeletesOverridden[where cc=cc]
                    apply (auto simp add: mkContext_def invContextH_def commitedCallsH_def )
                              apply (auto split: if_splits)[1]

                    find_theorems invContextH

                sorry
              show "inv2 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                       (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                       (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef))
                       (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
                sorry
              show "inv2_h1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                    (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))))
                    (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef))
                    (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
                sorry
            qed


            show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb})))) (calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
              if c0: "transactionStatus S t = None"
                and c1: "invariant_all S'"
                and c2: "state_wellFormed S'"
                and c3: "state_monotonicGrowth S S'"
                and c4: "localState S' i \<triangleq> lsInit\<lparr>ls_id := MessageId x4, ls_pc := Suc 0\<rparr>"
                and c5: "currentProc S' i \<triangleq> deleteMessageImpl"
                and c6: "currentTransaction S' i \<triangleq> t"
                and c7: "transactionOrigin S' t \<triangleq> i"
                and c8: "\<forall>c. callOrigin S' c \<noteq> Some t"
                and c9: "calls S' c = None"
                and c10: "crdtSpec ''message_chat_read'' [MessageId x4] (getContextH (calls S') (happensBefore S') (Some vis)) res"
                and c11: "visibleCalls S' i \<triangleq> vis"
                and c12: "ca \<noteq> c"
                and c13: "calls S' ca = None"
                and c14: "cb \<noteq> c"
                and c15: "cb \<noteq> ca"
                and c16: "calls S' cb = None"
                and c17: "\<And>ctxt procName args. finite (dom (calls ctxt)) \<Longrightarrow> Ex (crdtSpec procName args ctxt)"
                and c18: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t), happensBefore := insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited), localState := (localState S')(i := None), currentProc := (currentProc S')(i := None), visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> Undef), knownIds := knownIds S' \<union> uniqueIds Undef\<rparr>) visa"
              for  t S' c res vis ca cb visa
            proof -
              from c18
              have c18': "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_chat_read'' [MessageId x4] res, ca \<mapsto> Call ''chat_remove'' [res, MessageId x4] Undef, cb \<mapsto> Call ''message_delete'' [MessageId x4] Undef), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert cb (insert ca (insert c vis))), happensBefore := insert (c, ca) (insert (ca, cb) (insert (c, cb) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca} \<union> vis \<times> {cb}))), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId x4, ls_c := res, ls_pc := 5\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
                by (auto simp add: consistentSnapshot_def)

              from h[OF c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18']
              show "?thesis"
                by (meson example_chat.inv_def inv1_unchanged inv2_h1_unchanged inv2_unchanged)
            qed
          qed
        qed


        text {* send message *}
        show "checkCorrectAll progr S i"
          if c0: "invocationOp S i \<triangleq> (''sendMessage'', [UserId x2, String x1, ChatId x3])"
            and c1: "currentProc S i \<triangleq> sendMessageImpl"
            and c2: "localState S i \<triangleq> lsInit\<lparr>ls_from := UserId x2, ls_content := String x1, ls_to := ChatId x3\<rparr>"
            and c3: "uniqueIdsInList [UserId x2, String x1, ChatId x3] \<subseteq> knownIds S"
          for  x2 x1 x3
          sorry



      qed

end