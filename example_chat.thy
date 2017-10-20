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
  "is_message_updateH mid c \<equiv> 
  case c of 
     Call upd (mid'#args) _ \<Rightarrow> upd \<in> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''} \<and> mid = mid' 
   | _ \<Rightarrow> False"

lemma is_message_updateH_simp: "is_message_updateH mid (Call upd (mid'#args) res) \<longleftrightarrow> upd \<in> {''message_author_assign'', ''message_content_assign'', ''message_chat_assign''} \<and> mid = mid'"
  by (auto simp add: is_message_updateH_def)


abbreviation is_message_update :: "(val, 'b) operationContext_scheme \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where
  (*:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where *)
  "is_message_update ctxt c mId \<equiv> case calls ctxt c of Some call \<Rightarrow> is_message_updateH mId call | None \<Rightarrow> False "

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
  (\<exists>ca. calls ctxt ca \<triangleq> Call ''chat_add'' args Undef)
  \<and> (\<forall>cr. calls ctxt cr \<triangleq> Call ''chat_remove'' args Undef \<longrightarrow> (\<exists>ca. (cr,ca) \<in> happensBefore ctxt \<and> calls ctxt ca \<triangleq> Call ''chat_add'' args Undef))"

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


lemma is_message_update_vis_simps:
  "is_message_update (mkContext (invContextH co   to  ts  hb  cs  kids  iop  ires (Some vis))) c m
\<longleftrightarrow> (\<exists>call. cs c \<triangleq> call \<and>  is_message_updateH m call \<and> isCommittedH co ts c \<and> c \<in> vis)"
  by (auto simp add: mkContext_def invContextH_def restrict_map_def is_message_updateH_def commitedCallsH_def split: option.splits)


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
  using assms  by (auto simp add: inv2_h1_def mkContext_def invContextH_def)


lemma consistentSnapshot_subset:
  assumes cs: "consistentSnapshot S' vis"
    and calls1: "\<And>c. c\<notin>txCalls \<Longrightarrow> calls S' c = calls S c"
    and hb1: "\<And>c1 c2. c2\<notin>txCalls \<Longrightarrow>  (c1,c2)\<in>happensBefore S' \<longleftrightarrow> (c1,c2)\<in>happensBefore S"
    and hb2: "\<And>c1 c2. \<lbrakk>c1\<in>txCalls; c2\<notin>txCalls\<rbrakk> \<Longrightarrow>  (c1,c2)\<notin>happensBefore S"
    and co1: "\<And>c. c\<notin>txCalls \<Longrightarrow> callOrigin S' c = callOrigin S c"
    and co3: "\<And>c. c\<in>txCalls \<Longrightarrow> callOrigin S c = None"
    and co4: "\<And>c. callOrigin S c \<noteq> Some tx"
    and ts1: "\<And>t. t\<noteq>tx \<Longrightarrow> transactionStatus S' t = transactionStatus S t" 
    and wf: "\<And>c. calls S c \<noteq> None \<Longrightarrow> callOrigin S c \<noteq> None"
  shows "consistentSnapshot S (vis - txCalls)"
proof (auto simp add: consistentSnapshot_def)
  show vis_subset_calls: "\<And>x. \<lbrakk>x \<in> vis; x \<notin> txCalls\<rbrakk> \<Longrightarrow> \<exists>y. calls S x \<triangleq> y"
    by (metis basic_trans_rules(31) calls1 consistentSnapshot_def cs domD)

  from cs
  have cc: "causallyConsistent (happensBefore S') vis"
    by (simp add: consistentSnapshot_def)
  show "causallyConsistent (happensBefore S) (vis - txCalls)"
  proof (auto simp add: causallyConsistent_def)

    show "c2 \<in> vis"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "(c2, c1) \<in> happensBefore S"
      for  c1 c2
      using that
      by (meson causallyConsistent_def cc hb1) 


    show "False"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "(c2, c1) \<in> happensBefore S"
        and c3: "c2 \<in> txCalls"
      for  c1 c2
      using c1 c2 c3 hb2 by auto
  qed

  from cs
  have tc: "transactionConsistent (callOrigin S') (transactionStatus S') vis"
    by (simp add: consistentSnapshot_def)


  show "transactionConsistent (callOrigin S) (transactionStatus S) (vis - txCalls)"
  proof (auto simp add: transactionConsistent_def)

    show "transactionStatus S t \<triangleq> Commited"
      if c0: "c \<in> vis"
        and c1: "c \<notin> txCalls"
        and c2: "callOrigin S c \<triangleq> t"
      for  c t
      using that co1 co4 tc transactionConsistent_Commited ts1 by fastforce 

    show "c2 \<in> vis"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "callOrigin S c1 = callOrigin S c2"
      for  c1 c2
      using that
      by (metis co1 co3 local.wf option.distinct(1) tc transactionConsistent_all_from_same vis_subset_calls) 

    show "False"
      if c0: "c1 \<in> vis"
        and c1: "c1 \<notin> txCalls"
        and c2: "callOrigin S c1 = callOrigin S c2"
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
     apply auto
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
     apply auto
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




          text {* editMessage, case message does exist *}
          show h: "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S') (invocationOp S') (invocationRes S') (Some visa))"
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
              and c14: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)), happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
              and c15: "\<forall>c. callOrigin S' c \<noteq> Some t"
            for  t S' c vis ca resa visa
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
              by (simp add: c2 domD domI wellFormed_callOrigin_dom)



            find_theorems name: consistentSnapshot

            with `invariant_all S'` 
            have oldInv: "inv (invContextVis S' (visa - {c,ca}))"
              by (auto simp add: invariant_all_def)
            hence old_inv1: "inv1 (invContextVis S' (visa - {c, ca}))"
              and  old_inv2: "inv2 (invContextVis S' (visa - {c, ca}))"
              and old_inv2_h1: "inv2_h1 (invContextVis S' (visa - {c, ca}))"
              by (auto simp add: inv_def)

            show "inv1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
             (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S') (invocationOp S')
             (invocationRes S') (Some visa))"
            proof (auto simp add: inv1_def)
              fix cb m
              assume "crdtSpec_chat_contains_h [cb, m]
             (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                          (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
                          (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
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

              from this obtain c_add 
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
                by (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps split: if_splits)


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
                          (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
                          (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
                          (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))"
                apply (auto simp add: crdtSpec_message_exists_h_def mkContext_simps is_message_update_vis_simps)
                 apply (auto simp add: is_message_updateH_def isCommittedH_def split: option.splits)
                 apply fastforce
                by (metis no_calls_in_t)
            qed

            show "inv2 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S')
           (invocationOp S') (invocationRes S') (Some visa))"
            proof (auto simp add: inv2_def)
              fix m
              assume a_message_exists: "crdtSpec_message_exists_h [m]
          (mkContext (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited))
                       (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
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
                           (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
                           (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa))
                           (knownIds S') (invocationOp S') (invocationRes S') (Some visa)))
              (ListVal [a])"
                sorry
            qed


            show "inv2_h1 (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}))
              (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S')
              (invocationOp S') (invocationRes S') (Some visa))"
              sorry

          qed

          text {* editMessage, case message does exist, return from procedure  *}
          show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
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
              and c15: "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited), localState := (localState S')(i := None), currentProc := (currentProc S')(i := None), visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> Undef), knownIds := knownIds S' \<union> uniqueIds Undef\<rparr>) visa"
            for  t S' c vis ca resa visa
          proof -
            from c15
            have c15': "consistentSnapshot (S'\<lparr>calls := calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa), callOrigin := callOrigin S'(c \<mapsto> t, ca \<mapsto> t), visibleCalls := visibleCalls S'(i \<mapsto> insert ca (insert c vis)), happensBefore := insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca}), localState := localState S'(i \<mapsto> lsInit\<lparr>ls_id := MessageId mId, ls_pc := 4\<rparr>), currentTransaction := (currentTransaction S')(i := None), transactionStatus := transactionStatus S'(t \<mapsto> Commited)\<rparr>) visa"
              by (auto simp add: consistentSnapshot_def)

            from h[OF c0 c1 c2 c3 c4 c5 c6 c7 c9 c10 c11 c12 c13 c15' c8]
            show "example_chat.inv (invContextH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t)) (transactionOrigin S') (transactionStatus S'(t \<mapsto> Commited)) (insert (c, ca) (happensBefore S' \<union> vis \<times> {c} \<union> vis \<times> {ca})) (calls S'(c \<mapsto> Call ''message_exists'' [MessageId mId] (Bool True), ca \<mapsto> Call ''message_content_assign'' [MessageId mId, ls_content lsInit] resa)) (knownIds S' \<union> uniqueIds Undef) (invocationOp S') (invocationRes S'(i \<mapsto> Undef)) (Some visa))"
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



                from this obtain cc 
                  where cc4: "cc \<noteq> c"
                    and cc3: "calls S' cc \<triangleq> Call ''chat_add'' [ca, m] Undef"
                    and cc2: "cc \<in> visa"
                    and cc1: "isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cc"
                    and cc5: "\<forall>c'. isCommittedH (callOrigin S'(c \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) c' \<longrightarrow> calls S' c' \<triangleq> Call ''chat_remove'' [ca, m] Undef \<longrightarrow> c' \<in> visa \<longrightarrow> c' = c \<or> (cc, c') \<notin> happensBefore S' \<and> (cc \<in> vis \<longrightarrow> c' \<noteq> c)"
                  by (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps split: if_splits)


                hence "crdtSpec_chat_contains_h [ca, m] (mkContext (invContextVis S' (visa - {c})))"
                  apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps)
                  apply (rule_tac x=cc in exI)
                  apply (auto simp add: cc2 cc3)
                  using cc1 apply (auto simp add: isCommittedH_def no_calls_in_t split: if_splits)
                  done

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


                

                from a0' obtain cd 
                  where cd1: "isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) cd"
                    and cd2: "cd \<in> visa"
                    and cd3: "new_calls cd \<triangleq> Call ''chat_add'' [cc, m] Undef"
                    and cd4: "\<And>c'. isCommittedH (callOrigin S'(c \<mapsto> t, ca \<mapsto> t, cb \<mapsto> t)) (transactionStatus S'(t \<mapsto> Commited)) c' \<longrightarrow>
                (cd, c') \<in> new_hb \<longrightarrow> new_calls c' \<triangleq> Call ''chat_remove'' [cc, m] Undef \<longrightarrow> c' \<notin> visa"
                  by (auto simp add: crdtSpec_chat_contains_h_def mkContext_simps split: if_splits)

                have  [simp]: "cd \<noteq> ca" 
                  and [simp]: "cd \<noteq> c"
                  and [simp]: "cd \<noteq> cb"
                  using cd3 by (auto simp add: new_calls_def split: if_splits)

                have "cd \<in> commitedCalls S'"
                  using cd1 by (auto simp add: isCommittedH_def commitedCallsH_def no_calls_in_t split: if_splits)

                have "m \<noteq> MessageId x4" 



              (*we removed a chat message, so if something exists afterwards it should exist before: *)
                have "crdtSpec_chat_contains_h [cc, m] (mkContext (invContextVis S' (visa - {c, ca, cb})))"
                  apply (auto simp add: crdtSpec_chat_contains_h_def mkContext_def) 
                  apply (rule_tac x=cd in exI)
                  apply (auto simp add: invContextH_def restrict_map_def restrict_relation_def cd2 `cd \<in> commitedCalls S'`)
                proof -
                  show "calls S' cd \<triangleq> Call ''chat_add'' [cc, m] Undef"
                    using cd3 by (auto simp add: new_calls_def)

                  show "False"
                    if c0: "c' \<in> commitedCalls S'"
                      and c1: "c' \<in> visa"
                      and c2: "c' \<noteq> c"
                      and c3: "c' \<noteq> ca"
                      and c4: "c' \<noteq> cb"
                      and c5: "calls S' c' \<triangleq> Call ''chat_remove'' [cc, m] Undef"
                      and c6: "(cd, c') \<in> happensBefore S'"
                    for  c'
                    using that cd4[where c'=c'] by (auto simp add: commitedCallsH_def isCommittedH_def new_calls_def new_hb_def split: if_splits)
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