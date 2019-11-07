theory example_chat
  imports invariant_simps
begin




\<comment> \<open>^^^^\<close>

datatype val =
    String string
  | UserId int
  | ChatId int
  | MessageId int
  | Bool bool
  | Undef
  | ListVal "val list"
  | Pair val val
  | NotFound

fun uniqueIds_val_r  where 
  "uniqueIds_val_r (UserId i) = {UserId i}"
| "uniqueIds_val_r (MessageId i) = {MessageId i}"
| "uniqueIds_val_r (ListVal vs) = \<Union>(set (map uniqueIds_val_r vs))"
| "uniqueIds_val_r (Pair x y) = uniqueIds_val_r x \<union> uniqueIds_val_r y"
| "uniqueIds_val_r _ = {}"

instantiation val :: valueType begin
definition uniqueIds_val where 
  "uniqueIds_val x \<equiv> case x of 
       UserId u \<Rightarrow> {UserId u} 
     | MessageId i \<Rightarrow> {MessageId i}
     | _ \<Rightarrow> {}"
instance by standard
end

fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"

record localState = 
  ls_pc :: nat
  ls_m :: val
  ls_t :: val
  ls_from :: val
  ls_content :: val
  ls_to :: val
  ls_id :: val
  ls_c :: val

definition lsInit :: "localState" where
  "lsInit = \<lparr>
  ls_pc = 0,
  ls_m = Undef,
  ls_t = Undef,
  ls_from = Undef,
  ls_content = Undef,
  ls_to = Undef,
  ls_id = Undef,
  ls_c = Undef
\<rparr>"


definition "message_author_assign \<equiv> ''message_author_assign''"
definition "message_content_assign \<equiv> ''message_content_assign''"
definition "message_chat_assign \<equiv> ''message_chat_assign''"
definition "chat_add \<equiv> ''chat_add''"
definition "message_exists \<equiv> ''message_exists''"
definition "chat_remove \<equiv> ''chat_remove''"
definition "message_delete \<equiv> ''message_delete''"
definition "message_chat_read \<equiv> ''message_chat_read''"
definition "message_content_read \<equiv> ''message_content_read''"
definition "message_author_read \<equiv> ''message_author_read''"
definition "sendMessage \<equiv> ''sendMessage''"
definition "editMessage \<equiv> ''editMessage''"
definition "deleteMessage \<equiv> ''deleteMessage''"
definition "getMessage \<equiv> ''getMessage''"
definition "chat_contains \<equiv> ''chat_contains''"

lemma constants_distinct:
"distinct [message_author_assign, message_content_assign, message_chat_assign, chat_add, message_exists, chat_remove, message_delete, message_chat_read, 
  sendMessage, editMessage, deleteMessage, getMessage, message_content_read, message_author_read, chat_contains]"
  by (auto simp add: message_author_assign_def message_content_assign_def message_chat_assign_def chat_add_def message_exists_def chat_remove_def message_delete_def message_chat_read_def
sendMessage_def editMessage_def deleteMessage_def message_author_read_def message_content_read_def chat_contains_def getMessage_def)



lemma distinct_unfold1: "distinct [] \<longleftrightarrow> True"
  by auto

lemma distinct_unfold2: "distinct (x#xs) \<longleftrightarrow> x \<notin> set xs \<and> distinct xs"
  by auto

lemma distinct_unfold3: "a\<notin>set(x#xs) \<longleftrightarrow> a \<noteq> x \<and> x \<noteq> a \<and> a\<notin>set xs"
  by auto

lemma distinct_unfold4: "a\<notin>set[] \<longleftrightarrow> True"
  by auto

find_theorems "_ \<and> _ \<and> _"

schematic_goal constants_distinct2[simp]: "?P"
  apply (insert constants_distinct)
  apply (subst(asm) distinct_unfold1 distinct_unfold2 distinct_unfold3 distinct_unfold4 simp_thms(21) conj_assoc)+
  apply assumption
  done



definition sendMessageImpl :: "(localState, val) procedureImpl" where
  "sendMessageImpl ls \<equiv> [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> NewId (\<lambda>x. case x of MessageId m \<Rightarrow> Some (ls\<lparr>ls_m := x, ls_pc := 2\<rparr>) | _ \<Rightarrow> None),
   \<comment> \<open>  2  \<close> DbOperation message_author_assign [ls_m ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  3  \<close> DbOperation message_content_assign [ls_m ls, ls_content ls] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   \<comment> \<open>  4  \<close> DbOperation message_chat_assign [ls_m ls, ls_from ls] (\<lambda>r. ls\<lparr>ls_pc := 5\<rparr>),
   \<comment> \<open>  5  \<close> DbOperation chat_add [ls_to ls, ls_m ls] (\<lambda>r. ls\<lparr>ls_pc := 6\<rparr>),
   \<comment> \<open>  6  \<close> EndAtomic (ls\<lparr>ls_pc := 6\<rparr>),
   \<comment> \<open>  7  \<close> Return (ls_t ls)
   ] ! ls_pc ls"

definition editMessageImpl :: "(localState, val) procedureImpl" where
  "editMessageImpl ls \<equiv> [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation message_exists [ls_id ls] (\<lambda>r. if r = Bool True then ls\<lparr>ls_pc := 2\<rparr> else ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  2  \<close> DbOperation message_content_assign [ls_id ls, ls_content ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  3  \<close> EndAtomic  (ls\<lparr>ls_pc := 4\<rparr>),
   \<comment> \<open>  4  \<close> Return Undef
   ] ! ls_pc ls"   

definition deleteMessageImpl :: "(localState, val) procedureImpl" where
  "deleteMessageImpl ls \<equiv> [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation message_chat_read [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 2, ls_c := r\<rparr>),
   \<comment> \<open>  2  \<close> DbOperation chat_remove [ls_c ls, ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 3\<rparr>),
   \<comment> \<open>  3  \<close> DbOperation message_delete [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 4\<rparr>),
   \<comment> \<open>  4  \<close> EndAtomic  (ls\<lparr>ls_pc := 5\<rparr>),
   \<comment> \<open>  5  \<close> Return Undef
   ] ! ls_pc ls"      


definition getMessageImpl :: "(localState, val) procedureImpl" where
  "getMessageImpl ls \<equiv> [
   \<comment> \<open>  0  \<close> BeginAtomic (ls\<lparr>ls_pc := 1\<rparr>),
   \<comment> \<open>  1  \<close> DbOperation message_exists [ls_id ls] (\<lambda>r. if r = Bool True then ls\<lparr>ls_pc := 2\<rparr> else ls\<lparr>ls_pc := 7\<rparr>),
   \<comment> \<open>  2  \<close> DbOperation message_content_read [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 3, ls_c := r\<rparr>),
   \<comment> \<open>  3  \<close> DbOperation message_author_read [ls_id ls] (\<lambda>r. ls\<lparr>ls_pc := 4, ls_from := r\<rparr>),
   \<comment> \<open>  4  \<close> EndAtomic  (ls\<lparr>ls_pc := 5\<rparr>),
   \<comment> \<open>  5  \<close> Return (Pair (ls_c ls) (ls_from ls)),
   \<comment> \<open>  6  \<close> EndAtomic  (ls\<lparr>ls_pc := 7\<rparr>),
   \<comment> \<open>  7  \<close> Return NotFound
   ] ! ls_pc ls"      



definition procedures where
  "procedures proc args \<equiv> 
  if proc = sendMessage then
    case args of 
      [UserId from, String content, ChatId to] \<Rightarrow> 
        Some (lsInit\<lparr>ls_from := UserId from, ls_content := String content, ls_to := ChatId to \<rparr> , sendMessageImpl)
      | _ \<Rightarrow> None
  else if proc = editMessage then 
    case args of 
      [MessageId i] \<Rightarrow> 
        Some (lsInit\<lparr>ls_id := MessageId i \<rparr> , editMessageImpl)
      | _ \<Rightarrow> None
  else if proc = deleteMessage then 
    case args of 
      [MessageId i] \<Rightarrow> 
        Some (lsInit\<lparr>ls_id := MessageId i \<rparr> , deleteMessageImpl)
      | _ \<Rightarrow> None
  else if proc = getMessage then 
    case args of 
      [MessageId i] \<Rightarrow> 
        Some (lsInit\<lparr>ls_id := MessageId i \<rparr> , getMessageImpl)
      | _ \<Rightarrow> None
  else 
    None"

definition "callsOfOpH ctxt_calls opName \<equiv> {(c,args). ctxt_calls c \<triangleq> Call opName args Undef}"

abbreviation "callsOfOp ctxt opName \<equiv> callsOfOpH (calls ctxt) opName"

definition "callsWithOpArgsH ctxt_calls opName args \<equiv> {c. ctxt_calls c \<triangleq> Call opName args Undef}"

abbreviation "callsWithOpArgs ctxt opName args \<equiv> callsWithOpArgsH (calls ctxt) opName args"

(*
definition latest_name_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
  "latest_name_assign ctxt u \<equiv>  {v | c1 v. 
     (c1, [u, v]) \<in> callsOfOp ctxt users_name_assign
   \<and> (\<forall>c2\<in>callsWithOpArgs ctxt users_remove [u]. (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>(c2, args) \<in> callsOfOp ctxt users_name_assign. args!0 = u \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"

definition latest_mail_assign :: "val operationContext \<Rightarrow> val \<Rightarrow> val set" where
  "latest_mail_assign ctxt u \<equiv>  {v | c1 v. 
     (c1, [u, v]) \<in> callsOfOp ctxt users_mail_assign
   \<and> (\<forall>c2\<in>callsWithOpArgs ctxt users_remove [u]. (c2,c1)\<in>happensBefore ctxt)
   \<and> (\<forall>(c2, args) \<in> callsOfOp ctxt users_mail_assign. args!0 = u \<longrightarrow> \<not>(c1,c2)\<in>happensBefore ctxt)}"   
*)

definition crdtSpec_message_chat_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_chat_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
   (\<exists>c1\<in>callsWithOpArgs ctxt message_chat_assign (args@[v]).
       (\<forall>(c2,args')\<in>callsOfOp ctxt message_chat_assign. (\<exists>chat. args' = args@[chat]) \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2\<in>callsWithOpArgs ctxt message_delete args. (c2,c1)\<in>happensBefore ctxt)))"

definition crdtSpec_message_author_read :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_author_read args ctxt res \<equiv> \<exists>l.
  res = ListVal l 
 \<and> (\<forall>v. v\<in>set l \<longleftrightarrow> 
    (\<exists>c1\<in>callsWithOpArgs ctxt message_author_assign (args@[v]).
       (\<forall>(c2,args')\<in>callsOfOp ctxt message_author_assign. (\<exists>author. args' = args@[author]) \<longrightarrow> (c1,c2)\<notin>happensBefore ctxt)
     \<and> (\<forall>c2\<in>callsWithOpArgs ctxt message_delete args. (c2,c1)\<in>happensBefore ctxt)))"

definition is_message_updateH  where
  \<comment> \<open>:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where\<close>
  "is_message_updateH mid c \<equiv> 
  case c of 
     Call upd (mid'#args) _ \<Rightarrow> upd \<in> {message_author_assign, message_content_assign, message_chat_assign} \<and> mid = mid' 
   | _ \<Rightarrow> False"

lemma is_message_updateH_simp: "is_message_updateH mid (Call upd (mid'#args) res) \<longleftrightarrow> upd \<in> {message_author_assign, message_content_assign, message_chat_assign} \<and> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp1[simp]: "is_message_updateH mid (Call message_author_assign (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp2[simp]: "is_message_updateH mid (Call message_content_assign (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp3[simp]: "is_message_updateH mid (Call message_chat_assign (mid'#args) res) \<longleftrightarrow> mid = mid'"
  by (auto simp add: is_message_updateH_def)

lemma is_message_updateH_simp4[simp]: "  \<not>is_message_updateH mid (Call upd (mid'#args) res)" if "upd \<notin> {message_author_assign, message_content_assign, message_chat_assign}"
  using that  by (auto simp add: is_message_updateH_def )

definition message_updates :: "(callId \<rightharpoonup> val call) \<Rightarrow> val \<Rightarrow> callId set" where
  \<comment> \<open>:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where\<close>
  "message_updates ctxt_calls mId \<equiv> {c | c call . ctxt_calls c = Some call \<and> is_message_updateH mId call}"

abbreviation is_message_update :: "(val, 'b) operationContext_scheme \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where
  \<comment> \<open>:: "val operationContext \<Rightarrow> callId \<Rightarrow> val \<Rightarrow> bool" where\<close>
  "is_message_update ctxt c mId \<equiv> c \<in> message_updates (calls ctxt) mId "

definition crdtSpec_message_exists_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
  "crdtSpec_message_exists_h args ctxt \<equiv> 
  \<exists>mId.
  args = [mId]
 \<and> (\<exists>c. is_message_update ctxt c mId)
 \<and> (\<forall>c\<in>callsWithOpArgs ctxt message_delete args. 
          (\<exists>c'. (c,c')\<in>happensBefore ctxt \<and> is_message_update ctxt c mId))"

schematic_goal crdtSpec_message_exists_h_def2:
"crdtSpec_message_exists_h [mId] ctxt = ((\<exists>c. is_message_update ctxt c mId)
 \<and> (\<forall>c\<in>callsWithOpArgs ctxt message_delete [mId]. 
          (\<exists>c'. (c,c')\<in>happensBefore ctxt \<and> is_message_update ctxt c mId)))"
  by (auto simp add: crdtSpec_message_exists_h_def)

definition crdtSpec_message_exists :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_message_exists args ctxt res \<equiv> 
  res = Bool (crdtSpec_message_exists_h args ctxt)"

\<comment> \<open>ignores map-deletes as they are not used\<close>
definition crdtSpec_chat_contains_h :: "val list \<Rightarrow> val operationContext \<Rightarrow> bool" where
  "crdtSpec_chat_contains_h args ctxt \<equiv> 
  (callsWithOpArgs ctxt chat_add args \<noteq> {})
  \<and> (\<forall>cr\<in>callsWithOpArgs  ctxt chat_remove args. (\<exists>ca\<in>callsWithOpArgs ctxt chat_add args. (cr,ca) \<in> happensBefore ctxt))"

definition crdtSpec_chat_contains :: "val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec_chat_contains args ctxt res \<equiv> 
  res = Bool (crdtSpec_chat_contains_h args ctxt)"


definition crdtSpec :: "operation \<Rightarrow> val list \<Rightarrow> val operationContext \<Rightarrow> val \<Rightarrow> bool" where
  "crdtSpec oper  \<equiv> 
  if oper = message_chat_read then crdtSpec_message_chat_read
  else if oper = message_author_read then crdtSpec_message_author_read
  else if oper = chat_contains then crdtSpec_chat_contains
  else if oper = message_exists then crdtSpec_message_exists
  else 
    \<comment> \<open>  other operations are updates and don't have a result  \<close>
    (\<lambda>args ctxt res. res = Undef)"


find_consts name: "consistentSnapshot"

definition mkContext :: "'a invariantContext \<Rightarrow> callId set \<Rightarrow> 'a operationContext" where
  "mkContext ctxt vis \<equiv> \<lparr>
  calls = calls ctxt |` vis,
  happensBefore = happensBefore ctxt  |r vis
\<rparr>"

definition forAllSnapshots :: "'a invariantContext \<Rightarrow> ('a operationContext \<Rightarrow>  bool) \<Rightarrow> bool" where
"forAllSnapshots ctxt P  \<equiv> \<forall>vis. consistentSnapshotI ctxt vis \<longrightarrow> P (mkContext ctxt vis)"



lemma mkContext_calls[simp]:
"calls (mkContext ctxt vis) = calls ctxt |` vis"
  by (auto simp add: mkContext_def)

lemma mkContext_happensBefore[simp]:
"happensBefore (mkContext ctxt vis) = happensBefore ctxt  |r vis"
  by (auto simp add: mkContext_def)

(*
lemma mkContext_calls_simps: "calls (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis) vis) 
= state_calls |` (committedCallsH state_callOrigin state_transactionStatus \<inter> (vis orElse {}))"
  by (auto simp add: mkContext_def invContextH_def )

lemma mkContext_calls_eq_simps: "calls (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) c \<triangleq> x
\<longleftrightarrow> (isCommittedH state_callOrigin state_transactionStatus c \<and> c \<in> vis orElse {} \<and> state_calls c \<triangleq> x)"
  by (auto simp add: mkContext_def invContextH_def committedCallsH_def  restrict_map_def)

lemma mkContext_happensBefore_simps: "happensBefore (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) 
= state_happensBefore |r committedCallsH state_callOrigin state_transactionStatus |r (vis orElse {})"
  by (auto simp add: mkContext_def invContextH_def )

lemma mkContext_happensBefore_contains_simps: "(c1,c2) \<in> happensBefore (mkContext (invContextH state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes vis)) 
= ( (c1, c2) \<in> state_happensBefore 
    \<and> isCommittedH state_callOrigin state_transactionStatus c1 \<and> c1 \<in> vis orElse {} 
    \<and> isCommittedH state_callOrigin state_transactionStatus c2 \<and> c2 \<in> vis orElse {}
            )"
  by (auto simp add: mkContext_def invContextH_def committedCallsH_def restrict_map_def restrict_relation_def)

lemmas mkContext_simps = mkContext_happensBefore_contains_simps mkContext_calls_eq_simps
*)


(*
(* property 1:
If the chat contains a reference to a message, the message exists
 *)
definition inv1 :: "val invariantContext \<Rightarrow> bool" where
  "inv1 ctxt \<equiv> forAllSnapshots ctxt (\<lambda>s.  \<forall>c m. crdtSpec_chat_contains_h [c,m] s \<longrightarrow> crdtSpec_message_exists_h [m] s)"

(* property 2:
If a message exists, there is exactly one author set for the message 
We know this, because we never update the author...
*)
definition inv2 :: "val invariantContext \<Rightarrow> bool" where
  "inv2 ctxt \<equiv> forAllSnapshots ctxt (\<lambda>s. \<forall>m. crdtSpec_message_exists_h [m] s \<longrightarrow> (\<exists>a. crdtSpec_message_author_read [m] s (ListVal [a])))"

(*
There are no updates to a message after it has been deleted
*)
definition inv2_h1 :: "val invariantContext \<Rightarrow> bool" where
  "inv2_h1 ctxt \<equiv> (\<forall>c mId. calls ctxt c \<triangleq> Call message_delete [mId] Undef \<longrightarrow> (\<nexists>c'. is_message_update ctxt c' mId \<and> (c,c')\<in>happensBefore ctxt ))"


\<comment> \<open>The author of a message does not change\<close>
definition inv3 :: "val invariantContext \<Rightarrow> bool" where
  "inv3 ctxt \<equiv> (\<forall> m i1 a1 c1 i2  a2 c2. 
     invocationOp ctxt i1 \<triangleq> (getMessage, [MessageId m]) 
   \<and> invocationRes ctxt i1 \<triangleq> Pair a1 c1
   \<and> invocationOp ctxt i2 \<triangleq> (getMessage, [MessageId m])
   \<and> invocationRes ctxt i2 \<triangleq> Pair a2 c2
   \<longrightarrow> a1 = a2
     )"
*)


text " getMessage returns correct authors"
definition inv1  :: "val invariantContext \<Rightarrow> bool" where
"inv1 ctxt \<equiv> \<forall>g m author content.
   invocationOp ctxt g \<triangleq> (getMessage, [MessageId m])
 \<and> invocationRes ctxt g \<triangleq> Pair author content
 \<longrightarrow> (\<exists>s content2. invocationOp ctxt s \<triangleq> (sendMessage, [author, content2])) "

text "Additional invariants:"

definition inv1a :: "val invariantContext \<Rightarrow> bool" where
"inv1a ctxt \<equiv> \<forall>c m u.
  calls ctxt c \<triangleq> Call message_author_assign [m,u] Undef 
  \<longrightarrow> (\<exists>i s. invocationOp ctxt i \<triangleq> (sendMessage, [u, s]))"

definition inv1b :: "val invariantContext \<Rightarrow> bool" where
"inv1b ctxt \<equiv> \<forall>c m u.
  calls ctxt c \<triangleq> Call message_content_assign [m,u] Undef 
  \<longrightarrow> (\<exists>c' u. calls ctxt c' \<triangleq> Call message_author_assign [m,u] Undef \<and> (c', c)\<in>happensBefore ctxt)"

definition inv1c :: "val invariantContext \<Rightarrow> bool" where
"inv1c ctxt \<equiv>
  \<not>(\<exists>write delete m. 
      ((\<exists>u. calls ctxt write \<triangleq> Call message_author_assign [m,u] Undef)
       \<or> (\<exists>u. calls ctxt write \<triangleq> Call message_content_assign [m,u] Undef))
      \<and> calls ctxt delete \<triangleq> Call message_delete [m] Undef
      \<and> (delete, write) \<in> happensBefore ctxt
)"



definition inv :: "val invariantContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> inv1 ctxt \<and> inv1a ctxt \<and> inv1b ctxt \<and> inv1c ctxt"

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
definition initialStates :: "('localState, 'any) prog \<Rightarrow> invocId \<Rightarrow> ('localState, 'any) state set"  where
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
  \<and> state_wellFormed S \<comment> \<open>   TODO add wellformed?  \<close>
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

(*
lemma is_message_update_vis_simps:
  "is_message_update (mkContext (invContextH co   to  ts  hb  cs  kids  iop  ires (Some vis)) vis) c m
\<longleftrightarrow> (\<exists>call. cs c \<triangleq> call \<and>  is_message_updateH m call \<and> isCommittedH co ts c \<and> c \<in> vis)"
  by (auto simp add: message_updates_def mkContext_def invContextH_def restrict_map_def is_message_updateH_def committedCallsH_def split: option.splits)



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
  using assms  by (auto simp add: message_updates_def inv2_h1_def mkContext_def invContextH_def)
*)

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

    show "S_transactionStatus t \<triangleq> Committed"
      if c0: "c \<in> vis"
        and c1: "c \<notin> txCalls"
        and c2: "S_callOrigin c \<triangleq> t"
      for  c t
      using that co1 co4 tc transactionConsistent_Committed ts1 by fastforce 

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
  then have "B = {}"
    by blast
  then show ?case by simp
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
  using \<open>finite (dom m)\<close> proof (rule finite_mapping)
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
  shows  "\<exists>res. crdtSpec message_chat_read args ctxt res"
  apply (auto simp add: crdtSpec_def)
  apply (rule Ex_quantor)
  apply (auto simp add: crdtSpec_message_chat_read_def )
  apply (rule finite_list_exists)

  apply (rule_tac B="{v. \<exists>c. calls ctxt c \<triangleq> Call message_chat_assign (args @ [v]) Undef}" in finite_subset)
   apply (auto simp add: callsWithOpArgsH_def)
  apply (rule finite_mapping3[OF \<open>finite (dom (calls ctxt))\<close>])
  by (meson append1_eq_conv call.inject injI)


lemma every_query_has_result_message_author_read:
  assumes "finite (dom (calls ctxt))"
  shows  "\<exists>res. crdtSpec message_author_read args ctxt res"
  apply (auto simp add: crdtSpec_def)
  apply (rule Ex_quantor)
  apply (auto simp add: crdtSpec_message_author_read_def)
  apply (rule finite_list_exists)
  apply (rule_tac B="{v. \<exists>c. calls ctxt c \<triangleq> Call message_author_assign (args @ [v]) Undef}" in finite_subset)
   apply (auto simp add: callsWithOpArgsH_def)
  apply (rule finite_mapping3[OF \<open>finite (dom (calls ctxt))\<close>])
  by (meson append1_eq_conv call.inject injI)

lemma every_query_has_result_chat_contains[simp]:
  shows  "\<exists>res. crdtSpec chat_contains args ctxt res"
  apply (auto simp add: crdtSpec_def)
  by (auto simp add: crdtSpec_chat_contains_def)

lemma every_query_has_result_message_exists[simp]:
  shows  "\<exists>res. crdtSpec message_exists args ctxt res"
  apply (auto simp add: crdtSpec_def)
  by (auto simp add: crdtSpec_message_exists_def)

lemma every_query_has_result_assign[simp]:
  shows "crdtSpec message_author_assign args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec message_content_assign args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec message_chat_assign args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec chat_add args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec chat_remove args ctxt res \<longleftrightarrow> res = Undef"
"crdtSpec message_delete args ctxt res \<longleftrightarrow> res = Undef"
  by (auto simp add: crdtSpec_def)

lemma every_query_has_result:
  assumes fin: "finite (dom (calls ctxt))"
  shows  "\<exists>res. crdtSpec procName args ctxt res"
  apply (case_tac "procName = message_chat_read"; case_tac "procName = message_author_read"; case_tac "procName = chat_contains"; case_tac "procName = message_exists")
                 apply (auto simp add: every_query_has_result_message_chat_read[OF fin] every_query_has_result_message_author_read[OF fin])
  apply (auto simp add: crdtSpec_def )
  done



lemma committedCalls_simps[simp]:
  assumes noUncommitted: "\<And>tx. tx\<in>Option.these(range (callOrigin S)) \<Longrightarrow>  transactionStatus S tx \<noteq> Some Uncommitted"
    and wf: "state_wellFormed S"
  shows "committedCalls S = dom (calls S)"
  using assms apply (auto simp add: committedCallsH_def isCommittedH_def domD domIff wellFormed_callOrigin_dom3)
  by (smt domD domIff in_these_eq option.distinct(1) rangeI transactionStatus.exhaust wellFormed_callOrigin_dom wellFormed_state_callOrigin_transactionStatus)



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




(*  
lemma invariant_all_def2:
"invariant_all state =
 (\<forall>vis. vis \<subseteq> dom (calls state) \<and> consistentSnapshot state vis
 \<longrightarrow> invariant (prog state) (invContextVis state vis))"
  by (auto simp add: )
*)

lemma calls_restrict_simps[simp]:
"((calls S |` vis) c \<triangleq> ci) = (c \<in> vis \<and> calls S c \<triangleq> ci)"
  by (simp add: restrict_map_def)

lemma committedCallsH_true:
  assumes "cOrig c \<triangleq> t" and "tStatus t \<triangleq> Committed"
  shows "c \<in> committedCallsH cOrig tStatus"
  using assms  by (auto simp add: committedCallsH_def isCommittedH_def)

lemma committedCallsH_simp:
  assumes "tStatus t \<triangleq> Committed"
  shows "committedCallsH (cOrig(c \<mapsto> t)) (tStatus) = insert c (committedCallsH cOrig tStatus)"
  using assms  by (auto simp add: committedCallsH_def isCommittedH_def)

(*
lemma callsWithOpArgs_simps:
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommitted"
  shows "callsWithOpArgs (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  ) (Some vis)) opName args = {c\<in>vis. state_calls c \<triangleq> Call opName args Undef}"
  apply (auto simp add: callsWithOpArgsH_def)
    apply (auto simp add: committedCallsH_def isCommittedH_def restrict_map_def  split: if_splits)
  by (metis consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Committed)
*)
lemmas wellFormed_callOrigin_dom[simp]



lemma wellFormed_callOrigin_transactionStatus[simp]:
  assumes wf: "state_wellFormed S"
  shows  "Option.these (range (callOrigin S)) \<subseteq> dom (transactionStatus S)"

  using wf apply (induct rule: wellFormed_induct)
   apply (simp add: initialState_def)

  apply (erule step.cases)
          apply (auto split: if_splits)
  by (metis (no_types, lifting) domD domIff image_iff in_these_eq wf_no_transactionStatus_origin_for_nothing)



(*
lemma callsOfOp_simps:
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommitted"
  shows "callsOfOp (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  )) opName = {(c,args). c\<in>vis \<and> state_calls c \<triangleq> Call opName args Undef}"
  apply (auto simp add: callsOfOpH_def)
    apply (auto simp add: committedCallsH_def isCommittedH_def restrict_map_def   split: if_splits)
  by (metis consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Committed)
*)

(*
lemma is_message_update_simps1: 
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
  shows "is_message_update (mkContext (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  )) c mId \<longleftrightarrow> c\<in>vis \<and> (\<exists>call.  state_calls c = Some call \<and> is_message_updateH mId call)"
  apply (auto simp add: message_updates_def simp add: restrict_map_def split: option.splits)
  by (metis committedCallsH_true consistentSnapshotH_def cs domD domI local.wf transactionConsistent_Committed)


lemma is_message_update_simps2: 
  assumes cs: "consistentSnapshotH state_calls state_happensBefore state_callOrigin state_transactionStatus vis"
    and wf: "dom state_callOrigin = dom  state_calls"
    and wf2: "Option.these (range state_callOrigin) \<subseteq> dom state_transactionStatus"
    and noUncommitted: "\<forall>tx. state_transactionStatus tx \<noteq> Some Uncommitted"
shows "is_message_update
         (invContextH
state_callOrigin state_transactionOrigin state_transactionStatus state_happensBefore 
   state_calls state_knownIds state_invocationOp state_invocationRes (Some vis)
  ) c mId \<longleftrightarrow>(\<exists>call. state_calls c = Some call \<and> is_message_updateH mId call)"
  apply (auto simp add: message_updates_def committedCallsH_def  isCommittedH_def  simp add: restrict_map_def split: option.splits)
  by (smt domD domI in_these_eq less_eq_transactionStatus_def local.wf noUncommitted order_refl rangeI set_rev_mp wf2)


lemmas is_message_update_simps = is_message_update_simps1 is_message_update_simps2
*)

lemma happensBefore_restrict_wf[simp]:
  assumes wf: "state_wellFormed S"
  shows "happensBefore S |r dom (calls S) = happensBefore S"
  apply (auto simp add: restrict_relation_def)
  apply (simp add: domD happensBefore_in_calls_left local.wf)
  by (simp add: domD happensBefore_in_calls_right local.wf)

lemma restrict_case_simps: 
"(case (m |` S) x of None \<Rightarrow> False | Some x \<Rightarrow> P x) \<longleftrightarrow> x\<in>S \<and> (case m x of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (metis option.simps(4) restrict_in restrict_out)

(*
lemma invContextH_simps_allCommitted:
  assumes no_uncommitted: "\<And>tx. state_transactionStatus tx \<noteq> Some Uncommitted"
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
    apply (auto simp add: invContextH_def restrict_map_def restrict_relation_def committedCallsH_def  no_uncommitted intro!: ext split: if_splits)
    using h1 apply force
    using wf3a h1 apply auto[1]
    using wf3b h1 apply auto[1]
    apply (metis domD domIff h1 wf1)
    by (metis (full_types) domD domIff no_uncommitted transactionStatus.exhaust wf4)
qed
*)

lemmas wellFormed_visibleCallsSubsetCalls_prod[simp] = wellFormed_visibleCallsSubsetCalls_h(1)
lemmas wf_transaction_status_iff_origin_dom_simp[simp] = wf_transaction_status_iff_origin_dom

lemma wellFormed_happensBefore_calls_l'[simp]: "state_wellFormed S \<Longrightarrow> fst ` happensBefore S \<subseteq> dom (calls S)"
  using wellFormed_happensBefore_calls_l by fastforce

lemma wellFormed_happensBefore_calls_r'[simp]: "state_wellFormed S \<Longrightarrow> snd ` happensBefore S \<subseteq> dom (calls S)"
  using wellFormed_happensBefore_calls_r by fastforce

lemma invContextH_simps_allCommitted2:
  assumes no_uncommitted[simp]: "\<And>tx. transactionStatus S tx \<noteq> Some Uncommitted"
    and wf[simp]: "state_wellFormed S"
  shows
 "invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S)
   (calls S) (knownIds S) (invocationOp S) (invocationRes S)  = \<lparr>
        calls = calls S, 
        happensBefore = happensBefore S, 
        callOrigin  = callOrigin S,
        transactionOrigin = transactionOrigin S,
        knownIds = knownIds S,
        invocationOp = invocationOp S,
        invocationRes = invocationRes S
      \<rparr>"
  by (simp add: invContext_same_allCommitted)


lemma these_range_update[simp]: "f x = None \<Longrightarrow> Option.these ( range (f(x \<mapsto> y))) = insert y (Option.these (range f))"
  apply (auto simp add: fun_upd_def image_iff in_these_eq)
  by force

lemma updateHb_fst[simp]: "fst ` updateHb hb vis cs = (if cs = [] then fst`hb else fst ` hb \<union> vis \<union> set (butlast cs))"
  by (induct cs arbitrary: hb vis, auto simp add: updateHb_cons image_Un)

lemma updateHb_snd[simp]: "snd ` updateHb hb vis cs = (snd ` hb \<union> (if vis={} then set (tl cs) else set cs))"
  by (induct cs arbitrary: hb vis, auto simp add: updateHb_cons image_Un)

lemma callsWithOpArgsH_update_simps[simp]:
  assumes "cs c = None"
  shows  "callsWithOpArgsH (cs(c \<mapsto> Call opName' args' res')) opName args  
        = callsWithOpArgsH cs opName args \<union> (if opName' = opName \<and> args' = args \<and> res' = Undef then {c} else {})"
  using assms by (auto simp add: callsWithOpArgsH_def)


lemma message_updates_update_simps[simp]:
  assumes "cs c = None"
  shows "message_updates (cs(c \<mapsto> Call opName args res)) mId 
      = message_updates cs mId \<union> (if is_message_updateH mId (Call opName args res) then {c} else {})"
  using assms  by (auto simp add: message_updates_def)

lemma restrict_map_dom[simp]: "m |` dom m = m" for m
  by (auto simp add: restrict_map_def domD domIff)

lemma dom_exists: "x\<in>dom m \<longleftrightarrow> (\<exists>y. m x \<triangleq> y)"
  by auto

lemma exists_eq_simp: "(\<exists>a. \<forall>v. (v=a) \<longleftrightarrow> P a v) \<longleftrightarrow> (\<exists>a. P a a \<and> (\<forall>v. v\<noteq>a \<longrightarrow> \<not>P a v))"
  by auto

lemma procedure_cases2: "procedures procName args \<triangleq> (initState, impl) \<longleftrightarrow> (
  (\<exists>from content to. procName = sendMessage \<and> args = [UserId from, String content, ChatId to] \<and> initState = lsInit\<lparr>ls_from := UserId from, ls_content := String content, ls_to := ChatId to \<rparr> \<and> impl = sendMessageImpl)
\<or> (\<exists>i. procName = editMessage \<and> args = [MessageId i] \<and> initState = lsInit\<lparr>ls_id := MessageId i \<rparr> \<and> impl = editMessageImpl)
\<or> (\<exists>i. procName = deleteMessage \<and> args = [MessageId i] \<and> initState = lsInit\<lparr>ls_id := MessageId i \<rparr> \<and> impl = deleteMessageImpl))
\<or> (\<exists>i. procName = getMessage \<and> args = [MessageId i] \<and> initState = lsInit\<lparr>ls_id := MessageId i\<rparr> \<and> impl = getMessageImpl)
"
  by (auto simp add: procedures_def split: list.splits val.splits)


lemma forAllSnapshots_dont_care:
"forAllSnapshots (invContextH2 co to ts hb cs ki io ir) P
\<Longrightarrow> forAllSnapshots (invContextH2 co to' ts' hb cs ki' io' ir') P"
  by (auto simp add: forAllSnapshots_def mkContext_def)



theorem chatapp_correct: "programCorrect progr"
proof (rule show_programCorrect_using_checkCorrect)
  have [simp]: "invariant progr = inv" by simp

  have [simp]: "S \<in> initialStates progr i \<Longrightarrow> prog S = progr" for S i
    by (auto simp add: initialStates_def)


  subsection \<open>Initial state\<close>

  text \<open>Show that the initial state satisfies the invariant\<close>
  show "invariant_all' (initialState progr)"
    by (auto simp add: forAllSnapshots_def message_updates_def initialState_def  inv_def inv1_def inv2_def inv2_h1_def invContextH_def crdtSpec_message_exists_h_def crdtSpec_chat_contains_h_def mkContext_def is_message_updateH_def callsWithOpArgsH_def)


  subsection \<open>Initial state of procedure invocations\<close>

  text \<open>Show that the initial state of procedure invocations satisfies the invariant.\<close>
  show "\<And>S i. S \<in> initialStates' progr i \<Longrightarrow> invariant_all' S"
    apply (subst(asm) initialStates'_def)
  proof auto

    show "example_chat.inv (invContextH2 (callOrigin Sa) (transactionOrigin Sa) (transactionStatus Sa) (happensBefore Sa) (calls Sa) (knownIds Sa) (invocationOp Sa(i \<mapsto> (procName, args))) (invocationRes Sa))"
      if i0: "prog Sa = progr"
        and i1: "procedures procName args \<triangleq> (initState, impl)"
        and i2: "uniqueIdsInList args \<subseteq> knownIds Sa"
        and old_inv: "example_chat.inv (invContext' Sa)"
        and i4: "state_wellFormed Sa"
        and i5: "invocationOp Sa i = None"
        and i6: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"
        and i7: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
      for  i Sa procName args initState impl

      using i1 proof (subst(asm) procedure_cases2, auto)

      text \<open>We consider the initial state for each procedure individually:\<close>


      show "example_chat.inv (invContextH2 (callOrigin Sa) (transactionOrigin Sa) (transactionStatus Sa) (happensBefore Sa) (calls Sa) (knownIds Sa) (invocationOp Sa(i \<mapsto> (sendMessage, [UserId from, String content, ChatId to]))) (invocationRes Sa))"
        if c0: "procedures sendMessage [UserId from, String content, ChatId to] \<triangleq> (lsInit\<lparr>ls_from := UserId from, ls_content := String content, ls_to := ChatId to\<rparr>, sendMessageImpl)"
          and c1: "procName = sendMessage"
          and c2: "args = [UserId from, String content, ChatId to]"
          and c3: "impl = sendMessageImpl"
          and c4: "initState = lsInit\<lparr>ls_from := UserId from, ls_content := String content, ls_to := ChatId to\<rparr>"
        for "from" content to
        using old_inv
        apply (auto simp add: inv_def inv1_def inv1a_def inv1b_def inv1c_def forAllSnapshots_dont_care)
        by (metis i5 option.distinct(1))+



      show "example_chat.inv (invContextH2 (callOrigin Sa) (transactionOrigin Sa) (transactionStatus Sa) (happensBefore Sa) (calls Sa) (knownIds Sa) (invocationOp Sa(i \<mapsto> (editMessage, [MessageId ia]))) (invocationRes Sa))"
        if c0: "procedures editMessage [MessageId ia] \<triangleq> (lsInit\<lparr>ls_id := MessageId ia\<rparr>, editMessageImpl)"
          and c1: "procName = editMessage"
          and c2: "args = [MessageId ia]"
          and c3: "impl = editMessageImpl"
          and c4: "initState = lsInit\<lparr>ls_id := MessageId ia\<rparr>"
        for  ia
        using old_inv
        apply (auto simp add: inv_def inv1_def inv1a_def inv1b_def inv1c_def forAllSnapshots_dont_care)
        by (metis i5 option.distinct(1))+



      show "example_chat.inv (invContextH2 (callOrigin Sa) (transactionOrigin Sa) (transactionStatus Sa) (happensBefore Sa) (calls Sa) (knownIds Sa) (invocationOp Sa(i \<mapsto> (deleteMessage, [MessageId ia]))) (invocationRes Sa))"
        if c0: "procedures deleteMessage [MessageId ia] \<triangleq> (lsInit\<lparr>ls_id := MessageId ia\<rparr>, deleteMessageImpl)"
          and c1: "procName = deleteMessage"
          and c2: "args = [MessageId ia]"
          and c3: "impl = deleteMessageImpl"
          and c4: "initState = lsInit\<lparr>ls_id := MessageId ia\<rparr>"
        for  ia
        using old_inv
        apply (auto simp add: inv_def inv1_def inv1a_def inv1b_def inv1c_def forAllSnapshots_dont_care)
        by (metis i5 option.distinct(1))+

      show "example_chat.inv (invContextH2 (callOrigin Sa) (transactionOrigin Sa) (transactionStatus Sa) (happensBefore Sa) (calls Sa) (knownIds Sa) (invocationOp Sa(i \<mapsto> (getMessage, [MessageId ia]))) (invocationRes Sa))"
        if c0: "procedures getMessage [MessageId ia] \<triangleq> (lsInit\<lparr>ls_id := MessageId ia\<rparr>, getMessageImpl)"
          and c1: "procName = getMessage"
          and c2: "args = [MessageId ia]"
          and c3: "impl = getMessageImpl"
          and c4: "initState = lsInit\<lparr>ls_id := MessageId ia\<rparr>"
        for  ia
        using old_inv
        apply (auto simp add: inv_def inv1_def inv1a_def inv1b_def inv1c_def forAllSnapshots_dont_care)
        apply (simp add: i4 i5 wf_result_after_invocation)
        by (metis i5 option.distinct(1))+


    qed
  qed


  show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, S, i)"
    if c0: "S \<in> initialStates' progr i"
    for  S i


 using c0  apply (subst(asm) initialStates'_def)
  proof auto

    show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>, i)"
      if S_def: "S = Sa \<lparr>localState := localState Sa(i \<mapsto> initState), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (procName, args))\<rparr>"
        and prog_Sa: "prog Sa = progr"
        and procedures: "procedures procName args \<triangleq> (initState, impl)"
        and uniqueIds_args: "uniqueIdsInList args \<subseteq> knownIds Sa"
        and inv_Sa: "example_chat.inv (invContext' Sa)"
        and Sa_wf: "state_wellFormed Sa"
        and invoc_Sa: "invocationOp Sa i = None"
        and transactions_Sa: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"
        and transactionOriginSa: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
      for  Sa procName args initState impl
 using procedures proof (subst(asm) procedure_cases2, auto)



      have [simp]: "currentTransaction Sa i = None"
        by (simp add: Sa_wf invoc_Sa wellFormed_invoc_notStarted(1))

\<comment> \<open>ony unfold definitions, when needed for evaluation:\<close>
      have h1[simp]:  "S' ::= S \<Longrightarrow> (currentProc S' i \<triangleq> x) \<longleftrightarrow> (currentProc S i \<triangleq> x)" for S' S i x  by (auto simp add: Def_def)
      have h2[simp]: "S' ::= S \<Longrightarrow>  ls_pc (the (localState S' i)) = ls_pc (the (localState S i))" for S' S i by (auto simp add: Def_def)
      have h3[simp]: "S' ::= S \<Longrightarrow>  (currentTransaction S' i = None) \<longleftrightarrow> (currentTransaction S i = None)" for S' S i by (auto simp add: Def_def)

      thm inv1a_def

      have queries_defined_message_author_assign[simp]: 
        "Ex (querySpec progr message_author_assign [u, n] ctxt)"
        for u n ctxt
        by (auto simp add: progr_def crdtSpec_def )

      have queries_defined_message_content_assign[simp]: 
        "Ex (querySpec progr message_content_assign [u, n] ctxt)"
        for u n ctxt
        by (auto simp add: progr_def crdtSpec_def )

      have queries_defined_chat_add[simp]: 
        "Ex (querySpec progr chat_add [u, n] ctxt)"
        for u n ctxt
        by (auto simp add: progr_def crdtSpec_def )



      have queries_defined_message_content_read[simp]: 
        "Ex (querySpec progr message_content_read [m] ctxt)"
        for m ctxt
        by (auto simp add: progr_def crdtSpec_def )


      have h: "\<exists>l. \<forall>v. (v \<in> set l) = P v " if fin: "finite {x. P x}"   for P
        by (simp add: finite_list_exists that)

      have queries_defined_message_author_read[simp]: 
        "Ex (querySpec progr message_author_read [m] ctxt)"
        for m ctxt
        apply (auto simp add: progr_def crdtSpec_def )
        apply (rule ccontr)
        apply (auto simp add: crdtSpec_message_author_read_def)
        apply (erule contrapos_pp)
        apply auto
      proof (rule h)
        show "finite
     {x. \<exists>c1\<in>callsWithOpArgs ctxt message_author_assign [m, x].
            (\<forall>x\<in>callsOfOp ctxt message_author_assign.
                case x of (c2, args') \<Rightarrow> (\<exists>author. args' = [m, author]) \<longrightarrow> (c1, c2) \<notin> happensBefore ctxt) \<and>
            (\<forall>c2\<in>callsWithOpArgs ctxt message_delete [m]. (c2, c1) \<in> happensBefore ctxt)}"

        proof (rule finite_subset)
          show "{x. \<exists>c1\<in>callsWithOpArgs ctxt message_author_assign [m, x].
            (\<forall>x\<in>callsOfOp ctxt message_author_assign.
                case x of (c2, args') \<Rightarrow> (\<exists>author. args' = [m, author]) \<longrightarrow> (c1, c2) \<notin> happensBefore ctxt) \<and>
            (\<forall>c2\<in>callsWithOpArgs ctxt message_delete [m]. (c2, c1) \<in> happensBefore ctxt)}
\<subseteq> (\<lambda>c. case c of Call _ (m#x#_) _ \<Rightarrow> x | _ \<Rightarrow> undefined) `  Map.ran (calls ctxt)"
            apply (auto simp add: callsWithOpArgsH_def)
            by (smt call.case image_iff list.simps(5) ranI)
          show " finite ((\<lambda>c. case c of Call _ (m#x#_) _ \<Rightarrow> x | _ \<Rightarrow> undefined) ` ran (calls ctxt))"
          proof
            have "finite (dom (calls ctxt))"
              sorry
            with finite_ran 
            show "finite (ran (calls ctxt))"
              by auto
          qed
        qed
      qed





      from \<open> example_chat.inv (invContext' Sa)\<close>
      have inv1_Sa: "inv1 (invContext' Sa)"
        and inv1a_Sa: "inv1a (invContext' Sa)"
        and inv1b_Sa: "inv1b (invContext' Sa)"
        and inv1c_Sa: "inv1c (invContext' Sa)"
        by (auto simp add: inv_def)

      paragraph \<open>Case get_message\<close>

      show "\<exists>bound. (checkCorrect2F ^^ bound) bot (progr, {}, Sa \<lparr>localState := localState Sa(i \<mapsto> lsInit\<lparr>ls_id := MessageId ia\<rparr>), currentProc := currentProc Sa(i \<mapsto> getMessageImpl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> (getMessage, [MessageId ia]))\<rparr>, i)"
        if c0: "procedures getMessage [MessageId ia] \<triangleq> (lsInit\<lparr>ls_id := MessageId ia\<rparr>, getMessageImpl)"
          and c1: "procName = getMessage"
          and c2: "args = [MessageId ia]"
          and c3: "impl = getMessageImpl"
          and c4: "initState = lsInit\<lparr>ls_id := MessageId ia\<rparr>"
        for  ia
 text \<open>We start by unrolling the implementation.\<close>
        apply (rule_tac x="10" in exI)
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  defer
   apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  defer
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)
  apply (rule checkCorrect2F_step, auto simp add: getMessageImpl_def lsInit_def split: localAction.splits option.splits)



        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)
        apply (rule checkCorrect2F_step, auto simp add: registerUserImpl_def lsInit_def split: localAction.splits option.splits)




end