theory example_chat
  imports 
    program_verification_tactics
    impl_language
    crdt_specs
    unique_ids
    program_proof_rules
begin


section "Example: Chat application"



datatype val =
    String string
  | UserId int
  | ChatId int
  | MessageId int
  | Bool bool
  | Undef
  | ListVal "val list"
  | Found val val
  | NotFound

instance val :: countable
  by countable_datatype

fun uniqueIds_val_r  where 
  "uniqueIds_val_r (UserId i) = {}" \<comment> \<open>These are not considered Ids as they are not generated by this part of the app.\<close>
| "uniqueIds_val_r (MessageId i) = {to_nat i}"
| "uniqueIds_val_r (ListVal vs) = \<Union>(set (map uniqueIds_val_r vs))"
| "uniqueIds_val_r (Found x y) = uniqueIds_val_r x \<union> uniqueIds_val_r y"
| "uniqueIds_val_r _ = {}"

instantiation val :: valueType begin
definition [simp]: "uniqueIds_val \<equiv> uniqueIds_val_r"
definition [simp]: "default_val \<equiv> Undef"

instance by (standard, auto)
end

fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"


datatype messageDataOp =
    Author "val registerOp"
  | Content "val registerOp"


instance messageDataOp :: countable
  by countable_datatype
instantiation messageDataOp :: crdt_op begin
definition "uniqueIds_messageDataOp x \<equiv> 
  case x of 
     Author x \<Rightarrow> uniqueIds x
   | Content x \<Rightarrow> uniqueIds x"

lemma [simp]: "uniqueIds (Author x) = uniqueIds x"
  "uniqueIds (Content x) = uniqueIds x"
  by (auto simp add: uniqueIds_messageDataOp_def)

definition [simp]: "default_messageDataOp = Author default"

definition "is_update_messageDataOp x \<equiv> case x of Author x \<Rightarrow> is_update x | Content x \<Rightarrow> is_update x"

instance by (standard, auto)
end

definition "isMessageId x \<equiv> case x of MessageId _ \<Rightarrow> True | _ \<Rightarrow> False"

datatype operation =
      Chat "val setOp"
    | Message "(val, messageDataOp) mapOp"


definition sendMessage_impl :: "val \<Rightarrow> val \<Rightarrow> (val,operation,val) io" where
  "sendMessage_impl from content \<equiv>  do {
  m \<leftarrow> newId isMessageId;
  atomic (do {
    call (Message (NestedOp m (Author (Assign from))));
    call (Message (NestedOp m (Content (Assign content))));
    call (Chat (Add m))
  });
  return m
}"


definition editMessage_impl :: "val \<Rightarrow> val \<Rightarrow> (val,operation,val) io" where
  "editMessage_impl m newContent \<equiv>  do {
  atomic (do {
    call (Message (NestedOp m (Content (Assign newContent))))
  });
  return Undef
}"

definition deleteMessage_impl :: "val \<Rightarrow> (val,operation,val) io" where
  "deleteMessage_impl m \<equiv>  do {
  atomic (do {
    exists \<leftarrow> call (Message (KeyExists m));
    if exists = Bool True then do {
      call (Chat (Remove m));
      call (Message (DeleteKey m))
    } else
      skip
  });
  return Undef
}"


definition getMessage_impl :: "val \<Rightarrow> (val,operation,val) io" where
  "getMessage_impl m \<equiv>  do {
  atomic (do {
    exists \<leftarrow> call (Message (KeyExists m));
    if exists = Bool True then do {
      author \<leftarrow> call (Message (NestedOp m (Author Read)));
      content \<leftarrow> call (Message (NestedOp m (Content Read)));
      return (Found author content)
    } else do {
      return NotFound
    }
  })
}"

datatype proc =
    SendMessage string string
  | EditMessage int string
  | DeleteMessage int
  | GetMessage int

instance proc :: countable
  by countable_datatype

instantiation proc :: valueType begin
definition "uniqueIds_proc proc \<equiv> 
  case proc of 
     SendMessage a c \<Rightarrow> {}
   | EditMessage m s  \<Rightarrow> {to_nat (MessageId m)}
   | DeleteMessage m  \<Rightarrow> {to_nat (MessageId m)}
   | GetMessage m  \<Rightarrow> {to_nat (MessageId m)}"

lemma [simp]:
  "uniqueIds (SendMessage a c) = {}"
  "uniqueIds (EditMessage m s) = {to_nat (MessageId m)}"
  "uniqueIds (DeleteMessage m) = {to_nat (MessageId m)}"
  "uniqueIds (GetMessage m) = {to_nat (MessageId m)}"
  by (auto simp add: uniqueIds_proc_def)

definition [simp]: "default_proc \<equiv> SendMessage [] []"

instance by (standard, auto)
end

abbreviation  toImpl2 where
 "toImpl2 (x :: (val,operation,val) io) \<equiv> (x , toImpl)"

definition procedures :: "proc \<Rightarrow> ((val, operation, val) io \<times> ((val, operation, val) io, operation, val) procedureImpl)" where
  "procedures invoc \<equiv>
  case invoc of
    SendMessage author content \<Rightarrow> toImpl2 (sendMessage_impl (String author) (String content))
  | EditMessage m newContent \<Rightarrow> toImpl2 (editMessage_impl (MessageId m) (String newContent))
  | DeleteMessage m \<Rightarrow>  toImpl2 (deleteMessage_impl (MessageId m))
  | GetMessage m  \<Rightarrow>  toImpl2 (getMessage_impl (MessageId m))
"


(*
// getMessage returns correct authors
invariant (forall g: invocationId, m: MessageId, author: UserId, content: String ::
     g.info == getMessage(m)
  && g.result == getMessage_res(found(author, content))
  ==> (exists s: invocationId, content2: String :: s.info == sendMessage(author, content2)))
*)

definition inv1 where
"inv1 op res \<equiv> \<forall>g m author content.
    op g \<triangleq> GetMessage m
  \<and> res g \<triangleq> Found (String author) content
  \<longrightarrow> (\<exists>s content2. op s \<triangleq> SendMessage author content2)
"
    


(*
// additional invariants:
// for every author-assignment there is a corresponding invocation of sendMessage
invariant forall c: callId, m: MessageId, u: UserId ::
    c.op == message_author_assign(m, u)
    ==> (exists i: invocationId, s: String ::
            i.info == sendMessage(u, s))
*)

definition inv2 where
"inv2 op cop \<equiv> \<forall>c m u.
  cop c \<triangleq> Message (NestedOp m (Author (Assign (String u))))
  \<longrightarrow> (\<exists>i s. op i \<triangleq> SendMessage u s) "


(*
// if there is an assignment of the content field, there also is one for the author field that happened before:
invariant forall c1: callId, m: MessageId, s: String ::
    c1.op == message_content_assign(m, s)
    ==> (exists c2: callId, u: UserId ::
            c2.op == message_author_assign(m, u)
            && c2 happened before c1)
*)

definition inv3 where
"inv3 cop hb \<equiv> \<forall>c1 m s.
    cop c1 \<triangleq> Message (NestedOp m (Content (Assign s)))
    \<longrightarrow> (\<exists>c2 u. 
           cop c2 \<triangleq> Message (NestedOp m (Author (Assign u)))
           \<and> (c2, c1)\<in>hb) " 


(*
// there is no update after a delete
invariant !(exists write: callId, delete: callId, m: MessageId ::
       ((exists u: UserId ::  write.op == message_author_assign(m, u))
        || (exists s: String ::  write.op == message_content_assign(m, s)))
    && delete.op == message_delete(m)
    && delete happened before write)
*)


definition inv4 where
"inv4 cop hb \<equiv>
  \<nexists>write delete m no.
   cop write \<triangleq> Message (NestedOp m no)
   \<and> is_update no
   \<and> cop delete \<triangleq> Message (DeleteKey m)
   \<and> (delete,write)\<in>hb"



end