theory example_chat
  imports 
    program_verification_tactics
    impl_language
    crdt_specs
    unique_ids
    program_proof_rules
begin






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

instance val :: countable
  by countable_datatype

fun uniqueIds_val_r  where 
  "uniqueIds_val_r (UserId i) = {to_nat i}"
| "uniqueIds_val_r (MessageId i) = {to_nat i}"
| "uniqueIds_val_r (ListVal vs) = \<Union>(set (map uniqueIds_val_r vs))"
| "uniqueIds_val_r (Pair x y) = uniqueIds_val_r x \<union> uniqueIds_val_r y"
| "uniqueIds_val_r _ = {}"

instantiation val :: valueType begin
definition [simp]: "uniqueIds_val \<equiv> uniqueIds_val_r"
definition [simp]: "default_val \<equiv> Undef"

instance by standard
end

fun stringval where
  "stringval (String s) = s"
| "stringval _ = ''''"


datatype userDataOp =
    Author "val registerOp"
  | Content "val registerOp"







end