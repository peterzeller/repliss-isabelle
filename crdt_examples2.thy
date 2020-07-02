theory crdt_examples2
  imports crdt_specs2
    app_verification_helpers
begin

section "Difference Between CRDT Specifications"


subsection \<open>Struct example\<close>

text \<open>This is a struct with two fields: a counter and a set.\<close>

datatype val =
    I int
  | Bool bool
  | String string
  | ListVal "val list"
  | Undef

instance val :: countable
  by countable_datatype

definition [simp]: "uniqueIds_val_r (x::val) = ({}::uniqueId set)" 

instantiation val :: valueType begin
definition [simp]: "uniqueIds_val \<equiv> uniqueIds_val_r"
definition [simp]: "default_val \<equiv> Undef"

instance by (standard, auto)
end

instantiation val :: from_bool begin
definition [simp]: "from_bool_val \<equiv> Bool"

instance by (standard, auto)
end

instantiation val :: from_int begin
definition [simp]: "from_int_val \<equiv> I"

instance by (standard, auto)
end


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

lemma is_update_messageDataOp_simp[simp]:
  "is_update (Author x) = is_update x"
  "is_update (Content y) = is_update y"
  by (auto simp add: is_update_messageDataOp_def)

instance by (standard, auto)
end


datatype operation =
      Chat "val setOp"
    | Message "(val, messageDataOp) mapOp"


instance operation :: countable
  by countable_datatype
instantiation operation :: crdt_op begin
definition "uniqueIds_operation x \<equiv> 
  case x of 
     Chat x \<Rightarrow> uniqueIds x
   | Message x \<Rightarrow> uniqueIds x"

lemma [simp]: "uniqueIds (Chat x) = uniqueIds x"
  "uniqueIds (Message y) = uniqueIds y"
  by (auto simp add: uniqueIds_operation_def)

definition [simp]: "default_operation = Chat default"

definition "is_update_operation x \<equiv> case x of Chat x \<Rightarrow> is_update x | Message x \<Rightarrow> is_update x"

instance by (standard, auto)
end

definition messageStruct :: "(messageDataOp, val) crdtSpec" where
  "messageStruct \<equiv> 
      struct_field Author (register_spec Undef)  
  .\<or>. struct_field Content (register_spec Undef) 
" 

definition crdtSpec :: "(operation, val) crdtSpec" where
"crdtSpec \<equiv> 
      struct_field Message (map_sdw_spec messageStruct) 
  .\<or>. struct_field Chat set_rw_spec 
"


definition messageStruct'  :: "('a, messageDataOp, val) ccrdtSpec"  where
  "messageStruct' \<equiv> 
       struct_field' Author (register_spec' Undef) 
  .\<or>.. struct_field' Content (register_spec' Undef) 
" 

definition crdtSpec' :: "(operation, operation, val) ccrdtSpec" where
"crdtSpec' \<equiv> 
        struct_field' Message (map_sdw_spec' messageStruct') 
  .\<or>.. struct_field'  Chat set_rw_spec' 
"

lemma inj_fields[simp]: "inj Chat"
  "inj Message"
  "inj Author"
  "inj Content"
  by (auto simp add: inj_def)

text \<open>\DefineSnippet{first_order_spec_example_term}{
@{term "crdtSpec' (Message (NestedOp msg (Author Read))) vis op hb id (String author)"}
}%EndSnippet\<close>

lemma
  assumes "crdtSpec' (Message (NestedOp msg (Author Read))) vis op hb id (String author)"
  shows "???"
proof -
  from assms
  text_raw \<open>\DefineSnippet{first_order_spec_example1}{\<close>
  obtain a
    where "a \<in> vis"
      and  "\<forall>d\<in>vis. op d = Message (DeleteKey msg) \<longrightarrow> (d, a) \<in> hb"
      and  "op a = Message (NestedOp msg (Author (Assign (String author))))"
      and  "\<forall>c'. c' \<in> vis \<longrightarrow> 
             (\<exists>d\<in>vis. op d = Message (DeleteKey msg) \<and> (d, c') \<notin> hb) 
           \<or> (\<forall>v'. op c' \<noteq> Message (NestedOp msg (Author (Assign v'))))
           \<or> (a, c') \<notin> hb"
    text_raw \<open>}%EndSnippet\<close>

    apply (auto simp add: crdtSpec'_def map_sdw_spec'_def map_spec'_def messageStruct'_def register_spec'_def)
    apply (auto simp add: is_from_not_initial latest_values'_def latest_assignments'_def)
    apply (auto simp add: restrict_calls_def deleted_calls_sdw'_def)
    done
  oops

lemma   
  assumes "crdtSpec (Message (NestedOp msg (Author Read))) \<lparr>calls = cs, happensBefore = hb\<rparr> (String author)"
  shows ???
proof -
text_raw \<open>\DefineSnippet{first_order_spec_example2}{\<close>
  (*<*)define sub_ctxt where (*>*)
  "sub_ctxt \<equiv> 
      (restrict_ctxt_op (select_field Author)
               (sub_context (nested_op_on_key msg)
                 (- deleted_calls_sdw (restrict_ctxt_op (select_field Message) 
                                            \<lparr>calls = cs, happensBefore = hb\<rparr>) msg)
                 (restrict_ctxt_op (select_field Message) 
                                            \<lparr>calls = cs, happensBefore = hb\<rparr>)))"

  (*<*)from assms(*>*)
  obtain c where "Op sub_ctxt c \<triangleq> Assign (String author)"
    and "\<forall>c'. (\<forall>v'. Op sub_ctxt c' \<noteq> Some (Assign v')) 
        \<or> (c, c') \<notin> happensBefore sub_ctxt"
text_raw \<open>}%EndSnippet\<close>
    apply (auto simp add: crdtSpec_def struct_field_def select_field_def)
    apply (auto simp add: map_sdw_spec_def map_spec_def messageStruct_def 
        struct_field_def select_field_def)
    apply (auto simp add: register_spec_def split: if_splits)
    apply (thin_tac "\<not>_")
    apply (thin_tac "x \<in> _")
    apply (auto simp add: latestValues_def2 )
    apply (auto simp add: Op_restrict_ctxt_op_eq sub_ctxt_def)
    done

  have "(x,y) \<in> happensBefore sub_ctxt \<longleftrightarrow> ???"
    for x y
    apply (auto simp add: sub_ctxt_def happensBefore_restrict_ctxt_op2)
    apply (auto simp add: happens_before_sub_context happensBefore_restrict_ctxt_op2 calls_sub_context calls_restrict_ctxt_op2)
    oops

end
