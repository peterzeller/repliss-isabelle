theory unique_ids_procedure_check
  imports unique_ids
begin

inductive procedure_cannot_guess_ids :: "uniqueId set \<Rightarrow> 'ls \<Rightarrow> ('ls, 'operation::valueType, 'any::valueType) procedureImpl \<Rightarrow> bool"  where
  pcgi_local:  "\<lbrakk>impl ls = LocalStep ok ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_beginAtomic: "\<lbrakk>impl ls = BeginAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_endAtomic:"\<lbrakk>impl ls = EndAtomic ls'; procedure_cannot_guess_ids uids ls' impl\<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_newId:"\<lbrakk>impl ls = NewId f; \<And>uid ls'. f uid \<triangleq> ls' \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds uid) ls' impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_dbop: "\<lbrakk>impl ls = DbOperation opr f;  uniqueIds opr \<subseteq> uids; 
    \<And>res. procedure_cannot_guess_ids (uids \<union> uniqueIds res) (f res) impl
    \<rbrakk> \<Longrightarrow>  procedure_cannot_guess_ids uids ls impl"
| pcgi_return: "\<lbrakk>impl ls = Return r; uniqueIds r \<subseteq> uids\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls impl"


lemma pcgi_local_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = LocalStep ok ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_beginAtomic_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = BeginAtomic ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_endAtomic_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = EndAtomic ls'\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids uids ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_newId_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = NewId f\<rbrakk> \<Longrightarrow> f uid \<triangleq> ls' \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds uid) ls' impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_dbop_case1:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = DbOperation opr f\<rbrakk> \<Longrightarrow> uniqueIds opr \<subseteq> uids"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_dbop_case2:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = DbOperation opr f\<rbrakk> \<Longrightarrow> procedure_cannot_guess_ids (uids \<union> uniqueIds res) (f res) impl"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)
lemma pcgi_return_case:"\<lbrakk>procedure_cannot_guess_ids uids ls impl; impl ls = Return r\<rbrakk> \<Longrightarrow> uniqueIds r \<subseteq> uids"
  by (subst(asm) procedure_cannot_guess_ids.simps, auto)






definition procedures_cannot_guess_ids :: "('proc::valueType \<Rightarrow> ('ls \<times> ('ls, 'operation::valueType, 'any::valueType) procedureImpl)) \<Rightarrow> bool" where
  "procedures_cannot_guess_ids proc = 
(\<forall>p ls impl uids. proc p = (ls, impl) \<longrightarrow>  procedure_cannot_guess_ids (uids\<union>uniqueIds p) ls impl)"

lemmas show_procedures_cannot_guess_ids = procedures_cannot_guess_ids_def[THEN iffD1, rule_format]

end