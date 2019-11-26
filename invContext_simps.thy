theory invContext_simps
imports repliss_sem
begin


lemma invContext_unchanged_happensBefore:
  assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommitted"
  shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir 
    = invContextH co to ts hbOld cs ki io ir "
  using assms by (auto simp add: invContextH_def restrict_relation_def committedCallsH_def isCommittedH_def)

lemma invContext_unchanged_happensBefore2:
  assumes "co c = None"
  shows "invContextH co to ts (hbOld \<union> vis \<times> {c}) cs ki io ir  
    = invContextH co to ts hbOld cs ki io ir  "
  using assms by (auto simp add: invContextH_def restrict_relation_def committedCallsH_def isCommittedH_def)

lemma committedCallsH_notin:
  assumes "co c = None"
  shows "c \<notin> committedCallsH co ts"
  by (simp add: assms committedCallsH_def isCommittedH_def)

lemma committedCallsH_in:
  shows "(c \<in> committedCallsH co ts) \<longleftrightarrow> (case co c of None \<Rightarrow> False | Some t \<Rightarrow> ts t \<triangleq> Committed) "
  by (auto simp add: committedCallsH_def isCommittedH_def split: option.splits)



lemma committedCalls_unchanged_callOrigin:
  assumes a1: "ts t \<triangleq> Uncommitted"
    and a2: "co c = None"
  shows "committedCallsH (co(c \<mapsto> t)) ts = committedCallsH co ts"
  using a1 a2 by (auto simp add: committedCallsH_def isCommittedH_def)

lemma invContextH_map_update_all:
  assumes "co c = None" and "ts t \<triangleq> Uncommitted"
  shows "invContextH (co(c \<mapsto> t)) to ts hb cs ki io ir   =
       invContextH co to ts hb cs ki io ir  "
  using assms by (auto simp add: invContextH_def committedCallsH_notin committedCalls_unchanged_callOrigin)



lemma invContextH_update_calls:
  assumes "co c \<triangleq> t" and "ts t \<triangleq> Uncommitted"
  shows "invContextH co to ts hb (cs(c \<mapsto> newCall)) ki io ir   =
       invContextH co to ts hb cs ki io ir  "
  using assms by (auto simp add: invContextH_def committedCallsH_in)



lemma committedCallsH_update_uncommitted:
  assumes "ts t = None"
  shows "committedCallsH co (ts(t \<mapsto> Uncommitted))
     = committedCallsH co ts"
  using assms by (auto simp add: committedCallsH_def isCommittedH_def, force)


lemma invContextH_update_txstatus:
  assumes "ts t = None" 
  shows "invContextH co to (ts(t\<mapsto>Uncommitted)) hb cs ki io ir  =
       invContextH co to ts hb cs ki io ir "
  using assms by (auto simp add: invContextH_def restrict_map_def committedCallsH_update_uncommitted)

lemmas invContextH_simps = invContextH_update_calls invContextH_map_update_all invContextH_update_txstatus



end