theory examples
imports commutativity
begin

section "Examples"

text "Various examples to illustrate definitions."

\<comment> \<open>counts how many concurrent transactions are active\<close>
definition transactionsArePackedMeasure :: "('proc, 'op, 'any) trace \<Rightarrow> nat" where
  "transactionsArePackedMeasure tr \<equiv>
\<Sum>i\<in>{..<length tr}. card (sessionsInTransaction tr i - {get_invoc (tr!i)})  "


theorem not_packed_example2:
  assumes notPacked: "transactionsArePackedMeasure tr > 0"
  shows "\<exists>i s a.
    i<length tr
  \<and> tr!i = (s,a)
  \<and> sessionsInTransaction tr i - {s} \<noteq> {}" (is ?goal)
proof -
  from notPacked
  have "0 < (\<Sum>i<length tr. card (sessionsInTransaction tr i - {get_invoc (tr ! i)}))"
    by (auto simp add: transactionsArePackedMeasure_def)
  from this 
  obtain i 
    where a: "i < length tr" 
      and b: "card (sessionsInTransaction tr i - {get_invoc (tr ! i)}) > 0"
    by (meson lessThan_iff not_less sum_nonpos)

  from b 
  have "sessionsInTransaction tr i - {get_invoc (tr!i)} \<noteq> {}"
    by fastforce

  then show ?thesis
    by (metis a prod.collapse)
qed  



end
