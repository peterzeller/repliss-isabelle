theory crdt_specs2
  imports crdt_specs
begin

section "CRDT Specifications Part 2"

text "The previous CRDT are not nice to work with when composed.
The problem is, that the specifications for maps and structs transform the context
passed to embedded CRDTs.
During this transformation the reverse direction is lost, so it is hard to reconstruct the original
calls from the calls in an embedded context.
Therefore, we now use a different composition technique, where the mapping is explicitly passed down
into nested CRDTs."

type_synonym ('op, 'opn, 'res) ccrdtSpec = 
        "callId set                  \<comment> \<open>visible calls\<close>
      \<Rightarrow> (callId \<Rightarrow>'op)              \<comment> \<open>call information\<close> 
      \<Rightarrow> callId rel                  \<comment> \<open>happens-before\<close>
      \<Rightarrow> ('opn \<Rightarrow> 'op)               \<comment> \<open>mapping back\<close>
      \<Rightarrow> 'op 
      \<Rightarrow> 'res
      \<Rightarrow> bool"

text "There is a mapping between the composable CRDT specs above and the original specifications:"

(* TODO *)


subsection "Register"

definition 
"latest_assignments' vis op hb C \<equiv> 
   {(c,v). c\<in>vis \<and> op c = C (Assign v) \<and> (\<nexists>c' v'. c'\<in>vis \<and> op c' = C (Assign v') \<and> (c,c')\<in>hb)}"

definition
"latest_values' vis op hb C \<equiv> snd ` (latest_assignments' vis op hb C)"

definition
"register_spec' initial vis op hb C oper res \<equiv>
  case oper of
    Assign _ \<Rightarrow> res = default
  | Read \<Rightarrow>
      if latest_values' vis op hb C = {} then res = initial else res \<in> latest_values' vis op hb C"


definition firstValue' :: "'a \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> 'a" where
"firstValue' d m \<equiv> if m = {} then d else 
  let maxK = wo_rel.minim some_well_order (fst ` m) in
  wo_rel.minim some_well_order {y. (maxK,y)\<in>m}
  "


definition 
"lww_register_spec' initial vis op hb C oper res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> res = firstValue' initial (latest_values' vis op hb C)"


(* Needed for example: structs, set_rw, map_rw *)

end