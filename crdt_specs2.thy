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
      \<Rightarrow> 'opn 
      \<Rightarrow> 'res
      \<Rightarrow> bool"

text "There is a mapping between the composable CRDT specs above and the original specifications:"

(* TODO
so far the relation is only without nesting (for identity mapping.
Must add the mapping to both sides of the equation
left through transforming the context, right through C directly

best to prove equivalence for the map first and see what is required
 *)
definition crdt_spec_rel :: "('op, 'res) crdtSpec \<Rightarrow> ('op, 'op, 'res) ccrdtSpec \<Rightarrow> bool" where
"crdt_spec_rel spec cspec \<equiv>
(\<forall>ctxt op r. 
spec op ctxt r \<longleftrightarrow> cspec (dom (calls ctxt)) (\<lambda>c. case calls ctxt c of Some (Call op r) \<Rightarrow> op) (happensBefore ctxt) id op r)

"


subsection "Register"

definition latest_assignments' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> ('v registerOp \<Rightarrow> 'op) \<Rightarrow> (callId \<times> 'v) set"  where
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


definition lww_register_spec' :: "('v::default) \<Rightarrow> ('op, 'v registerOp, 'v) ccrdtSpec" where
"lww_register_spec' initial vis op hb C oper res \<equiv> 
  case oper of
    Assign x \<Rightarrow> res = default
  | Read \<Rightarrow> res = firstValue' initial (latest_assignments' vis op hb C)"


lemma 
"crdt_spec_rel (lww_register_spec initial) (lww_register_spec' initial) "
  unfolding crdt_spec_rel_def
proof (intro allI impI)

  show "lww_register_spec initial op ctxt r =
       lww_register_spec' initial (dom (calls ctxt)) (\<lambda>c. case calls ctxt c of None \<Rightarrow> ??? | Some (Call op r) \<Rightarrow> op) (happensBefore ctxt)
        id op r" (is ?g)
    for ctxt op r
  proof -

    have h1: "(latest_assignments' (dom (calls ctxt)) (\<lambda>c. case calls ctxt c of None \<Rightarrow> ??? | Some (Call op r) \<Rightarrow> op) (happensBefore ctxt) id)
    = {(x,y). latestAssignments ctxt x \<triangleq> y}"
      apply (auto simp add: latest_assignments'_def latestAssignments_def latestAssignments_h_def split: call.splits)
         apply (auto split: option.splits call.splits registerOp.splits if_splits)
      done

    have h2: "(fst ` {(x, y). latestAssignments ctxt x \<triangleq> y}) =
              (dom (latestAssignments ctxt))"
      by (auto simp add: in_img_simp)


    have h3: "firstValue' initial {(x, y). latestAssignments ctxt x \<triangleq> y}
          = firstValue initial (latestAssignments ctxt)"
      apply (auto simp add: firstValue'_def firstValue_def h2)
      by (smt dom_def emptyE mem_Collect_eq option.exhaust option.sel some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)



    show ?g
      apply (auto simp add: lww_register_spec_def lww_register_spec'_def split: registerOp.splits)
      apply (auto simp add: h1 h3)
      done
  qed
qed




subsection "Sets"

definition set_rw_spec' where
"set_rw_spec' from_bool vis op hb C oper res \<equiv> 
  case oper of
    Add _ => res = default
  | Remove _ \<Rightarrow> res = default
  | Contains v \<Rightarrow> res = from_bool 
        (\<exists>a\<in>vis. a \<triangleq> Add v 
           \<and> (\<forall>r\<in>vis. op r \<triangleq> Remove v
                 \<longrightarrow> (\<exists>a'\<in>vis. op a' \<triangleq> Add v \<and> (r,a')\<in>hb)))"



subsection "Maps"


definition
"deleted_calls_dw' vis op hb C k \<equiv> {c. \<exists>d\<in>vis. op d \<triangleq> C (DeleteKey k) \<and> (d,c)\<notin>hb}"

definition 
"restrict_calls vis op C k \<equiv>
{c\<in>vis. \<exists>u. op c = C (NestedOp k u) }"

definition
"map_spec' deleted_calls from_bool nestedSpec vis op hb C oper res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c\<in>vis. \<exists>upd_op. op c \<triangleq> NestedOp k upd_op \<and> is_update upd_op \<and>  c \<notin> deleted_calls vis op hb C k)
  | NestedOp k nested_op \<Rightarrow>
     nestedSpec (restrict_calls vis op C k - deleted_calls vis op hb C k) op hb (\<lambda>x. C (NestedOp k x)) nested_op res
"
(* Needed for example: structs, set_rw, map_rw *)

end