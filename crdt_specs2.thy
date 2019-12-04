theory crdt_specs2
  imports crdt_specs
 "fuzzyrule.fuzzyrule"
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

definition 
"extract_op c_calls c \<equiv>  case c_calls c of Some (Call op r) \<Rightarrow> op"

(* TODO utils *)
lemma option_bind_def:
"(x \<bind> f) = (case x of None \<Rightarrow> None | Some a \<Rightarrow> f a)"
  by (metis bind.bind_lunit bind_eq_None_conv option.case_eq_if option.exhaust_sel)

definition is_reverse :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
"is_reverse f_in f_out \<equiv> 
  (\<forall>x y. ((f_in x) \<triangleq> y) \<longrightarrow> (f_out y = x))
  \<and> (\<forall>x.  (f_in (f_out x)) \<triangleq> x)"

lemma is_reverse_1:
  assumes "is_reverse f_in f_out"
    and "f_in x \<triangleq> y"
  shows "f_out y = x"
  by (meson assms is_reverse_def)


lemma is_reverse_2:
  assumes "is_reverse f_in f_out"
  shows "f_in (f_out x) \<triangleq> x"
  by (meson assms is_reverse_def)


(* TODO
so far the relation is only without nesting (for identity mapping.
Must add the mapping to both sides of the equation
left through transforming the context, right through C directly

best to prove equivalence for the map first and see what is required
 *)

(* TODO utils *)
definition map_chain ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" (infixr "\<ggreater>" 54) where
"(f \<ggreater> g) \<equiv> \<lambda>x. f x \<bind> g"

definition map_map ::  "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c" where
"(map_map f g) \<equiv> \<lambda>x. map_option g (f x)"



find_consts "('a \<rightharpoonup> 'b) \<Rightarrow> ('b \<rightharpoonup> 'c) \<Rightarrow> 'a \<rightharpoonup> 'c"

definition crdt_spec_rel :: "('opn, 'res) crdtSpec \<Rightarrow> ('op, 'opn, 'res) ccrdtSpec \<Rightarrow> bool" where
"crdt_spec_rel spec cspec \<equiv>
\<forall>C_in::'op \<rightharpoonup> 'opn. \<forall>C_out::'opn \<Rightarrow> 'op.
  is_reverse C_in C_out
  \<longrightarrow> 
  (\<forall>ctxt (outer_op::'op) (op::'opn) r Cs. 
   C_in outer_op \<triangleq> op
    \<longrightarrow>
       (spec op (sub_context C_in Cs ctxt) r
    \<longleftrightarrow> cspec (dom ((map_map (calls ctxt) call_operation) \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt))  (happensBefore ctxt) C_out op r))

"

lemmas use_crdt_spec_rel = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format]
lemmas use_crdt_spec_rel1 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD1]
lemmas use_crdt_spec_rel2 = crdt_spec_rel_def[unfolded atomize_eq, THEN iffD1, rule_format, THEN iffD2]


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

  show "lww_register_spec initial op (sub_context C_in Cs ctxt) r 
    = lww_register_spec' initial (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out op r"
    if c0: "is_reverse C_in C_out"
      and c1: "C_in outer_op \<triangleq> op"
    for  C_in C_out ctxt outer_op op r Cs
  proof -

(*
    have h1: "(latest_assignments' (dom (calls ctxt)) (extract_op (calls ctxt)) (happensBefore ctxt) id)
    = {(x,y). latestAssignments ctxt x \<triangleq> y}"
      apply (auto simp add: latest_assignments'_def extract_op_def latestAssignments_def latestAssignments_h_def split: call.splits)
         apply (auto split: option.splits call.splits registerOp.splits if_splits)
      done

    have h2: "(fst ` {(x, y). latestAssignments ctxt x \<triangleq> y}) =
              (dom (latestAssignments ctxt))"
      by (auto simp add: in_img_simp)


    have h3: "firstValue' initial {(x, y). latestAssignments ctxt x \<triangleq> y}
          = firstValue initial (latestAssignments ctxt)"
      apply (auto simp add: firstValue'_def firstValue_def h2)
      by (smt dom_def emptyE mem_Collect_eq option.exhaust option.sel some_well_order_includes_all some_well_order_is_wo_rel wo_rel.minim_in)
*)


    show "lww_register_spec initial op (sub_context C_in Cs ctxt) r =
    lww_register_spec' initial (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out op r"
      apply (auto simp add: lww_register_spec_def lww_register_spec'_def split: registerOp.splits)
      sorry
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


definition deleted_calls_dw' :: "callId set \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set" where
"deleted_calls_dw' vis op hb C k \<equiv> {c\<in>vis. \<exists>d\<in>vis. op d = C (DeleteKey k) \<and> (d,c)\<notin>hb}"

definition 
"restrict_calls vis op C k \<equiv>
{c\<in>vis. \<exists>u. op c = C (NestedOp k u) }"

definition map_spec' :: "
      (callId set  \<Rightarrow> (callId \<Rightarrow>'op) \<Rightarrow> callId rel \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set) 
    \<Rightarrow> (bool \<Rightarrow> 'r)
    \<Rightarrow> ('op, 'opn::crdt_op, 'r) ccrdtSpec
    \<Rightarrow> ('op, ('k, 'opn) mapOp, ('r::default)) ccrdtSpec" where
"map_spec' deleted_calls from_bool nestedSpec vis op hb C oper res \<equiv>
  case oper of
    DeleteKey k \<Rightarrow> res = default
  | KeyExists k \<Rightarrow> res = from_bool (\<exists>c\<in>vis. \<exists>upd_op. op c = C (NestedOp k upd_op) \<and> is_update upd_op \<and>  c \<notin> deleted_calls vis op hb C k)
  | NestedOp k nested_op \<Rightarrow>
     nestedSpec (restrict_calls vis op C k - deleted_calls vis op hb C k) op hb (\<lambda>x. C (NestedOp k x)) nested_op res
"
(* Needed for example: structs, set_rw, map_rw *)




lemma subcontext_calls:
  assumes in_out: "is_reverse C_in C_out"
  shows "(calls (sub_context C_in Cs ctxt) c \<triangleq> Call op r)
     \<longleftrightarrow> (calls ctxt c \<triangleq> Call (C_out op) r \<and> c\<in>Cs \<and> C_in (C_out op) \<triangleq> op)"

  by (auto simp add:   sub_context_def restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def ctxt_restrict_calls_def restrict_map_def option_bind_def split: option.splits call.splits,
      (simp add: in_out[simplified is_reverse_def])+)

lemma subcontext_of_subcontext_collapse:
"sub_context C_inA CsA (sub_context C_inB CsB ctxt)
= sub_context (\<lambda>x. C_inB x \<bind> C_inA) (CsA \<inter> CsB) ctxt"
  by (auto simp add: sub_context_def restrict_ctxt_op_def restrict_ctxt_def restrict_hb_def 
      fmap_map_values_def ctxt_restrict_calls_def restrict_map_def option_bind_def
      restrict_relation_def
      intro!: ext split: option.splits call.splits)


lemma 
  assumes "is_reverse C_in C_out"
  assumes "L = deleted_calls_dw (sub_context C_in Cs ctxt) k"
and "R = deleted_calls_dw' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "L = R"
  apply (auto simp add: deleted_calls_dw_def deleted_calls_dw'_def sub_context_def assms restrict_ctxt_op_def restrict_ctxt_def
      fmap_map_values_def option_bind_def ctxt_restrict_calls_def restrict_map_def
      restrict_relation_def extract_op_def split: option.splits call.splits if_splits)
      apply (rule_tac x=c' in bexI)
       apply auto
  apply (metis (no_types, lifting) assms(1) is_reverse_def option.exhaust)
  apply (meson call.exhaust option.exhaust)






lemma map_spec_rel:
  fixes nestedSpec :: "('opn::crdt_op, 'res::default) crdtSpec"
    and nestedSpec' :: "('op, 'opn, 'res) ccrdtSpec"
    and deletedCalls :: "(('k, 'opn) mapOp, 'res) operationContext \<Rightarrow> 'k \<Rightarrow> callId set"
    and deletedCalls' :: "callId set \<Rightarrow> (callId \<Rightarrow> 'op) \<Rightarrow> (callId \<times> callId) set \<Rightarrow> (('k, 'opn) mapOp \<Rightarrow> 'op) \<Rightarrow> 'k \<Rightarrow> callId set"
  assumes nested_rel: "crdt_spec_rel nestedSpec nestedSpec'"
and deletedCalls_rel: 
    "\<And>ctxt C_in C_out Cs k. deleted_calls (sub_context C_in Cs ctxt) k
        = deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
shows "crdt_spec_rel (map_spec deleted_calls from_bool nestedSpec) (map_spec' deleted_calls' from_bool nestedSpec') "
  unfolding crdt_spec_rel_def
proof (intro allI impI)

  show "map_spec deleted_calls from_bool nestedSpec op (sub_context C_in Cs ctxt) r 
     = map_spec' deleted_calls' from_bool nestedSpec' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out op r"
      (is "?l = ?r")
    if is_rev: "is_reverse C_in C_out"
      and in_out: "C_in outer_op \<triangleq> op"
    for  C_in C_out ctxt outer_op op r Cs
  proof -


    show "?l = ?r"
    proof (cases op)
      case (NestedOp k nestedOp)


      have h1: "((restrict_calls (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) C_out k)
                   - deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k) = 
            {c \<in> dom (calls ctxt). c \<in> Cs \<and> (\<exists>u. extract_op (calls ctxt) c = C_out (NestedOp k u)) 
               \<and> c \<notin> deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k}
              " 
         by (auto simp add: restrict_calls_def)

       have h2: "nestedSpec nestedOp
         (sub_context (nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k) (sub_context C_in Cs ctxt))
         r 
          = ???"
         thm use_crdt_spec_rel[OF nested_rel, 
             where op=nestedOp 
               and r=r
               and C_in="\<lambda>x. C_in x \<bind> nested_op_on_key k"
               and C_out="\<lambda>x. C_out (NestedOp k x)"]
         sorry


      show ?thesis 
      proof (simp add: NestedOp h1 map_spec_def map_spec'_def subcontext_calls[OF is_rev] deletedCalls_rel subcontext_of_subcontext_collapse)

        show "nestedSpec nestedOp (sub_context (\<lambda>x. C_in x \<bind> nested_op_on_key k) (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs) ctxt) r =
            nestedSpec'
             (restrict_calls (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) C_out k -
              deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
             (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) nestedOp r"
        proof (subst use_crdt_spec_rel[OF nested_rel])        

          show is_rev_combined: "is_reverse (\<lambda>x. C_in x \<bind> nested_op_on_key k) (\<lambda>x. C_out (NestedOp k x))"
            by (auto simp add: is_reverse_def option_bind_def nested_op_on_key_def 
                is_reverse_1[OF is_rev] is_reverse_2[OF is_rev] split: option.splits mapOp.splits)

          show "(C_in (C_out (NestedOp k nestedOp)) \<bind> nested_op_on_key k) \<triangleq> nestedOp"
            using is_rev_combined is_reverse_def by fastforce

          have h1: "deleted_calls (sub_context C_in Cs ctxt) k
              = deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k"
            by (rule deletedCalls_rel)

          have h3: "(dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter>
                 (- deleted_calls' (dom (calls ctxt) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k \<inter> Cs))
              = (restrict_calls (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) C_out k -
                    deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)"
            apply (auto simp add: 
                  restrict_calls_def extract_op_def nested_op_on_key_def
                  map_chain_def option_bind_def map_map_def split: option.splits call.splits mapOp.splits if_splits)
            using is_rev is_reverse_1 apply fastforce



            sorry

          show "nestedSpec'
               (dom (map_map (calls ctxt) call_operation \<ggreater> (\<lambda>x. C_in x \<bind> nested_op_on_key k)) \<inter>
                (- deleted_calls (sub_context C_in Cs ctxt) k \<inter> Cs))
               (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) nestedOp r =
              nestedSpec'
               (restrict_calls (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) C_out k -
                deleted_calls' (dom (map_map (calls ctxt) call_operation \<ggreater> C_in) \<inter> Cs) (extract_op (calls ctxt)) (happensBefore ctxt) C_out k)
               (extract_op (calls ctxt)) (happensBefore ctxt) (\<lambda>x. C_out (NestedOp k x)) nestedOp r"
            apply (simp add: h1 restrict_calls_def)

          have "nestedSpec' (dom (calls ?ctxt) \<inter> ?Cs) (extract_op (calls ?ctxt)) (happensBefore ?ctxt) ?C_out ?op ?r"


          thm use_crdt_spec_rel1[OF nested_rel]
         apply (fuzzy_rule(noabs) use_crdt_spec_rel1)

        sorry
    next
      case (KeyExists k)
      then show ?thesis 
        apply (auto simp add: map_spec_def map_spec'_def subcontext_calls[OF is_rev] deletedCalls_rel intro!: arg_cong[where f=from_bool])
           apply (auto simp add:  extract_op_def split: option.splits call.splits)
           apply (metis (no_types, lifting) Int_iff call.inject deletedCalls_rel domI domIff option.sel)
          apply (meson deletedCalls_rel is_rev is_reverse_2)
         apply (meson deletedCalls_rel is_rev is_reverse_2)
        by (metis (no_types, lifting) Int_iff call.inject deletedCalls_rel domI domIff option.sel)
    next
      case (DeleteKey k)
      then show ?thesis
        by (auto simp add: map_spec_def map_spec'_def)
    qed


  qed

end