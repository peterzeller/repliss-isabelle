section "Example: Computing Maximum with a forEach-Loop"

theory example_loop_max2
  imports 
    program_verification_tactics
    unique_ids
    program_proof_rules_loops
    app_verification_helpers
    unique_ids_loops
begin





datatype val =
    Nat (nat_value:nat)
  | Bool (bool_value:bool)
  | Undef
  | ListVal (list_value:"val list")

instance val :: countable
  by countable_datatype


instantiation val :: valueType begin
definition [simp]: "uniqueIds_val \<equiv> \<lambda>x::val. {}::uniqueId set"
definition [simp]: "default_val \<equiv> Undef"

instance by (standard, auto)
end

instantiation val :: natConvert begin
definition[simp]: "fromNat \<equiv> Nat"
instance proof (standard, simp)
  show "inj Nat"
    using injI by force
qed
end


type_synonym operation = unit

datatype proc =
    PMax "nat list"

definition "only_store_changed PS_old PS \<equiv> \<exists>store'. PS = PS_old\<lparr>ps_store := store'\<rparr>"

lemma show_only_store_changed:
  assumes "only_store_changed PS_old PS"
    and "PS' = PS\<lparr>ps_store := x\<rparr>"
  shows "only_store_changed PS_old PS'"
  using assms by (auto simp add: only_store_changed_def)

text_raw \<open>\DefineSnippet{loop_max_example_loop_inv}{\<close>
definition loop_inv :: "nat ref \<Rightarrow> nat list \<Rightarrow> (proc, val, unit) proof_state \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> nat list \<Rightarrow> (proc, val, unit) proof_state \<Rightarrow> bool" where
"loop_inv resR p_list PS_old Done res Todo  PS \<equiv>
 \<exists>re.
          (iref resR) \<in> dom (ps_store PS)
        \<and> re ::= s_read (ps_store PS) resR 
        \<and> (if Done = [] then re = 0 else re = Max (set Done))
        \<and> (only_store_changed PS_old PS)"
text_raw \<open>}%EndSnippet\<close>

text_raw \<open>\DefineSnippet{loop_max_example_impl}{\<close>
definition max_impl :: "nat list \<Rightarrow> (val,operation,val) io" where
"max_impl p_list \<equiv> 
   do {
      resR \<leftarrow> makeRef 0;
      forEach_a p_list (loop_inv resR p_list) (\<lambda>x. do {
        res \<leftarrow> read resR;
        resR :\<leftarrow> max x res
      });
      res \<leftarrow> read resR;
      return (Nat res)
}"
text_raw \<open>}%EndSnippet\<close>






instance proc :: countable
  by countable_datatype

instantiation proc :: valueType begin
definition [simp]: "uniqueIds_proc (proc::proc) \<equiv> ({} :: uniqueId set)"


definition [simp]: "default_proc \<equiv> PMax []"

instance by (standard, auto)
end

type_synonym localState = "val store  \<times> uniqueId set \<times> (val, operation, val) io"

definition procedures :: "proc \<Rightarrow> (localState \<times> (localState, operation, val) procedureImpl)" where
  "procedures invoc \<equiv>
  case invoc of
    PMax n \<Rightarrow> toImpl' invoc (max_impl n)
"

text_raw \<open>\DefineSnippet{loop_max_example_inv}{\<close>
definition inv1 where
"inv1 op res \<equiv> \<forall>i list r.
    op i \<triangleq> PMax list
  \<and> list \<noteq> []
  \<and> res i \<triangleq> r
  \<longrightarrow> (r = Nat (Max (set list)))
"
text_raw \<open>}%EndSnippet\<close>



definition inv :: "(proc, operation, val) invContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> 
    inv1 (invocOp ctxt) (invocRes ctxt) "

definition "crdtSpec c op r = False"

definition "crdtSpec' op Cs Ops  Hb C_out r = False"

lemma crdtSpec_rel: 
  shows "crdt_spec_rel crdtSpec crdtSpec'"
  by (rule show_crdt_spec_rel')
   (auto simp add: crdtSpec_def crdtSpec'_def)


definition progr :: "(proc, localState, operation, val) prog" where
  "progr \<equiv> \<lparr>
  querySpec = crdtSpec,
  procedure = procedures,
  invariant = inv
\<rparr>"

lemma [simp]: "procedure progr = procedures"
"querySpec progr = crdtSpec"
"invariant progr = inv"
  by (auto simp add: progr_def)


lemma progr_wf[simp]: "program_wellFormed progr"
proof (auto simp add: program_wellFormed_def)
  show "invocations_cannot_guess_ids progr"
  proof (rule invocations_cannot_guess_ids_io)

    show "impl = impl_language_loops.toImpl \<and> localKnown = uniqueIds proc"
      if c0: "procedure progr proc = ((store, localKnown, cmd), impl)"
      for  proc store localKnown cmd impl
      using that by (auto simp add: progr_def procedures_def split: proc.splits)
  qed

  show "queries_cannot_guess_ids crdtSpec"
  proof (auto simp add:  crdtSpec_def queries_cannot_guess_ids_def split: )

    show "\<And>opr. query_cannot_guess_ids (uniqueIds opr) (crdtSpec opr)"
      by (simp add: crdtSpec_def query_cannot_guess_ids_def2)
  qed
qed



theorem correct: "programCorrect progr"
proof M_show_programCorrect

  case invariant_initial_state
  show "invariant_all' (initialState progr)"
    by (simp add: inv_def initialState_def invContextH2_calls inv1_def  invContextH2_happensBefore invContextH2_i_invocOp progr_def)


  case (procedure_correct S i)



  show "procedureCorrect S i"
  proof (rule Initial_Label, rule show_initial_state_prop[OF procedure_correct], rule DC_final2, casify)
    case (show_P S_pre proc initState impl1)
    have "invocOp S i \<triangleq> proc"
      using show_P by auto
    have "invocRes S i = None"
      using show_P apply auto
      using state_wellFormed_invocation_before_result by blast

    have "uniqueIds proc \<subseteq> knownIds S"
      using show_P by auto


    note show_P[simp]

    show "procedureCorrect S i"
    proof (cases proc)
      case (PMax list)

      show "procedureCorrect S i"
      proof M_show_procedureCorrect
        case after_invocation
         show ?case
           using show_P.invariant_pre  show_P.i_fresh
           by (auto simp add:  inv_def inv1_def  invContextH2_simps wf_result_after_invocation)


      next
        case execution

        have ls: "localState S i \<triangleq> (Map.empty, {}, max_impl list)"
            by (auto simp add: PMax procedures_def )

        show "execution_s_correct S i"
          using ls procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound4)
          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add:  PMax procedures_def )

          

          show "invocOp S i \<triangleq> PMax list"
            using PMax \<open>invocOp S i \<triangleq> proc\<close> by blast

          note max_impl_def[simp]

          show "program_wellFormed (prog S)"
            by (auto simp add: show_P)

          from `invariant_all' S`
          show "invariant_all' S" .

          show "crdt_spec_rel (querySpec progr) crdtSpec'"
            using crdtSpec_rel progr_def by simp

          show "program_proof_rules_loops.execution_s_check (invariant progr) crdtSpec' \<lparr>
                  calls = s_calls, 
                  happensBefore = s_happensBefore, 
                  callOrigin = s_callOrigin, 
                  txOrigin = s_txOrigin, 
                  knownIds = s_knownIds, 
                  invocOp = (s_invocOp(i \<mapsto> PMax list)), 
                  invocRes = (s_invocRes(i := None)), 
                  ps_i = i, 
                  ps_generatedLocal = {}, 
                  ps_generatedLocalPrivate = {}, 
                  ps_localKnown = uniqueIds (PMax list), 
                  ps_vis = {}, 
                  ps_localCalls = [], 
                  ps_tx = None, 
                  ps_firstTx = True, 
                  ps_store = Map.empty,
                  ps_prog = progr
                  \<rparr> 
                  (max_impl list) 
                  (finalCheck (invariant progr) i)" \<comment> \<open>TODO finalCheck could be fixed for the initial P (as variant)\<close>
            if c0: "(\<And>tx. s_txOrigin tx \<noteq> Some i)"
              and inv: "invariant progr
                         \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
                            txOrigin = s_txOrigin, knownIds = s_knownIds,
                            invocOp = s_invocOp(i \<mapsto> PMax list), invocRes = s_invocRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_txOrigin s_knownIds s_invocOp s_invocRes
              (*
            Would also work with this one-liner:
            by (repliss_vcg_l asmUnfold: loop_inv_def, use inv in \<open> auto simp add:  inv_def inv1_def loop_inv_def Def_def only_store_changed_def s_read_def split: if_splits\<close>)
        *)
          proof (repliss_vcg_l asmUnfold: loop_inv_def,
              fuzzy_goal_cases loop_inv_start loop_body final)
            case loop_inv_start
            show ?case
              unfolding loop_inv_def
              by (auto simp add: s_read_def Def_def only_store_changed_def)
          next
            case (loop_body Done results t todo PSl re y)
            show ?case
            proof (auto simp add: loop_inv_def Def_def)
              show "s_read (ps_store PSl(0 \<mapsto> intoAny (max t (s_read (ps_store PSl) (Ref 0))))) (Ref 0) = Max (insert t (set Done))"
                using `re ::= s_read (ps_store PSl) (Ref 0)`
                  and `if Done = [] then re = 0 else re = Max (set Done)`
                by (auto simp add: s_read_def Def_def split: if_splits)

              from loop_body.only_store_changed
              show "only_store_changed
                 \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
                    txOrigin = s_txOrigin, knownIds = s_knownIds,
                    invocOp = s_invocOp(i \<mapsto> PMax (Done @ t # todo)), invocRes = s_invocRes(i := None),
                    ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = {}, ps_vis = {},
                    ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = [0 \<mapsto> intoAny 0], ps_prog = progr\<rparr>
                 (PSl\<lparr>ps_store := ps_store PSl(0 \<mapsto> intoAny (max t (s_read (ps_store PSl) (Ref 0))))\<rparr>)"
                by (auto simp add: only_store_changed_def proof_state_ext)
            qed
          next
            case (final results PSl re y)

            from final.only_store_changed
            have "invocOp PSl i \<triangleq> PMax list"
              by (auto simp add: only_store_changed_def)


            show "example_loop_max2.inv
            \<lparr>calls = calls PSl, happensBefore = happensBefore PSl,
               callOrigin = callOrigin PSl, txOrigin = txOrigin PSl,
               knownIds = knownIds PSl, invocOp = invocOp PSl,
               invocRes = invocRes PSl(i \<mapsto>
                 val.Nat (s_read (ps_store PSl) (Ref 0)))\<rparr>"
              unfolding inv_def inv1_def
            proof (auto simp add:  `invocOp PSl i \<triangleq> PMax list`)

              show "s_read (ps_store PSl) (Ref 0) = Max (set list)"
                if c0: "list \<noteq> []"
                using `re ::= s_read (ps_store PSl) (Ref 0)`
                  `if list = [] then re = 0 else re = Max (set list)`
                  that
                by (auto simp add: Def_def)

              from inv
              have "inv1 (s_invocOp(i \<mapsto> PMax list)) (s_invocRes(i := None))"
                by (auto simp add: inv_def)

              with final.only_store_changed
              have "inv1 (invocOp PSl) (invocRes PSl)"
                using only_store_changed_def by force


              show "r = val.Nat (Max (set list))"
                if c0: "ia \<noteq> i"
                  and c1: "invocOp PSl ia \<triangleq> PMax list"
                  and c2: "list \<noteq> []"
                  and c3: "invocRes PSl ia \<triangleq> r"
                for  ia list r
                by (meson \<open>inv1 (invocOp PSl) (invocRes PSl)\<close> c1 c2 c3 inv1_def)
            qed
          qed
        qed (auto)
      qed
    qed
  qed
qed


end
