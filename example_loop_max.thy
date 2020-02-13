section "Example: Computing Maximum with a Loop"

theory example_loop_max
  imports 
    program_verification_tactics
    crdt_specs2
    unique_ids
    program_proof_rules_loops
    app_verification_helpers
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

definition loop_inv :: "nat list ref \<Rightarrow> nat ref \<Rightarrow> nat list \<Rightarrow> (proc, val, unit) proof_state \<Rightarrow> (proc, val, unit) proof_state \<Rightarrow> bool" where
"loop_inv listR resR p_list PS_old PS \<equiv>
 \<exists>li re li_done.
          iref resR \<noteq> iref listR
        \<and> (iref listR) \<in> dom (ps_store PS)
        \<and> (iref resR) \<in> dom (ps_store PS)
        \<and> li ::= s_read (ps_store PS) listR 
        \<and> re ::= s_read (ps_store PS) resR 
        \<and> p_list ::= li_done @ li
        \<and> (if li_done = [] then re = 0 else re = Max (set li_done))
        \<and> (only_store_changed PS_old PS)"

definition max_impl :: "nat list \<Rightarrow> (val,operation,val) io" where
"max_impl p_list \<equiv> 
   do {
      listR \<leftarrow> makeRef p_list;
      resR \<leftarrow> makeRef 0;
      loop_a (loop_inv listR resR p_list) (do {
        list \<leftarrow> read listR;
        res \<leftarrow> read resR;
        if list = [] then 
          return True
        else do {
          let x = hd list;
          listR :\<leftarrow> tl list;
          resR :\<leftarrow> max x res;
          return False
        }
      });
      res \<leftarrow> read resR;
      return (Nat res)
   }"





instance proc :: countable
  by countable_datatype

instantiation proc :: valueType begin
definition [simp]: "uniqueIds_proc (proc::proc) \<equiv> ({} :: uniqueId set)"


definition [simp]: "default_proc \<equiv> PMax []"

instance by (standard, auto)
end

abbreviation  toImpl2 where
 "toImpl2 (x :: (val,operation,val) io) \<equiv> ((Map.empty, x) , toImpl)"

type_synonym localState = "val store \<times> (val, operation, val) io"

definition procedures :: "proc \<Rightarrow> (localState \<times> (localState, operation, val) procedureImpl)" where
  "procedures invoc \<equiv>
  case invoc of
    PMax n \<Rightarrow> toImpl2 (max_impl n)
"


definition inv1 where
"inv1 op res \<equiv> \<forall>i list r.
    op i \<triangleq> PMax list
  \<and> list \<noteq> []
  \<and> res i \<triangleq> r
  \<longrightarrow> (r = Nat (Max (set list)))
"



definition inv :: "(proc, operation, val) invariantContext \<Rightarrow> bool" where
  "inv ctxt \<equiv> 
    inv1 (invocationOp ctxt) (invocationRes ctxt) "

definition "crdtSpec c op r = False"

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

instantiation unit :: valueType begin
definition [simp]: "uniqueIds_unit (x::unit) = ({}::uniqueId set)"
instance by standard auto
end

lemma progr_wf[simp]: "program_wellFormed progr"
proof (auto simp add: program_wellFormed_def)
  show "procedures_cannot_guess_ids procedures"
  proof (auto simp add: procedures_cannot_guess_ids_def procedures_def uniqueIds_proc_def split: proc.splits)

    show "\<And>x uids.
       procedure_cannot_guess_ids uids (Map.empty, max_impl x) impl_language_loops.toImpl "
      apply (auto simp add: max_impl_def, show_procedures_cannot_guess_ids)
      sorry
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
    by (simp add: inv_def initialState_def invContextH2_calls inv1_def  invContextH2_happensBefore invContextH2_i_invocationOp progr_def)


  case (procedure_correct S i)



  show "procedureCorrect S i"
  proof (rule Initial_Label, rule show_initial_state_prop[OF procedure_correct], rule DC_final2, casify)
    case (show_P S_pre proc initState impl1)
    have "invocationOp S i \<triangleq> proc"
      using show_P by auto
    have "invocationRes S i = None"
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

        have ls: "localState S i \<triangleq> (Map.empty, max_impl list)"
            by (auto simp add: PMax procedures_def )

        show "execution_s_correct S i"
          using ls procedure_correct.in_initial_state
        proof (fuzzy_rule program_proof_rules_loops.execution_s_check_sound3)
          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add:  PMax procedures_def )

          

          show "invocationOp S i \<triangleq> PMax list"
            using PMax \<open>invocationOp S i \<triangleq> proc\<close> by blast

          note max_impl_def[simp]

          show "program_wellFormed (prog S)"
            by (auto simp add: show_P)

          from `invariant_all' S`
          show "invariant progr (invariantContext.truncate S)"
            unfolding invContext'_truncate by auto



          show "program_proof_rules_loops.execution_s_check (invariant progr) (querySpec progr) \<lparr>
                  calls = s_calls, 
                  happensBefore = s_happensBefore, 
                  callOrigin = s_callOrigin, 
                  transactionOrigin = s_transactionOrigin, 
                  knownIds = s_knownIds, 
                  invocationOp = (s_invocationOp(i \<mapsto> PMax list)), 
                  invocationRes = (s_invocationRes(i := None)), 
                  ps_i = i, 
                  ps_generatedLocal = {}, 
                  ps_generatedLocalPrivate = {}, 
                  ps_localKnown = uniqueIds (PMax list), 
                  ps_vis = {}, 
                  ps_localCalls = [], 
                  ps_tx = None, 
                  ps_firstTx = True, 
                  ps_store = Map.empty
                  \<rparr> 
                  (max_impl list) 
                  (finalCheck inv i)" \<comment> \<open>TODO finalCheck could be fixed for the initial P (as variant)\<close>
            if c0: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
              and inv: "invariant progr
                         \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
                            transactionOrigin = s_transactionOrigin, knownIds = s_knownIds,
                            invocationOp = s_invocationOp(i \<mapsto> PMax list), invocationRes = s_invocationRes(i := None)\<rparr>"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
            apply (auto simp add: )
            apply (repliss_vcg_l asmUnfold: loop_inv_def)
          proof (goal_cases loop_inv_start final loop_body )
            case loop_inv_start
            show ?case
              unfolding loop_inv_def
              by (auto simp add: s_read_def Def_def only_store_changed_def)
          next
            case (loop_body PS li_v li re_v re li_done)
            have [simp]: "fromAny li_v = li"
              using loop_body by (auto simp add: Def_def s_read_def)

            have [simp]: "fromAny re_v = re"
              using loop_body by (auto simp add: Def_def s_read_def)

            have "li \<noteq> []"
              using loop_body Def_def by metis


            show ?case
              unfolding loop_inv_def
              apply (rule exI[where x="tl li"])
              apply (rule exI[where x="max (hd li) re"])
              apply (rule exI[where x="li_done @ [hd li]"])
            proof (auto simp add: Def_def loop_body s_read_def intro!: show_only_store_changed[OF loop_body(7)])
              show "list = li_done @ hd li # tl li"
                using Def_def \<open>li \<noteq> []\<close> `list ::= li_done @ li` by fastforce

              from `if li_done = [] then re = 0 else re = Max (set li_done)`
              show "max (hd li) re = Max (insert (hd li) (set li_done))"
                by (auto split: if_splits)
            qed

          next
            case (final PS li_v li re_v re li_done)
            show ?case
            proof (auto simp add: inv_def inv1_def invariantContext.defs)

              show "s_read (ps_store PS) (Ref (Suc 0)) = Max (set list)"
                if c0: "invocationOp PS i \<triangleq> PMax list"
                  and c1: "list \<noteq> []"
                for  list
                using final that by (auto simp add: inv_def inv1_def invariantContext.defs Def_def only_store_changed_def split: if_splits)
                               

              show "r = val.Nat (Max (set list))"
                if c0: "ia \<noteq> i"
                  and c1: "invocationOp PS ia \<triangleq> PMax list"
                  and c2: "list \<noteq> []"
                  and c3: "invocationRes PS ia \<triangleq> r"
                for  ia list r
                using inv that final(7)
                by (auto simp add: inv_def inv1_def final(7) only_store_changed_def, force)
            qed
          qed




        qed (auto simp add: finalCheck_def)
      qed
    qed
  qed
qed



end
