section "Example: Computing Maximum with a Loop"

theory example_loop_max
  imports 
    program_verification_tactics
    impl_language
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


definition max_impl :: "val \<Rightarrow> (val,operation,val) io" where
"max_impl p_list \<equiv> 
   do {
      listR \<leftarrow> makeRef (map nat_value (list_value p_list));
      resR \<leftarrow> makeRef 0;
      loop (do {
        list \<leftarrow> read listR;
        res \<leftarrow> read resR;
        if list = [] then 
          return False
        else do {
          let x = hd list;
          listR ::= tl list;
          resR ::= max x res;
          return True
        }
      });
      res \<leftarrow> read resR;
      return (Nat res)
   }"



datatype proc =
    PMax "nat list"

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
    PMax n \<Rightarrow> toImpl2 (max_impl (ListVal (map Nat n)))
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
       procedure_cannot_guess_ids uids (Map.empty, max_impl (ListVal (map val.Nat x))) impl_language_loops.toImpl "
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

        have ls: "localState S i \<triangleq> (Map.empty, max_impl (ListVal (map val.Nat list)))"
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
                  (max_impl (ListVal (map val.Nat list))) 
                  (finalCheck inv i)" \<comment> \<open>TODO finalCheck could be fixed for the initial P (as variant)\<close>
            if c0: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
            apply (auto simp add: )
            apply repliss_vcg_l


          show "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
       (\<And>tx. s_transactionOrigin tx \<noteq> Some i) \<Longrightarrow>
       program_proof_rules_loops.execution_s_check (invariant progr) (querySpec progr)
        \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
           transactionOrigin = s_transactionOrigin, knownIds = s_knownIds,
           invocationOp = s_invocationOp(i \<mapsto> PMax list), invocationRes = s_invocationRes(i := None), ps_i = i,
           ps_generatedLocal = {}, ps_generatedLocalPrivate = {}, ps_localKnown = uniqueIds (PMax list), ps_vis = {},
           ps_localCalls = [], ps_tx = None, ps_firstTx = True, ps_store = Map.empty\<rparr>
        (max_impl (ListVal (map val.Nat list))) ?P"


          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds (s_invocationOp(i \<mapsto> SendMessage author content)) (s_invocationRes(i := None)) {} {} {} [] None True (sendMessage_impl (String author) (String content))"
            if tx_fresh: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "AtCommit" "AtReturn" )
            case (AtCommit v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)

            have [simp]: "res = Undef"
              using local.AtCommit(16)
              by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def messageStruct_def register_spec_def)
            have [simp]:"resa = Undef"
              using local.AtCommit(17)
              by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def messageStruct_def register_spec_def)

            have [simp]:"resb = Undef"
              using local.AtCommit(18)
              by (auto simp add: crdtSpec_def struct_field_def set_rw_spec_def)

            have [simp]:  "in_sequence [c, ca, cb] c ca"
              by (simp add: in_sequence_cons)

            have "new_unique_not_in_calls s_calls' (to_nat v)"
              by (meson AtCommit(13) uid_is_private'_def)


            hence no_v: "to_nat v \<notin> uniqueIds opr" if "s_calls' c \<triangleq> Call opr r" for c opr r
              by (meson new_unique_not_in_calls_def that)

            have [simp]: "s_calls' delete \<noteq> Some (Call (Message (DeleteKey v)) Undef)" for delete
              apply auto
              apply (drule no_v)
             using `uniqueIds_val_r v = {to_nat v}` by auto

            from AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases  inv2 inv3 inv4)
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case
                by (auto simp add: inv2_def exists_cases1)

            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              
              from inv3 show ?case 
                by (auto simp add: inv3_def updateHb_cases in_sequence_cons cong: conj_cong, meson)
            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv4_def is_update_operation_def in_sequence_cons updateHb_cases)
            qed
              
              
          next
            case (AtReturn v tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            then show ?case
              apply (auto simp add: inv_def)
              apply (auto simp add: inv1_def)
              by (smt map_upd_Some_unfold proc.inject(1))

          qed

        qed
      qed

    next
      case (EditMessage m newContent)
      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case
          using show_P.invariant_pre EditMessage show_P.i_fresh
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def inv4_def invContextH2_simps, 
              metis option.distinct(1) show_P.i_fresh)+

      next
        case execution

        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)
          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: EditMessage procedures_def )

          show "localState S i \<triangleq> editMessage_impl (MessageId m) (String newContent)"
            by (auto simp add: EditMessage procedures_def )

          show "invocationOp S i \<triangleq> EditMessage m newContent"
            using EditMessage \<open>invocationOp S i \<triangleq> proc\<close> by blast

          note editMessage_impl_def[simp]

          

          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds (s_invocationOp(i \<mapsto> EditMessage m newContent)) (s_invocationRes(i := None)) {} {} {} [] None True (editMessage_impl (MessageId m) (String newContent))"
            if tx_fresh: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn")
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)

            note `c \<noteq> ca`[simp]

            from `example_chat.inv
             \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin', transactionOrigin = s_transactionOrigin',
                knownIds = s_knownIds', invocationOp = s_invocationOp'(i \<mapsto> EditMessage m newContent),
                invocationRes = s_invocationRes'(i := None)\<rparr>`
            have  i1: "inv1 (s_invocationOp'(i \<mapsto> EditMessage m newContent)) (s_invocationRes'(i := None))"
              and i2: "inv2 (s_invocationOp'(i \<mapsto> EditMessage m newContent)) s_calls'"
              and i3: "inv3 s_calls' s_happensBefore'"
              and i4: "inv4 s_calls' s_happensBefore'"
              by (auto simp add: inv_def)

            from \<open>crdtSpec (Message (KeyExists (MessageId m))) \<lparr>calls = s_calls' |` vis', happensBefore = s_happensBefore' |r vis'\<rparr> (Bool True)\<close>
            obtain upd_c upd_op upd_r
              where upd_vis: "upd_c \<in> vis'"
                and upd_call: "s_calls' upd_c \<triangleq> Call (Message (NestedOp (MessageId m) upd_op)) upd_r"
                and upd_is_update: "is_update upd_op"
                and ipd_not_deleted: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>x2. s_calls' c' \<triangleq> x2 \<longrightarrow> (\<forall>x2a. x2 \<noteq> Call (Message (DeleteKey (MessageId m))) x2a) \<or> (c', upd_c) \<in> s_happensBefore')"
              by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def restrict_ctxt_op_def restrict_ctxt_def fmap_map_values_def'
                      restrict_map_def deleted_calls_dw_def restrict_relation_def
                   split: option.splits if_splits operation.splits call.splits)





            hence "upd_r = Undef"
              using Exists_AtCommit(9) query_result_undef by auto


            have "upd_c \<noteq> c"
              by (smt Exists_AtCommit(15) Exists_AtCommit(5) Exists_AtCommit(9) basic_trans_rules(31) domIff invariantContext.simps(1) operationContext.select_convs(1) upd_vis wellFormed_callOrigin_dom3)

            have "upd_c \<noteq> ca"
              by (smt Exists_AtCommit(15) Exists_AtCommit(5) Exists_AtCommit(9) basic_trans_rules(31) domIff invariantContext.simps(1) operationContext.select_convs(1) upd_vis wellFormed_callOrigin_dom)

            obtain upda_c upda_val
              where upda_call: "s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef"
                and upda_before_upd: "(upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c"
            proof (atomize_elim, cases upd_op)
              case (Author a)
              obtain x where "a = Assign x"
                using upd_is_update Author 
                by (cases a, auto simp add: is_update_messageDataOp_def)

              show "\<exists>upda_c upda_val.
                   s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef \<and>
                   ((upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c)"
                using Author \<open>a = Assign x\<close> upd_call \<open>upd_r = Undef\<close> by blast

            next
              case (Content a)
              obtain x where "a = Assign x"
                using upd_is_update Content 
                by (cases a, auto simp add: is_update_messageDataOp_def)

              show "\<exists>upda_c upda_val.
                 s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef \<and>
                 ((upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c)"
                using i3 Content \<open>a = Assign x\<close> \<open>upd_r = Undef\<close> upd_call 
                by (auto simp add: inv3_def, blast)
            qed



            have "upda_c \<noteq> c"
              using Exists_AtCommit \<open>upd_c \<noteq> c\<close> upda_before_upd by blast

            have "upda_c \<noteq> ca"
              using Exists_AtCommit \<open>upd_c \<noteq> ca\<close> upda_before_upd by blast





            from Exists_AtCommit
            show ?case
            proof (auto simp add: inv_def, goal_cases "inv2" "inv3" "inv4" )
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv2_def)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              show ?case 
                apply (auto simp add: inv3_def updateHb_cases in_sequence_cons cong: conj_cong)
                 apply (rule exI[where x=upda_c])
                 apply (auto simp add: \<open>upda_c \<noteq> c\<close> \<open>upda_c \<noteq> ca\<close> upda_call)
                using causallyConsistent_def inv3(6) upd_vis upda_before_upd apply fastforce
                by (metis i3 inv3(13) inv3_def)
            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                apply (auto simp add: inv4_def updateHb_cases in_sequence_cons)
                by (metis (no_types, lifting) \<open>upd_r = Undef\<close> ipd_not_deleted upd_call upd_is_update)
            qed
              
          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa)
            then show ?case 
              apply (auto simp add: inv_def )
              apply (auto simp add: inv1_def cong: conj_cong)
              by (smt map_upd_Some_unfold proc.distinct(1))
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case 
            proof (auto simp add: inv_def, goal_cases inv2 inv3 inv4)
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case by (auto simp add: inv2_def)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case by (auto simp add: inv3_def updateHb_single cong: conj_cong, fastforce)
            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv4_def updateHb_single)
            qed
          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case 
              apply (auto simp add: inv_def inv1_def cong: conj_cong)
              by (meson option.inject proc.simps(6))
          qed
        qed
      qed
    next
      case (DeleteMessage m)


      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case
          using show_P.invariant_pre DeleteMessage show_P.i_fresh
          by (auto simp add:  inv_def inv1_def inv2_def inv3_def inv4_def invContextH2_simps, 
              metis option.distinct(1) show_P.i_fresh)+

      next
        case execution

        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)
          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: DeleteMessage procedures_def )

          show "localState S i \<triangleq> deleteMessage_impl (MessageId m)"
            by (auto simp add: DeleteMessage procedures_def )

          show "invocationOp S i \<triangleq> DeleteMessage m"
            using DeleteMessage \<open>invocationOp S i \<triangleq> proc\<close> by blast

          note deleteMessage_impl_def[simp]

          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds (s_invocationOp(i \<mapsto> DeleteMessage m)) (s_invocationRes(i := None)) {} {} {} [] None True (deleteMessage_impl (MessageId m))"
            if tx_fresh: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn")
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)

            from `c \<noteq> ca \<and> c \<noteq> cb \<and> ca \<noteq> cb`
            have [simp]: "c \<noteq> ca" "c \<noteq> cb" "ca \<noteq> cb"
              by auto


            from `example_chat.inv
               \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin', transactionOrigin = s_transactionOrigin',
                  knownIds = s_knownIds', invocationOp = s_invocationOp'(i \<mapsto> DeleteMessage m), invocationRes = s_invocationRes'(i := None)\<rparr>`
            have  i1: "inv1 (s_invocationOp'(i \<mapsto> DeleteMessage m)) (s_invocationRes'(i := None))"
              and i2: "inv2 (s_invocationOp'(i \<mapsto> DeleteMessage m)) s_calls'"
              and i3: "inv3 s_calls' s_happensBefore'"
              and i4: "inv4 s_calls' s_happensBefore'"
              by (auto simp add: inv_def)

            show ?case
            proof (auto simp add: inv_def, goal_cases inv1 inv2 inv3 inv4)
              case inv1
              from i1
              show ?case by auto
            next
              case inv2
              from i2
              show ?case
                by (auto simp add: inv2_def)
            next
              case inv3
              from i3
              show ?case 
                apply (auto simp add: inv3_def updateHb_cases cong: conj_cong)
                by (metis Exists_AtCommit(18)) 

            next
              case inv4
              then show ?case
                apply (auto simp add: inv4_def updateHb_cases in_sequence_cons)
                using Exists_AtCommit(18) apply blast
                by (meson i4 inv4_def)
            qed
              
          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            then show ?case
              apply (auto simp add: inv_def inv1_def)
              by (metis (no_types, lifting) option.inject proc.distinct(3))
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case
            proof (auto simp add: inv_def, goal_cases inv2 inv3 inv4)
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case
                by (auto simp add: inv2_def)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv3_def updateHb_cases in_sequence_cons, fastforce)

            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv4_def updateHb_cases in_sequence_cons)
            qed
          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case 
              apply (auto simp add: inv_def inv1_def)
              by (metis (no_types, lifting) option.inject proc.distinct(3)) 
          qed
        qed
      qed
    next
      case (GetMessage m)


      show "procedureCorrect progr S i"
      proof M_show_procedureCorrect
        case after_invocation
        show ?case
          using show_P.invariant_pre GetMessage show_P.i_fresh
        proof (auto simp add:  inv_def invContextH2_simps, goal_cases inv1 inv2)
          case inv1
          then show ?case
            apply (auto simp add: inv1_def state_wellFormed_invocation_before_result)
            by (metis option.simps(3) show_P.i_fresh)
        next
          case inv2
          then show ?case
            apply (auto simp add: inv2_def)
            by (metis option.distinct(1) show_P.i_fresh)
        qed

      next
        case execution

        show "execution_s_correct progr S i"
          using procedure_correct.in_initial_state
        proof (fuzzy_rule execution_s_check_sound3)
          show "currentProc S i \<triangleq> toImpl"
            by (auto simp add: GetMessage procedures_def )

          show "localState S i \<triangleq> getMessage_impl (MessageId m)"
            by (auto simp add: GetMessage procedures_def )

          show "invocationOp S i \<triangleq> GetMessage m"
            using GetMessage \<open>invocationOp S i \<triangleq> proc\<close> by blast

          note getMessage_impl_def[simp]

          show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds (s_invocationOp(i \<mapsto> GetMessage m)) (s_invocationRes(i := None)) {} {} {} [] None True (getMessage_impl (MessageId m))"
            if tx_fresh: "(\<And>tx. s_transactionOrigin tx \<noteq> Some i)"
            for  s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes
          proof (repliss_vcg, goal_cases "Exists_AtCommit" "Exists_AtReturn" "NotExists_AtCommit" "NotExists_AtReturn")
            case (Exists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            then show ?case 
            proof (auto simp add: inv_def, goal_cases inv2 inv3 inv4)
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv2_def)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv3_def  updateHb_cons cong: conj_cong, meson)
            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv4_def updateHb_cons is_update_messageDataOp_def)
            qed  
          next
            case (Exists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res ca resa cb resb)
            
            from \<open>example_chat.inv
             \<lparr>calls = s_calls', happensBefore = s_happensBefore', callOrigin = s_callOrigin',
                transactionOrigin = s_transactionOrigin', knownIds = s_knownIds',
                invocationOp = s_invocationOp'(i \<mapsto> GetMessage m), invocationRes = s_invocationRes'(i := None)\<rparr>\<close>
            have i1: "inv1 (s_invocationOp'(i \<mapsto> GetMessage m)) (s_invocationRes'(i := None))"
              and i2: "inv2 (s_invocationOp'(i \<mapsto> GetMessage m)) s_calls'"
              and i3: "inv3 s_calls' s_happensBefore'"
              and i4: "inv4 s_calls' s_happensBefore'"
              by (auto simp add: inv_def)

            have "c \<notin> vis'"
              by (simp add: Exists_AtReturn(17))



            from Exists_AtReturn show ?case
            proof (auto simp add: inv_def, goal_cases inv1)
              case (inv1 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)

              

              show ?case
              proof (auto simp add: inv1_def cong: conj_cong)

                show "\<exists>s. s \<noteq> i \<and> (\<exists>content2. s_invocationOp' s \<triangleq> SendMessage author content2)"
                  if c0: "g \<noteq> i"
                    and c1: "s_invocationOp' g \<triangleq> GetMessage m'"
                    and c2: "s_invocationRes' g \<triangleq> Found (String author) content"
                  for  g m' author content
                  using \<open>inv1 (s_invocationOp'(i \<mapsto> GetMessage m)) (s_invocationRes'(i := None))\<close>
                  using that apply (auto simp add: inv1_def)
                  by (metis option.inject proc.distinct(5))


                show "\<exists>s. s \<noteq> i \<and> (\<exists>content2. s_invocationOp' s \<triangleq> SendMessage author content2)"
                  if c0: "resa = String author"
                  for  author
                proof -

                  have [simp]: "x \<in> Field (s_happensBefore' |r vis') \<Longrightarrow> x \<in> vis'" for x
                    by (auto simp add: Field_def restrict_relation_def)

                  hence [simp]: " x \<in> Field (s_happensBefore' |r vis') \<Longrightarrow> \<exists>y. s_calls' x \<triangleq> y" for x
                    by (meson  in_dom `vis' \<subseteq> dom s_calls'`)

                  from \<open>crdtSpec (Message (KeyExists (MessageId m)))
                     \<lparr>calls = s_calls' |` vis', happensBefore = s_happensBefore' |r vis'\<rparr> (Bool True)\<close>
                  have "crdtSpec' (Message (KeyExists (MessageId m))) (dom s_calls' \<inter> vis') (extract_op s_calls') s_happensBefore' id (Bool True)"
                    apply (subst(asm) crdtSpec'_alt)
                    by (auto simp add: crdtSpec'_alt crdtSpec'_simp_op crdtSpec'_simp_hb)



                  from this
                  obtain upd_c upd_call upd_op
                    where upd_call1: "s_calls' upd_c \<triangleq> upd_call"
                      and upd_vis: "upd_c \<in> vis'"
                      and upd_c_op: "extract_op s_calls' upd_c = Message (NestedOp (MessageId m) upd_op)"
                      and upd_is_update: "is_update upd_op"
                      and ud_not_deleted: "\<forall>d. extract_op s_calls' d = Message (DeleteKey (MessageId m)) \<longrightarrow> d \<in> dom s_calls' \<and> d \<in> vis' \<longrightarrow> (d, upd_c) \<in> s_happensBefore'"
                    by (auto simp add: C_out_calls_def crdtSpec'_def struct_field'_def map_dw_spec'_def map_spec'_def deleted_calls_dw'_def)

                  obtain upd_r where 
                    upd_call: "s_calls' upd_c \<triangleq> Call (Message (NestedOp (MessageId m) upd_op)) upd_r"
                    using upd_call1 upd_c_op
                    by (auto simp add: extract_op_def' split: call.splits)


                  have "upd_r = Undef"
                    using local.Exists_AtReturn(9) upd_call upd_is_update
                    by (rule query_result_undef)


                  obtain upda_c upda_val
                    where upda_call: "s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef"
                      and upda_before_upd: "(upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c"
                  proof (atomize_elim, cases upd_op)
                    case (Author a)
                    obtain x where "a = Assign x"
                      using upd_is_update Author 
                      by (cases a, auto simp add: is_update_messageDataOp_def)

                    show "\<exists>upda_c upda_val.
                   s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef \<and>
                   ((upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c)"
                      using Author \<open>a = Assign x\<close> upd_call \<open>upd_r = Undef\<close> by blast

                  next
                    case (Content a)
                    obtain x where "a = Assign x"
                      using upd_is_update Content 
                      by (cases a, auto simp add: is_update_messageDataOp_def)

                    show "\<exists>upda_c upda_val.
                 s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef \<and>
                 ((upda_c, upd_c) \<in> s_happensBefore' \<or> upda_c = upd_c)"
                      using i3 Content \<open>a = Assign x\<close> \<open>upd_r = Undef\<close> upd_call 
                      by (auto simp add: inv3_def, blast)
                  qed

                  have [simp]: "upda_c \<noteq> c"
                    by (metis Exists_AtReturn(9) inv1(12) invariantContext.simps(1) operationContext.simps(1) option.simps(3) upda_call wellFormed_callOrigin_dom3)

                  from \<open>crdtSpec (Message (NestedOp (MessageId m) (Author Read)))
                   \<lparr>calls = (s_calls' |` (vis'))(c \<mapsto> Call (Message (KeyExists (MessageId m))) (Bool True)),
                      happensBefore = updateHb (s_happensBefore' |r vis') vis' [c]\<rparr>
                   resa\<close>
                  have spec1: "crdtSpec' (Message (NestedOp (MessageId m) (Author Read))) (insert c (dom s_calls' \<inter> (vis' )))
                       (extract_op ((s_calls' |` (vis'))(c \<mapsto> Call (Message (KeyExists (MessageId m))) (Bool True))))
                       (updateHb (s_happensBefore' |r vis') vis' [c]) id resa"
                    apply (subst(asm) crdtSpec'_alt)
                  proof (auto simp add: crdtSpec'_alt crdtSpec'_simp_op crdtSpec'_simp_hb  )

                    show "\<exists>y. s_calls' x \<triangleq> y"
                      if c0: "x \<in> Field (updateHb (s_happensBefore' |r vis') vis' [c])"
                        and c1: "x \<noteq> c"
                      for  x
                      using that `vis' \<subseteq> dom s_calls'` by (auto simp add: in_sequence_cons Field_def restrict_relation_def updateHb_cases)


                    show "x \<in> vis'"
                      if c0: "x \<in> Field (updateHb (s_happensBefore' |r vis') vis' [c])"
                        and c1: "x \<noteq> c"
                      for  x
                      using that `vis' \<subseteq> dom s_calls'` by (auto simp add: in_sequence_cons Field_def restrict_relation_def updateHb_cases)

                  qed

                  have spec2: "crdtSpec' (Message (NestedOp (MessageId m) (Author Read))) 
                       (insert c (dom s_calls' \<inter> (vis')))
                       ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                       (updateHb s_happensBefore' vis' [c]) id resa"
                  proof (rule use_ccrdtSpec_wf1[OF crdtSpec'_wf, rotated -1, OF spec1])

                    show " map_same_on (insert c (dom s_calls' \<inter> (vis' )))
                       (extract_op ((s_calls' |` (vis' ))(c \<mapsto> Call (Message (KeyExists (MessageId m))) (Bool True))))
                       ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))"
                      by (auto simp add: map_same_on_def extract_op_def)

                    show " rel_same_on (insert c (dom s_calls' \<inter> (vis'))) (updateHb (s_happensBefore' |r vis') vis' [c])
                           (updateHb s_happensBefore' vis' [c])"
                      using inv1(14) by (auto simp add: rel_same_on_def updateHb_cons restrict_relation_def)
                  qed

                  have [simp]: "(\<lambda>x. Message (NestedOp (MessageId m) x)) \<circ> Author
                      = Message \<circ> (NestedOp (MessageId m)) \<circ> Author"
                    by auto

                  have [simp]: "upda_c \<in> vis'"
                    using causallyConsistent_def inv1(6) upd_vis upda_before_upd by fastforce

                  from spec2
                  have "is_from (String author) Undef
                     (latest_values'
                       (C_out_calls (Message \<circ> NestedOp (MessageId m) \<circ> Author)
                         ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                         (C_out_calls (Message \<circ> NestedOp (MessageId m)) ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                           (insert c (dom s_calls' \<inter> (vis'))) -
                          deleted_calls_dw'
                           (C_out_calls Message ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                             (insert c (dom s_calls' \<inter> (vis'))))
                           ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c]) Message
                           (MessageId m)))
                       ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c])
                       (Message \<circ> NestedOp (MessageId m) \<circ> Author))"
                    by (auto simp add: crdtSpec'_def `resa = String author` struct_field'_def map_dw_spec'_def
                        map_spec'_def restrict_calls_def2 messageStruct'_def register_spec'_def)

                  hence spec3: "(String author) \<in>
                     (latest_values'
                       (C_out_calls (Message \<circ> NestedOp (MessageId m) \<circ> Author)
                         ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                         (C_out_calls (Message \<circ> NestedOp (MessageId m)) ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                           (insert c (dom s_calls' \<inter> (vis' ))) -
                          deleted_calls_dw'
                           (C_out_calls Message ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                             (insert c (dom s_calls' \<inter> (vis' ))))
                           ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c]) Message
                           (MessageId m)))
                       ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c])
                       (Message \<circ> NestedOp (MessageId m) \<circ> Author))"
                    apply (rule is_from_exists[THEN iffD1, rotated])
                  proof (rule latest_values'_exists)

                    show "finite
                       (C_out_calls (Message \<circ> NestedOp (MessageId m) \<circ> Author) ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                         (C_out_calls (Message \<circ> NestedOp (MessageId m)) ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                           (insert c (dom s_calls' \<inter> (vis'))) -
                          deleted_calls_dw'
                           (C_out_calls Message ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                             (insert c (dom s_calls' \<inter> (vis'))))
                           ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c]) Message
                           (MessageId m)))"
                    proof (rule finite_subset)
                      show "finite (dom s_calls')"
                        using Exists_AtReturn(9) wf_finite_calls by force
                    qed (auto simp add: C_out_calls_def)

                    have "acyclic s_happensBefore'"
                      using happensBefore_acyclic[OF local.inv1(17)] by simp

                    show "acyclic (updateHb s_happensBefore' vis' [c])"
                      using \<open>acyclic s_happensBefore'\<close>
                      proof (rule acyclic_updateHb)

                        show "distinct [c]" by simp

                        show "vis' \<inter> set [c] = {}"
                          using \<open>c \<notin> vis'\<close> by auto

                        show " Field s_happensBefore' \<inter> set [c] = {}"
                          by (metis DomainE Field_def RangeE Un_iff disjoint_iff_not_equal empty_set inv1(14) inv1(15) list.simps(15) singletonD)
                      qed

                    from upda_before_upd
                    have delete_before_upda_c: "(d, upda_c) \<in> s_happensBefore'"
                      if d_not_c: "d \<noteq> c"
                        and d_vis: "d \<in> vis'"
                        and d_call: "s_calls' d \<triangleq> Call (Message (DeleteKey (MessageId m))) x2"
                      for  d x2
                    proof 


                      obtain d_ctxt where "querySpec progr (Message (DeleteKey (MessageId m))) d_ctxt x2"
                        by (meson d_call get_query_spec inv1(17))

                      hence [simp]: "x2 = Undef"
                        by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def) 

                      have [simp]: "d \<in> dom s_calls'"
                        using d_call by blast

                      have "(d, upd_c) \<in> s_happensBefore'"
                        using ud_not_deleted[rule_format, where d=d]  d_vis d_call
                        by (auto simp add: extract_op_def split: option.splits)

                      show "(d, upda_c) \<in> s_happensBefore'" if "upda_c = upd_c"
                        using `(d, upd_c) \<in> s_happensBefore'` `upda_c = upd_c` by simp


                      show "(d, upda_c) \<in> s_happensBefore'"
                        if c0: "(upda_c, upd_c) \<in> s_happensBefore'"
                      proof (rule ccontr)
                        assume "(d, upda_c) \<notin> s_happensBefore'"

                        from `inv4 s_calls' s_happensBefore'`
                        show False
                          apply (auto simp add: inv4_def)
                          apply (drule spec[where x=upd_c])
                          apply (drule spec[where x=d])
                          using upd_is_update by (auto simp add: d_call upd_call  \<open>upd_r = Undef\<close> \<open>(d, upd_c) \<in> s_happensBefore'\<close>)
                      qed
                    qed

                    show "\<exists>ca y.
                           ca \<in> C_out_calls (Message \<circ> NestedOp (MessageId m) \<circ> Author)
                                  ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                                  (C_out_calls (Message \<circ> NestedOp (MessageId m)) ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                                    (insert c (dom s_calls' \<inter> vis')) -
                                   deleted_calls_dw'
                                    (C_out_calls Message ((extract_op s_calls')(c := Message (KeyExists (MessageId m))))
                                      (insert c (dom s_calls' \<inter> vis')))
                                    ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c]) Message
                                    (MessageId m)) \<and>
                           ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) ca =
                           (Message \<circ> NestedOp (MessageId m) \<circ> Author) (Assign y)"
                    proof (auto simp add: C_out_calls_def cong: conj_cong; intro exI conjI)
                      show "upda_c \<noteq> c"
                        by auto

                      from `s_calls' upda_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign upda_val)))) Undef`
                      show "extract_op s_calls' upda_c = Message (NestedOp (MessageId m) (Author (Assign upda_val)))"
                        by (auto  simp add: extract_op_def)
                      thus "extract_op s_calls' upda_c = Message (NestedOp (MessageId m) (Author (Assign upda_val)))" .
                      thus "extract_op s_calls' upda_c = Message (NestedOp (MessageId m) (Author (Assign upda_val)))" .

                      show "upda_c \<in> dom s_calls'"
                        using upda_call by blast

                      show "upda_c \<in> vis'"
                        by auto

                      show "upda_c
                          \<notin> deleted_calls_dw' {ca. ca \<noteq> c \<longrightarrow> ca \<in> dom s_calls' \<and> ca \<in> vis' \<and> (\<exists>x. extract_op s_calls' ca = Message x)}
                        ((extract_op s_calls')(c := Message (KeyExists (MessageId m)))) (updateHb s_happensBefore' vis' [c]) Message
                        (MessageId m)"
                        using delete_before_upda_c  by (auto simp add: deleted_calls_dw'_def updateHb_cons extract_op_def' split: call.splits)
                    qed
                  qed

                  have [simp]: "c' \<noteq> c" if "c' \<in> vis'" for c'
                    using \<open>c \<notin> vis'\<close> that by blast

                  have [simp]: "c \<in> dom s_calls'" if "c \<in> vis'" for c
                    using inv1(4) that by blast


                  from spec3
                  obtain updb_c updb_res
                    where updb_c1: "\<forall>x. x \<in> dom s_calls' \<longrightarrow> (\<exists>res. s_calls' x \<triangleq> Call (Message (DeleteKey (MessageId m))) res) \<longrightarrow> x \<in> vis' \<longrightarrow> (x, updb_c) \<in> s_happensBefore'"
                      and updb_c_vis: "updb_c \<in> vis'"
                      and updb_c_call: "s_calls' updb_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign (String author))))) updb_res"
                      and updb_c2: "\<forall>c'. c' \<in> vis' \<longrightarrow> (\<forall>y res. s_calls' c' \<noteq> Some (Call (Message (NestedOp (MessageId m) y)) res)) \<or> (\<exists>y res. s_calls' c' \<triangleq> Call (Message y) res) \<and> (\<exists>x. (\<exists>res. s_calls' x \<triangleq> Call (Message (DeleteKey (MessageId m))) res) \<and> x \<in> vis' \<and> (x, c') \<notin> s_happensBefore') \<or> (\<forall>y res. s_calls' c' \<noteq> Some (Call (Message (NestedOp (MessageId m) (Author y))) res)) \<or> (\<forall>v' res. s_calls' c' \<noteq> Some (Call (Message (NestedOp (MessageId m) (Author (Assign v')))) res)) \<or> (updb_c, c') \<notin> s_happensBefore'"
                    apply (auto simp add: latest_values'_def latest_assignments'_def in_deleted_calls_dw'
                      in_C_out extract_op_eq Ball_def Bex_def updateHb_cons
                        split: if_splits
                      cong: conj_cong disj_cong
                      )
                    by blast

                  from updb_c_call
                  have "\<exists>ctxt. querySpec progr (Message (NestedOp (MessageId m) (Author (Assign (String author))))) ctxt updb_res"
                    by (meson get_query_spec inv1(17))

                  hence [simp]: " updb_res = Undef"
                    by (auto simp add: crdtSpec_def struct_field_def map_dw_spec_def map_spec_def messageStruct_def register_spec_def)

                  from updb_c_call
                  have updb_c_call': " s_calls' updb_c \<triangleq> Call (Message (NestedOp (MessageId m) (Author (Assign (String author))))) Undef"
                    by simp

                  from `inv2 (s_invocationOp'(i \<mapsto> GetMessage m)) s_calls'`[unfolded inv2_def, rule_format, OF updb_c_call']
                  obtain ia s where "(s_invocationOp'(i \<mapsto> GetMessage m)) ia \<triangleq> SendMessage author s"
                    by blast

                  thus "\<exists>s. s \<noteq> i \<and> (\<exists>content2. s_invocationOp' s \<triangleq> SendMessage author content2)"
                    by (metis map_upd_Some_unfold proc.distinct(5))
                qed
              qed
            qed
          next
            case (NotExists_AtCommit tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case
            proof (auto simp add: inv_def, goal_cases inv2 inv3 inv4)
              case (inv2 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv2_def)
            next
              case (inv3 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv3_def updateHb_cases in_sequence_cons cong: conj_cong, fastforce)
            next
              case (inv4 some_generatedIds some_generatedIds1 some_currentTransaction some_currentTransaction1 some_localState some_localState1 some_currentProc some_currentProc1 some_visibleCalls some_visibleCalls1 some_transactionStatus some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2)
              then show ?case 
                by (auto simp add: inv4_def updateHb_cases in_sequence_cons)
            qed
          next
            case (NotExists_AtReturn tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis' s_invocationOp' s_invocationRes' c res)
            then show ?case
              apply (auto simp add: inv_def)
              apply (auto simp add: inv1_def)
              by (metis (no_types, lifting) option.inject proc.distinct(5))
          qed
        qed
      qed
    qed
  qed
qed


end
