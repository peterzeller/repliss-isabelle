section "Program Proof Rules With Loops"

theory program_proof_rules_loops
  imports 
    invariant_simps 
    unique_ids2
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    impl_language_loops
    topological_sort
    program_verification_tactics
begin

term "set"

text "We define some proof rules for our implementation languages, so that 
we can automate the generation of verification conditions.

The proof rules can simulate symbolic execution of a procedure.
We add some additional state compared to the system state in the semantics, so that we can derive
additional assumptions for the verification conditions."

\<comment> \<open>
Maybe it would have been better to use a record below.
However, with records it is sometimes difficult to get them into 
a normalized form where rules are directly applicable.
Still, it might be worth a try as it would make the rules more readable.
\<close>



record ('proc, 'any, 'operation) proof_state = "('proc, 'operation, 'any) invariantContext" +
  ps_i :: invocId
  ps_generatedLocal  :: "uniqueId set"
  ps_generatedLocalPrivate  :: "uniqueId set"
  ps_localKnown :: "uniqueId set"
  ps_vis :: "callId set"
  ps_localCalls :: "callId list"
  ps_tx :: "txid option"
  ps_firstTx :: bool
  ps_store :: "'any store"



definition proof_state_rel :: "
     ('proc::valueType, 'any::valueType, 'operation::valueType) proof_state 
  \<Rightarrow> ('proc, ('any store \<times> uniqueId set \<times> ('any, 'operation, 'any) io), 'operation, 'any) state 
  \<Rightarrow> bool" where
  "proof_state_rel S S1 \<equiv> 
         state_wellFormed S1
       \<and> calls S1 = calls S
       \<and> happensBefore S1 = updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)
       \<and> callOrigin S1 = map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S))
       \<and> transactionOrigin S1 = (transactionOrigin S)
       \<and> knownIds S1 = (knownIds S)
       \<and> invocationOp S1 = (invocationOp S)
       \<and> invocationRes S1 = (invocationRes S)
       \<and> ps_generatedLocal S = {x. generatedIds S1 x \<triangleq> ps_i S}
       \<and> (\<exists>ps_ls. localState S1 (ps_i S) \<triangleq> (ps_store S, ps_localKnown S,  ps_ls))
       \<and> currentProc S1 (ps_i S) \<triangleq> toImpl 
       \<and> visibleCalls S1 (ps_i S) \<triangleq>  (ps_vis S \<union> set (ps_localCalls S))
       \<and> currentTransaction S1 (ps_i S) = ps_tx S
       \<and> (\<forall>tx'. ps_tx S \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted)
       \<and> (case ps_tx S of Some tx' \<Rightarrow> set (ps_localCalls S) =  {c. callOrigin S1 c \<triangleq> tx'} 
                          | None \<Rightarrow> ps_localCalls S = [])
       \<and> (sorted_by (happensBefore S1) (ps_localCalls S))
       \<and> (ps_vis S \<inter> set (ps_localCalls S) = {})
       \<and> (dom (callOrigin S) \<inter> set (ps_localCalls S) = {})
       \<and> (Field (happensBefore S) \<inter> set (ps_localCalls S) = {})
       \<and> distinct (ps_localCalls S)
       \<and> (ps_firstTx S \<longleftrightarrow> (\<nexists>c tx . callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> ps_i S \<and> transactionStatus S1 tx \<triangleq> Committed ))
       \<and> (\<forall>c. i_callOriginI_h (callOrigin S) (transactionOrigin S) c \<triangleq> (ps_i S) \<longrightarrow> c \<in> (ps_vis S))
       \<and> (ps_generatedLocalPrivate S \<subseteq> ps_generatedLocal S)
       \<and> (\<forall>v\<in>ps_generatedLocalPrivate S. uid_is_private (ps_i S) S1 v)
       \<and> (finite (dom (ps_store S)))
       \<and> (invocation_cannot_guess_ids (ps_localKnown S) (ps_i S) S1)
       \<and> (ps_generatedLocal S \<subseteq> ps_localKnown S)
"

\<comment> \<open>There might be a more elegant solution for this. Deatomize\<close>
lemmas proof_state_rel_fact = 
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1]
  proof_state_rel_def[THEN meta_eq_to_obj_eq, THEN iffD1, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2]


lemma proof_state_rel_wf: 
  "proof_state_rel S S1 \<Longrightarrow> state_wellFormed S1"
  unfolding proof_state_rel_def
  by auto

text "Define execution of a command."


fun io_nested :: "('a,'operation, 'any) io \<Rightarrow> ('a,'operation, 'any) io set" where
  "io_nested (WaitLocalStep n)  = (snd ` snd ` range n)"
| "io_nested (WaitBeginAtomic n)  =  {n}"
| "io_nested (WaitEndAtomic n)  = {n} "
| "io_nested (WaitNewId P n)  =  range n"
| "io_nested (WaitDbOperation op n)  =  range n"
| "io_nested (WaitReturn s)  =  {}"
| "io_nested (Loop body n)  = {n}" 

lemma io_nested_wf: "wf {(x,y). x\<in>io_nested y}"
proof (rule wfI)
  show "{(x, y). x \<in> io_nested y} \<subseteq> UNIV \<times> UNIV"
    by simp

  show "P x" 
    if induct: "\<forall>x. (\<forall>y. (y, x) \<in> {(x, y). x \<in> io_nested y} \<longrightarrow> P y) \<longrightarrow> P x"
    for  x and P :: "('a,'operation, 'any) io \<Rightarrow> bool"
  proof (induct x)
    case (WaitLocalStep x)
    show ?case
    proof (rule induct[rule_format])

      show "P y"
        if c0: "(y, impl_language_loops.io.WaitLocalStep x) \<in> {(x, y). x \<in> io_nested y}"
        for  y
        using that apply auto
        using WaitLocalStep.hyps by auto
    qed
  next
    case (WaitBeginAtomic x)
    show ?case
      by (simp add: WaitBeginAtomic.hyps that)
  next
    case (WaitEndAtomic x)
    then show ?case 
      by (simp add: WaitEndAtomic.hyps that)
  next
    case (WaitNewId x1a x2a)
    then show ?case
      using that by auto
  next
    case (WaitDbOperation x1a x2a)
    then show ?case
      using that by auto
  next
    case (WaitReturn x)
    then show ?case
      using that by auto
  next
    case (Loop x1a x)
    then show ?case
      by (simp add: that) 
  qed
qed

lemma io_nested_acyclic: "acyclic {(x, y). x \<in> io_nested y}"
  using io_nested_wf wf_acyclic by blast

lemma acyclic_non_refl: "acyclic r \<Longrightarrow> (x,x) \<notin> r"
  by (meson acyclic_def trancl.intros(1))


lemma io_nested_non_refl: "x \<notin> io_nested x"
  using acyclic_non_refl[OF io_nested_acyclic]
  by auto

definition "io_is_nested x y \<equiv> (x,y) \<in> {(x, y). x \<in> io_nested y}\<^sup>+"



definition "proof_state_wellFormed PS \<equiv> \<exists>S. proof_state_rel PS S \<and> state_wellFormed S"


lemma show_proof_state_wellFormed:
  assumes "state_wellFormed S" and "proof_state_rel PS S" 
  shows "proof_state_wellFormed PS"
  using assms(1) assms(2) proof_state_wellFormed_def by auto

\<comment> \<open>TODO : more properties about freshness: uid cannot be used anywhere \<close>
definition "uid_fresh uid S \<equiv> uid_is_private' (ps_i S) (calls S)
  (invocationOp S) (invocationRes S) (knownIds S) uid"


\<comment> \<open>TODO: need some information about Growing \<close>
definition "ps_growing S S' \<equiv> True"

text "Define execution of io commands:"


definition step_io :: "
     (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool)
  \<Rightarrow> ('operation \<Rightarrow> ('operation, 'any) operationContext \<Rightarrow> 'any \<Rightarrow> bool)
  \<Rightarrow> ('proc, 'any, 'operation) proof_state 
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> ('proc, 'operation, 'any) action \<comment> \<open>TODO: is action needed at all?\<close>
  \<Rightarrow> ('proc, 'any, 'operation) proof_state
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> bool \<comment> \<open>step is correct\<close>
  \<Rightarrow> bool " where
  "step_io progInv qrySpec S cmd action S' cmd' Inv \<equiv> 
  case cmd of
    WaitReturn r \<Rightarrow> False
  | WaitLocalStep cont \<Rightarrow> 
      (action = ALocal Inv
      \<and> (\<exists>store' ok.  
           cont (ps_store S) =  (ok, store', cmd') 
         \<and> (Inv \<longleftrightarrow> ok \<and> finite (dom store'))
         \<and> (S' = S\<lparr>      
            ps_store := store'
           \<rparr>)))
  | WaitBeginAtomic n \<Rightarrow>
      \<exists>t txns vis'
        calls' happensBefore' callOrigin' transactionOrigin' knownIds' invocationOp' invocationRes'.
          action = ABeginAtomic t txns
        \<and> cmd' = n
        \<and> Inv
        \<and> proof_state_wellFormed S'
        \<and> progInv (invariantContext.truncate (S'\<lparr>transactionOrigin := transactionOrigin'(t := None) \<rparr>))
        \<and> transactionOrigin' t \<triangleq> (ps_i S) 
        \<and> (S' = S\<lparr>
             calls := calls',
             happensBefore := happensBefore',
             callOrigin := callOrigin',
             transactionOrigin := transactionOrigin',
             knownIds := knownIds',
             invocationOp := invocationOp',
             invocationRes := invocationRes',
             ps_tx := Some t,
             ps_vis := vis'
          \<rparr>)
        \<and> ps_growing S S'
        \<and> transactionOrigin S t = None
  | WaitEndAtomic n \<Rightarrow>
       action = AEndAtomic  
      \<and> cmd' = n
      \<and> (S' = S\<lparr>
        happensBefore := updateHb (happensBefore S) (ps_vis S) (ps_localCalls S),
        callOrigin := map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S)),
        ps_tx := None,
        ps_localCalls := [],
        ps_vis := ps_vis S \<union> set (ps_localCalls S),
        ps_firstTx := ps_firstTx S \<and> ps_localCalls S = []
      \<rparr>)
      \<and> (Inv  \<longleftrightarrow> progInv (invariantContext.truncate S'))
  | WaitNewId P n \<Rightarrow>
    \<exists> uidv uid.
        action = ANewId uidv
     \<and> cmd' = n uidv
     \<and> Inv
     \<and> uniqueIds uidv = {uid}
     \<and> uid \<notin> ps_generatedLocal S
     \<and> uid_fresh uid S
     \<and> (S' = S\<lparr>
          ps_localKnown := ps_localKnown S \<union> {uid},
          ps_generatedLocal := ps_generatedLocal S \<union> {uid},
          ps_generatedLocalPrivate := ps_generatedLocalPrivate S \<union> {uid}
         \<rparr>)
  | WaitDbOperation oper n \<Rightarrow>
       (if Inv then
          \<exists>c res. 
           calls S c = None
         \<and> ps_tx S \<noteq> None
         \<and> uniqueIds oper \<subseteq> ps_localKnown S 
         \<and> qrySpec oper (getContextH (calls S) (updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)) (Some (ps_vis S \<union> set (ps_localCalls S)))) res
         \<and> cmd' = n res
         \<and> (S' = S\<lparr>
            ps_localKnown := ps_localKnown S \<union> uniqueIds res, 
            ps_generatedLocalPrivate := ps_generatedLocalPrivate S - uniqueIds oper,
            calls := (calls S)(c \<mapsto> Call oper res),
            ps_localCalls := ps_localCalls S @ [c]
          \<rparr>)
        else
          S' = S \<and> cmd' = cmd \<and> \<not>(uniqueIds oper \<subseteq> ps_localKnown S) 
        )
  | Loop body n \<Rightarrow> 
      cmd' = from_V body \<bind> (\<lambda>r. if r then n else Loop body n)
      \<and> Inv
      \<and> (S' = S)
"




text \<open>@{term steps_io} is an inductive definition for combining multiple steps and getting 
  a result value (from WaitReturn).
If the result is None, there was an error in the execution.
Otherwise, the result is Some r.
\<close>

inductive steps_io :: "
     (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool)
  \<Rightarrow> ('operation \<Rightarrow> ('operation, 'any) operationContext \<Rightarrow> 'any \<Rightarrow> bool)
  \<Rightarrow> ('proc, 'any, 'operation) proof_state 
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> ('proc, 'any, 'operation) proof_state
  \<Rightarrow> 'a option
  \<Rightarrow> bool " for progInv qrySpec where
  steps_io_final:
  "steps_io progInv qrySpec S (WaitReturn res) S (Some res)"
| steps_io_error:
  "step_io progInv qrySpec S cmd action S' cmd' False
  \<Longrightarrow> steps_io progInv qrySpec S cmd S' None"
| steps_io_step:
  "\<lbrakk>step_io progInv qrySpec S cmd action S' cmd' True;
   steps_io progInv qrySpec S' cmd' S'' res
\<rbrakk>
 \<Longrightarrow>  steps_io progInv qrySpec S cmd S'' res"

\<comment> \<open>TODO might want to change this: remove the trace 
and steps-io-partial. Instead return None when not ok and 
only allow to make a step when ok. \<close>

\<comment> \<open>TODO: better to have a case on the action? 
Hmm, not really. Then I would not know when I am done.

One problem is: Two io values can be different but have the same semantics (e.g. unrolled loops).
I should define semantic equality below.
\<close>




lemma cmd_is_local:
  assumes noReturn: "\<And>r. cmd \<noteq> WaitReturn r"
  shows
    "(cmd \<bind> cmdCont = WaitLocalStep n)
\<longleftrightarrow> (\<exists>n'. cmd = WaitLocalStep n' 
      \<and> (\<forall>store. 
          let (ok,  st, cmd) = n store;
              (ok', st', cmd') = n' store
          in st = st' \<and> ok = ok' \<and> cmd = (cmd' \<bind> cmdCont))) "
  using noReturn  apply (induct cmd)
        apply (auto simp add: noReturn dest!: fun_cong2 intro!: HOL.ext split: prod.splits)
proof -
  fix x :: "(nat \<Rightarrow> 'c option) \<Rightarrow> bool \<times> (nat \<Rightarrow> 'c option) \<times> ('a, 'b, 'c) impl_language_loops.io" and s :: "nat \<Rightarrow> 'c option" and x1 :: bool and a :: "nat \<Rightarrow> 'c option" and b :: "('a, 'b, 'c) impl_language_loops.io"
  assume a1: "\<forall>store x1 a b x1a aa ba. x store = (x1a, aa, ba) \<longrightarrow> n store = (x1, a, b) \<longrightarrow> a = aa \<and> x1 = x1a \<and> b = ba \<bind> cmdCont"
  assume a2: "x s = (x1, a, b)"
  obtain bb :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> bool" and zz :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> nat \<Rightarrow> 'c option" and ii :: "bool \<times> (nat \<Rightarrow> 'c option) \<times> ('d, 'b, 'c) impl_language_loops.io \<Rightarrow> ('d, 'b, 'c) impl_language_loops.io" where
    f3: "\<forall>p. p = (bb p, zz p, ii p)"
    by (meson prod_cases3)
  then have "n s = (bb (n s), zz (n s), ii (n s))"
    by meson
  then have f4: "zz (n s) = a \<and> (\<not> bb (n s)) \<noteq> x1 \<and> ii (n s) = b \<bind> cmdCont"
    using a2 a1 by presburger
  have "n s = (bb (n s), zz (n s), ii (n s))"
    using f3 by meson
  then show "(x1, a, b \<bind> cmdCont) = n s"
    using f4 by force
qed

abbreviation
  "currentCommand S i \<equiv> snd (snd (the (localState S i)))"



lemma prop_subst': "t = s \<Longrightarrow> PROP P t \<Longrightarrow> PROP P s"
  by auto

\<comment> \<open>Strange rotations and shifting to remove the first equality that you
usually get when using a cases rule.\<close>
method remove_first_equality = (
    (rotate_tac 1),
    ((erule rev_mp)+)?,
    (rule impI),
    (erule prop_subst'),
    ((rule impI)+)?,
    ((erule rev_mp)+)?,
    (unfold triv_forall_equality)?,
    ((rule impI)+)?
    )

lemma "\<And>y a b q. \<lbrakk>x = y; A x y a; B x y b; C x y \<rbrakk> \<Longrightarrow> D x y a"
  apply remove_first_equality
  oops


method cmd_step_cases uses step insert simps  = 
  (rule step_s.cases[OF step]; 
    remove_first_equality;
    insert insert;
    (((auto simp add: simps split: prod.splits)[1]; fail)?); 
    ((erule Pair_inject)+)?,
    goal_cases A)
  (*
  erule prop_subst;
  goal_cases A)
*)




lemma step_io_simulation:
  assumes rel: "proof_state_rel PS S"
    and step: "S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'"
    and i_def: "i = ps_i PS"
    and cmd_prefix: "currentCommand S i = cmd \<bind> cmdCont"
    and cm_no_return: "\<And>r. cmd \<noteq> WaitReturn r"
    and prog_wf: "program_wellFormed (prog S)"
    and no_generate_db: "\<And>c Op res. action = ADbOp c Op res \<Longrightarrow> uniqueIds Op \<subseteq> ps_localKnown PS"
  shows "\<exists>PS' cmd'. step_io (invariant (prog S)) (querySpec (prog S)) 
                            PS cmd action PS' cmd' Inv 
               \<and> (Inv \<longrightarrow> proof_state_rel PS' S' \<and> currentCommand S' i = cmd' \<bind> cmdCont)" (is ?g)
proof (rule ccontr)
  assume "\<not>?g"

  hence goal: False if ?g
    using that by blast



  have toImpl: "currentProc S (ps_i PS) \<triangleq> toImpl"
    by (simp add: assms(1) proof_state_rel_fact(11))
  hence currentProc[simp]: "currentProc S i \<triangleq> toImpl"
    using i_def by simp


  have ls[simp]: "localState S i \<triangleq> (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
    using cmd_prefix i_def proof_state_rel_fact(10) rel by force

  have "state_wellFormed S"
    using proof_state_rel_fact(1) rel by auto
  hence "state_wellFormed S'"
    using local.step state_wellFormed_combine_s1 by blast


  have [simp]: "invocationOp S i \<noteq> None"
    by (simp add: \<open>state_wellFormed S\<close> wf_localState_to_invocationOp)

  have [simp]: "finite (dom (ps_store PS))"
    using proof_state_rel_fact(25) rel by blast


  have no_guess: "(invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S)"
    by (simp add: proof_state_rel_fact[OF rel])

  have "(the (localState S (ps_i PS))) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
    using i_def ls by auto

  have uip: "uid_is_private i S' uidv" 
    if "uid_is_private i S uidv"
      and "uidv \<notin> action_outputs action"
    for uidv
  proof (rule uid_is_private_step_s_same)
    show "S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'"
      using `S ~~ (i, action, Inv) \<leadsto>\<^sub>S S'` .

    show "state_wellFormed S"
      by (simp add: \<open>state_wellFormed S\<close>)
    show "program_wellFormed (prog S)"
      using prog_wf by auto
    show "uid_is_private i S uidv"
      using that by simp
    show "uidv \<notin> action_outputs action"
      using that by simp
  qed

  hence uip': "uid_is_private (ps_i PS) S' uidv" 
    if "uid_is_private (ps_i PS) S uidv"
      and "uidv \<notin> action_outputs action"
    for uidv
    by (simp add: i_def that(1) that(2))




  show False
  proof (cases cmd)
    case (WaitLocalStep n)

    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitLocalStep)
      case (A i' ls f ok ls')

      have  "i' = i" using A by simp

      have f_impl[simp]: "f = toImpl"
        using `currentProc S i' \<triangleq> f` currentProc `i' = i` by auto

      from `f ls = LocalStep ok ls'` `localState S i' \<triangleq> ls`
      have toImpl: "toImpl (ps_store PS, ps_localKnown PS,  cmd \<bind> cmdCont) = LocalStep ok ls'"
        and ls_parts: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto

      from toImpl
      obtain ok' store' cmd'
        where c0: "n (ps_store PS) = (ok', store', cmd')"
          and c1: "ls' = (store', ps_localKnown PS, cmd' \<bind> cmdCont)"
          and c2: "ok = (ok' \<and> finite (dom store'))"
        by (auto simp add: WaitLocalStep split: prod.splits)


      have  cmd_def[simp]: "cmd = impl_language_loops.io.WaitLocalStep n"
        by (simp add: WaitLocalStep)
      have action_def: "action = ALocal Inv"
        using A(7) A(8) by auto

      have Inv: "Inv \<longleftrightarrow> (ok \<and> finite (dom (store')))"
        using A(8) c2 by blast
      have S'_def: "S' = S\<lparr>localState := localState S(i \<mapsto> (store', ps_localKnown PS, cmd' \<bind> cmdCont))\<rparr>"
        by (auto simp add: A(1) c1 `i' = i`)


      define PS' where "PS' \<equiv> PS\<lparr>
      ps_store := store'
    \<rparr>"

      show False
      proof (rule goal, intro exI conjI impI)
        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' cmd' Inv"
          by (auto simp add: step_io_def c0 c2 action_def Inv PS'_def)


        show "proof_state_rel PS' S'" if Inv
          unfolding proof_state_rel_def 
        proof (intro conjI)

          from `Inv` and Inv
          have " ok" and  [simp]: "finite (dom store')"
            by auto

          show "state_wellFormed S'" using \<open>state_wellFormed S'\<close> .


          from proof_state_rel_fact[OF rel] 
          have old_priv: "uid_is_private (ps_i PS) S v" if "v \<in> ps_generatedLocalPrivate PS" for v
            using that by auto


          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.  uid_is_private (ps_i PS') S' v"
          proof (auto simp add: uid_is_private_def PS'_def)
            fix v
            assume a0: "v \<in> ps_generatedLocalPrivate PS"


            show "new_unique_not_in_invocationOp (invocationOp S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)

            show "new_unique_not_in_calls (calls S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show " new_unique_not_in_calls_result (calls S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "new_unique_not_in_invocationRes (invocationRes S') v"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "v \<in> knownIds S' \<Longrightarrow> False"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "generatedIds S' v \<triangleq> ps_i PS"
              using a0 old_priv[OF a0] by (auto simp add: uid_is_private_def S'_def)
            show "new_unique_not_in_other_invocations (ps_i PS) S' v"
            proof (rule new_unique_not_in_other_invocations_maintained)
              show "new_unique_not_in_other_invocations (ps_i PS) S v"
                using old_priv[OF a0] by (auto simp add: uid_is_private_def)
              from step
              show "S ~~ (ps_i PS, action, Inv) \<leadsto>\<^sub>S S'"
                using `i = ps_i PS` by simp
            qed (simp add: action_def)+

          qed

          show "finite (dom (ps_store PS'))"
            by (auto simp add: PS'_def)


          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def)
            show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S'"
              using no_guess
            proof (fuzzy_rule show_invocation_cannot_guess_ids_step)
              show "S ~~ (ps_i PS, action) \<leadsto> S'"
                using step action_def step_s_to_step i_def by blast

              show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
                using action_def by simp
            qed
          qed



        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: i_def S'_def PS'_def  split: option.splits)[1]); fail)+


        show "currentCommand S' i = cmd' \<bind> cmdCont"
          if c0: "Inv"
          by (auto simp add: S'_def)
      qed
    qed
  next
    case (WaitBeginAtomic n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitBeginAtomic)
      case (A S1 i' ls f ls' t Sn Sf vis vis' )

      have [simp]: "ps_localCalls PS = []"
        using A(26) A(8) i_def proof_state_rel_fact(13) proof_state_rel_fact(15) rel by fastforce

      have [simp]: "i' = ps_i PS"
        using A(26) i_def by blast

      have [simp]: "ls' = (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        using A(5) A(6) A(7) WaitBeginAtomic i_def ls toImpl by auto

      have Sn_toImpl[simp]: "currentProc Sn (ps_i PS) \<triangleq> toImpl"
        using toImpl A(16) A(6) by auto





      define PS' where "PS' \<equiv> PS\<lparr>
             calls := calls Sn,
             happensBefore := happensBefore Sn,
             callOrigin := callOrigin Sn,
             transactionOrigin := transactionOrigin Sn(t \<mapsto> i),
             knownIds := knownIds Sn,
             invocationOp := invocationOp Sn,
             invocationRes := invocationRes Sn,
             ps_tx := Some t,
             ps_vis := vis'
          \<rparr>"


      have [simp]: "ps_i PS' = ps_i PS"
        by (simp add: PS'_def)


      show ?thesis
      proof (rule goal, intro exI conjI impI)

        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def `S' = Sf`
        proof (intro conjI)




          show "ps_generatedLocal PS' = {x. generatedIds Sf x \<triangleq> ps_i PS'}"
            apply (auto simp add: PS'_def A )
            using A(11) proof_state_rel_fact(9) rel state_monotonicGrowth_generatedIds apply fastforce
            using A(11) A(26) i_def proof_state_rel_fact(9) rel state_monotonicGrowth_generatedIds_same1 by fastforce

          from proof_state_rel_fact(21)[OF rel]
          show "ps_firstTx PS' =
               (\<nexists>c tx. callOrigin Sf c \<triangleq> tx \<and> transactionOrigin Sf tx \<triangleq> ps_i PS' \<and> transactionStatus Sf tx \<triangleq> Committed)"
            apply (auto simp add: PS'_def A )
             apply (smt A(11) A(13) A(18) A(19) A(26) A(8) \<open>state_wellFormed S\<close> i_def in_dom state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin_i state_wellFormed_ls_visibleCalls_callOrigin transactionConsistent_Committed wellFormed_callOrigin_dom wellFormed_visibleCallsSubsetCalls_h(2) wf_transactionConsistent_noTx)
            by (metis (no_types, lifting) A(11) A(9) \<open>state_wellFormed S\<close> state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin state_monotonicGrowth_transactionStatus2 wellFormed_state_callOrigin_transactionStatus)


          show "\<forall>c. i_callOriginI PS' c \<triangleq> ps_i PS' \<longrightarrow> c \<in> ps_vis PS'"
            apply (auto simp add: PS'_def A  i_callOriginI_h_def split: option.splits)
            using A(13) A(19) A(20) chooseSnapshot_def state_wellFormed_ls_visibleCalls_callOrigin by fastforce

          show "ps_generatedLocalPrivate PS' \<subseteq> ps_generatedLocal PS'"
            apply (auto simp add: PS'_def A )
            using proof_state_rel_fact(23) rel by blast

          from proof_state_rel_fact[OF rel]
          have uid_private: "uid_is_private (ps_i PS) S v"
            if "v \<in> ps_generatedLocalPrivate PS"
            for v
            using that by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
               uid_is_private (ps_i PS') Sf v"
          proof (rule ballI)
            fix v
            assume v_priv: "v \<in> ps_generatedLocalPrivate PS'"

            have  "uid_is_private i' S v"
            proof (fuzzy_rule uid_private)
              show "v \<in> ps_generatedLocalPrivate PS"
                using v_priv by (auto simp add: PS'_def)
              show "ps_i PS = i'" by simp
            qed


            have "uid_is_private i S' v"
            proof (rule uip)
              show "uid_is_private i S v"
                using `i = i'` \<open>uid_is_private i' S v\<close> by blast

              show "v \<notin> action_outputs action"
                using `action = ABeginAtomic t vis'` by simp
            qed


            from this
            show "uid_is_private (ps_i PS') Sf v"
              by (simp add: A(4) i_def)
          qed 

          have toImpl_ba: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = BeginAtomic (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
            using toImpl `f ls = BeginAtomic ls'` `currentProc S i' \<triangleq> f` `localState S i' \<triangleq> ls` i_def ls
            by auto

          have ls_Sf: "localState Sf (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
            by (auto simp add: A)



          show "ps_generatedLocal PS' \<subseteq> ps_localKnown PS'"
            using \<open>ps_generatedLocal PS \<subseteq> ps_localKnown PS\<close> PS'_def by auto


          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') Sf"
          proof (simp add: PS'_def A(4)[symmetric])

            have "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  S"
              by (simp add: no_guess)

            from `state_monotonicGrowth i' S Sn`
            obtain tr
              where "state_wellFormed S"
                and "S ~~ tr \<leadsto>* Sn" 
                and "\<forall>(i'',a)\<in>set tr. i'' \<noteq> i'"
                and "\<forall>i. (i, ACrash) \<notin> set tr"
              by (auto simp add: state_monotonicGrowth_def)


            from no_guess `S ~~ tr \<leadsto>* Sn`
            have "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  Sn"
            proof (rule show_invocation_cannot_guess_ids_steps_other)
              show "\<forall>(i', a)\<in>set tr. i' \<noteq> ps_i PS"
                using A(26) \<open>\<forall>(i'', a)\<in>set tr. i'' \<noteq> i'\<close> i_def by blast
            qed

            have ls_split: "ls = (fst ls, fst (snd ls), snd (snd ls))"
              by force

            have " Sn ~~ (ps_i PS, ABeginAtomic t vis' ) \<leadsto> S'"
              using A ls_split by (auto simp add: step.simps state_ext intro!: exI[where x=Sn] exI HOL.ext)

            from `invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS)  Sn`
              and `Sn ~~ (ps_i PS, ABeginAtomic t vis' ) \<leadsto> S'`
            show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S'"
            proof (fuzzy_rule show_invocation_cannot_guess_ids_step)
              show "ps_localKnown PS \<union> action_inputs (ABeginAtomic t vis') = ps_localKnown PS"
                by simp
            qed
          qed

        qed ((insert A, (auto simp add: PS'_def sorted_by_empty)[1]); fail)+



        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' n Inv"
        proof (auto simp add: step_io_def `cmd = impl_language_loops.io.WaitBeginAtomic n`, intro exI conjI)

          show "proof_state_wellFormed PS'"
          proof (rule show_proof_state_wellFormed)
            show "state_wellFormed Sf"
              using A by auto

            show "proof_state_rel PS' Sf"
              using A(4) \<open>proof_state_rel PS' S'\<close> by blast
          qed



          show "Inv"
            using A by simp

          show "action = ABeginAtomic t vis'"
            using A by simp

          have [simp]: "(transactionOrigin Sn)(t := None) = transactionOrigin Sn"
            using A(23) by auto



          have invContext_simp: "invariantContext.truncate (PS'\<lparr>transactionOrigin := ((transactionOrigin Sn)(t \<mapsto> ps_i PS))(t := None)\<rparr>)
          = invContext Sn"
            apply (auto simp add: invContextH_def PS'_def A invariantContext.defs committedCalls_allCommitted restrict_relation_def)
               apply (meson A(13) option.exhaust wellFormed_happensBefore_calls_l)
              apply (meson A(13) option.exhaust wellFormed_happensBefore_calls_r)
             apply (metis A(13) restrict_map_noop2 wellFormed_callOrigin_dom)
            by (smt A(13) A(2) Collect_cong domD dom_def mem_Collect_eq option.distinct(1) restrict_map_noop2 transactionStatus.exhaust wf_transaction_status_iff_origin)

          show "invariant (prog S)
         (invariantContext.truncate
           (PS'\<lparr>transactionOrigin := ((transactionOrigin Sn)(t \<mapsto> ps_i PS))(t := None)\<rparr>))"
            unfolding invContext_simp
            using A(10) A(12) by auto

          show "((transactionOrigin Sn)(t \<mapsto> ps_i PS)) t \<triangleq> ps_i PS"
            by simp

          show "PS' = PS\<lparr>
            calls := calls Sn,
            happensBefore := happensBefore Sn, 
            callOrigin := callOrigin Sn,
            transactionOrigin := transactionOrigin Sn(t \<mapsto> ps_i PS), 
            knownIds := knownIds Sn,
            invocationOp := invocationOp Sn,
            invocationRes := invocationRes Sn,
            ps_tx := Some t, 
            ps_vis := vis'\<rparr>"
            by (auto simp add: PS'_def i_def)

          show " ps_growing PS PS'"
            unfolding ps_growing_def by simp

          show "transactionOrigin PS t = None"
            using A(9) \<open>state_wellFormed S\<close> proof_state_rel_fact(5) rel wf_transaction_status_iff_origin by fastforce


        qed

        show "currentCommand S' i = n \<bind> cmdCont"
          by (auto simp add: A)

      qed

    qed
  next
    case (WaitEndAtomic n)

    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitEndAtomic)
      case (A i' ls f ls' t S'' valid)


      have  "i' = i" using A by simp
      hence "i' = ps_i PS"
        using i_def by blast


      have f_impl[simp]: "f = toImpl"
        using `currentProc S i' \<triangleq> f` currentProc `i' = i` by auto

      from `f ls = EndAtomic ls'` `localState S i' \<triangleq> ls`
      have toImpl: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = EndAtomic ls'"
        and ls_parts: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto




      from toImpl
      have ls'_def: "ls' = (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        by (auto simp add: WaitEndAtomic)

      have S''_def: "S'' = S
    \<lparr>localState := localState S(i' \<mapsto> ls'), currentTransaction := (currentTransaction S)(i' := None),
       transactionStatus := transactionStatus S(t \<mapsto> Committed)\<rparr>"
        using A by auto

      have [simp]: "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, n \<bind> cmdCont)"
        by (auto simp add: `S' = S''` S''_def `i' = ps_i PS` ls'_def)


      define PS' where "PS' \<equiv> PS\<lparr>
        happensBefore := updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS),
        callOrigin := map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS)),
        ps_tx := None,
        ps_localCalls := [],
        ps_vis := ps_vis PS \<union> set (ps_localCalls PS),
        ps_firstTx := ps_firstTx PS \<and> ps_localCalls PS = []
      \<rparr>"


      show False
      proof (rule goal, intro exI conjI impI)

        show "currentCommand S' i = n \<bind> cmdCont"
          by (simp add: S''_def `S' = S''` `i = i'` ls'_def)

        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)
          show "state_wellFormed S'"
            by (simp add: \<open>state_wellFormed S'\<close>)

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
            by (simp add: PS'_def)

          have [simp]: "ps_tx PS \<triangleq> t"
            using A(5) \<open>i' = ps_i PS\<close> proof_state_rel_fact(13) rel by fastforce

          have no_other_uncommitted: "transactionStatus S tx \<noteq> Some Uncommitted" if "t \<noteq> tx" for tx
            by (rule proof_state_rel_fact(14)[OF rel, rule_format], simp add: that)




          show "\<forall>tx'. ps_tx PS' \<noteq> Some tx' \<longrightarrow> transactionStatus S' tx' \<noteq> Some Uncommitted"
            apply (simp add: PS'_def  `S' = S''` S''_def)
            using A(5) \<open>i' = ps_i PS\<close> proof_state_rel_fact(13) proof_state_rel_fact(14) rel by force

          from proof_state_rel_fact(21)[OF rel]
          show "ps_firstTx PS' =
           (\<nexists>c tx. callOrigin S' c \<triangleq> tx \<and> transactionOrigin S' tx \<triangleq> ps_i PS' \<and> transactionStatus S' tx \<triangleq> Committed)"
            using proof_state_rel_fact(15)[OF rel]
            apply (auto simp add: PS'_def  `S' = S''` S''_def)
            using A(5) \<open>i' = ps_i PS\<close> \<open>state_wellFormed S\<close> state_wellFormed_current_transaction_origin by blast

          show "\<forall>c. i_callOriginI PS' c \<triangleq> ps_i PS' \<longrightarrow> c \<in> ps_vis PS'"
            apply (auto simp add: PS'_def)
            by (metis i_callOriginI_h_update_to4 proof_state_rel_fact(22) rel)

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.  uid_is_private (ps_i PS') S' v"

          proof (auto simp add: PS'_def )
            fix v
            assume a0: "v \<in> ps_generatedLocalPrivate PS"

            have "uid_is_private (ps_i PS) S v"
              using a0 proof_state_rel_fact(24) rel by blast

            show "uid_is_private (ps_i PS) S' v"
            proof (fuzzy_rule uip)
              show "uid_is_private i S v"
                by (simp add: \<open>uid_is_private (ps_i PS) S v\<close> i_def)
              show "v \<notin> action_outputs action"
                by (simp add: A(11)) 
              show "i = ps_i PS"
                by (simp add: i_def) 
            qed
          qed

          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(11) i_def local.step step_s_to_step by blast
            show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
              using `action = AEndAtomic` by simp
          qed



        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: sorted_by_empty i_def S''_def PS'_def `S' = S''` `i = i'` `i' = ps_i PS`  split: option.splits)[1]); fail)+

        have "\<And>t. transactionStatus S'' t \<noteq> Some Uncommitted"
          apply (auto simp add: S''_def)
          using A(5) \<open>i' = ps_i PS\<close> proof_state_rel_fact(13) proof_state_rel_fact(14) rel by fastforce



        have committed_all: "committedCallsH (callOrigin S) (transactionStatus S(t \<mapsto> Committed))
          = dom (calls S)"
          apply (auto simp add: committedCallsH_def isCommittedH_def)
          using \<open>state_wellFormed S\<close> wellFormed_callOrigin_dom apply fastforce
            apply (simp add: \<open>state_wellFormed S\<close> wellFormed_callOrigin_dom2)
          using A(5) \<open>state_wellFormed S\<close> wellFormed_currentTransaction_unique_h(2) apply fastforce
          by (smt A(5) \<open>state_wellFormed S\<close> not_None_eq not_uncommitted_cases proof_state_rel_fact(14) rel wellFormed_callOrigin_dom3 wellFormed_currentTransaction_unique_h(2) wf_no_transactionStatus_origin_for_nothing)



        have context_Same: "invariantContext.truncate PS' = invContext S''"
          apply (auto simp add: invContext_same_allCommitted'[OF `state_wellFormed S''` `\<And>t. transactionStatus S'' t \<noteq> Some Uncommitted`])
          by (auto simp add: PS'_def S''_def invariantContext.defs proof_state_rel_fact[OF rel])


        have prog_same: "prog S'' = prog S"
          using A(1) local.step steps_s_single unchangedProg by blast

        have inv: "Inv  \<longleftrightarrow> invariant (prog S) (invariantContext.truncate PS')"
          by (simp add: context_Same `Inv = valid` `valid = invariant_all S''` prog_same)


        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' n Inv"
          by (clarsimp simp add: step_io_def WaitEndAtomic PS'_def inv A(11))
      qed
    qed


  next
    case (WaitNewId P n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitNewId)
      case (A i' ls f ls' uid uidv ls'')

      have S'_def: "S' = S\<lparr>localState := localState S(i' \<mapsto> ls''), generatedIds := generatedIds S(uid \<mapsto> i')\<rparr>"
        using A by simp

      have S'_wf: "state_wellFormed S'"
        by (simp add: \<open>state_wellFormed S'\<close>)

      have "i' = ps_i PS"
        using A(10) i_def by auto


      have ls''_def: "ls'' = (ps_store PS, ps_localKnown PS \<union> uniqueIds uidv, n uidv \<bind> cmdCont)"
        by (smt A(10) A(2) A(3) A(4) A(7) WaitNewId i_def impl_language_loops.bind.simps(4) toImpl.simps(4) localAction.inject(4) ls option.sel option.simps(3) toImpl)

      define cmd' where "cmd' \<equiv> n uidv"


      define PS' where "PS' = PS\<lparr> 
          ps_localKnown := ps_localKnown PS \<union> {uid},
          ps_generatedLocal := ps_generatedLocal PS \<union> {uid},
          ps_generatedLocalPrivate := ps_generatedLocalPrivate PS \<union> {uid}
        \<rparr>"




      show False
      proof (rule goal, intro exI conjI impI)
        show "currentCommand S' i = cmd' \<bind> cmdCont"
          by (simp add: S'_def ls''_def cmd'_def `i = i'`)


        have uid_priv: "uid_is_private (ps_i PS) S' uid"
          unfolding uid_is_private_def
        proof (intro conjI)
          show "new_unique_not_in_invocationOp (invocationOp S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_invocationOp_def prog_wf wf_onlyGeneratedIdsInInvocationOps by (auto simp add: A, blast)
          show "new_unique_not_in_calls (calls S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_calls_def prog_wf wf_onlyGeneratedIdsInCalls by (auto simp add: A, blast)
          show "new_unique_not_in_calls_result (calls S') uid"
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_calls_result_def prog_wf wf_onlyGeneratedIdsInCallResults by (auto simp add: A, blast)
          show "new_unique_not_in_invocationRes (invocationRes S') uid"
            apply (auto simp add: A)
            using A(5) A(8) \<open>state_wellFormed S\<close> new_unique_not_in_invocationRes_def prog_wf wf_onlyGeneratedIdsInInvocationRes by blast
          show "uid \<notin> knownIds S'"
            apply (auto simp add: A)
            using A(5) A(8) \<open>state_wellFormed S\<close> prog_wf wf_onlyGeneratedIdsInKnownIds by blast
          show "generatedIds S' uid \<triangleq> ps_i PS"
            using \<open>i' = ps_i PS\<close> by (auto simp add: A)
          have "new_unique_not_in_other_invocations (ps_i PS) S uid"
          proof (rule wf_invocation_cannot_guess_ids_not_generated)
            show "state_wellFormed S"
              using \<open>state_wellFormed S\<close> by auto
            show "program_wellFormed (prog S)"
              by (simp add: prog_wf)
            show "generatedIds S uid = None"
              by (simp add: A(5))
          qed
          thus "new_unique_not_in_other_invocations (ps_i PS) S' uid"
            using A(11) i_def local.step new_unique_not_in_other_invocations_maintained by blast
        qed


        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)
          show "state_wellFormed S'"
            using S'_wf by simp

          show "ps_generatedLocal PS' = {x. generatedIds S' x \<triangleq> ps_i PS'}"
            apply (auto simp add: PS'_def S'_def `i' = ps_i PS`)
            using proof_state_rel_fact(9) rel apply auto[1]
            using proof_state_rel_fact(9) rel by auto

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
            by (auto simp add: PS'_def S'_def `i' = ps_i PS` ls''_def `uniqueIds uidv = {uid}`)





          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
           uid_is_private (ps_i PS') S' v"
          proof (auto simp add: PS'_def)
            show "uid_is_private (ps_i PS) S' uid"
              using uid_priv by blast
            show "uid_is_private (ps_i PS) S' v" if "v \<in> ps_generatedLocalPrivate PS" for v
              using A(11) i_def proof_state_rel_fact(24) rel that uip by auto
          qed



          have ls''_def: "ls'' = (the (localState S' (ps_i PS)))"
            by (auto simp add: S'_def \<open>i' = ps_i PS\<close>)

          show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
          proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(11) i_def local.step step_s_to_step by blast
            show "ps_localKnown PS \<union> action_inputs action = insert uid (ps_localKnown PS)"
              using `action = ANewId uidv` `uniqueIds uidv = {uid}` by auto
          qed




        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: i_def  S'_def PS'_def  split: option.splits)[1]); fail)+



        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' cmd' Inv"
        proof (auto simp add: step_io_def WaitNewId, intro exI conjI)
          show "action = ANewId uidv"
            by (simp add: A(11))

          from `f ls = NewId ls'`
          have "toImpl ls = NewId ls'"
            using A(3) \<open>i' = ps_i PS\<close> toImpl by auto


          have ls_def: "ls = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)"
            using A(10) A(2) ls by auto



          show "cmd' = n uidv"
            using cmd'_def by simp




          show "uniqueIds uidv = {uid}"
            by (simp add: A(6))

          show "uid \<notin> ps_generatedLocal PS"
            using A(5) proof_state_rel_fact(9) rel by fastforce

          from uid_is_private'_implies[OF uid_priv]
          have h: " uid_is_private' (ps_i PS) (calls S') (invocationOp S') (invocationRes S') (knownIds S') uid" .

          have "uid_is_private' (ps_i PS) (calls PS) (invocationOp PS) (invocationRes PS) (knownIds PS) uid"
            using h
            by (auto simp add: S'_def  proof_state_rel_fact[OF rel])

          thus "uid_fresh uid PS"
            by (auto simp add: uid_fresh_def)

          show "PS' = PS
                \<lparr>  ps_localKnown := insert uid (ps_localKnown PS),
                   ps_generatedLocal := insert uid (ps_generatedLocal PS),
                   ps_generatedLocalPrivate := insert uid (ps_generatedLocalPrivate PS)\<rparr>"
            by (auto simp add: PS'_def)
          show "Inv"
            by (simp add: A(12))
        qed
      qed
    qed

  next
    case (WaitDbOperation oper n)

    show False 
    proof (cases "\<exists>c Op res. action = ADbOp c Op res")
      case False
      hence a: "action \<noteq> ADbOp c Op res" for c Op res
        by blast

\<comment> \<open>TODO move to utils\<close>
      have if_simp1: "((if c then x else y) = z) \<longleftrightarrow> (if c then x = z else y = z)" for c and  x y z :: "('ls, 'operation, 'any) localAction"
        by auto

      have if_simp2: "(if c then False else y) \<longleftrightarrow> \<not>c \<and> y" for c y
        by auto


      show False
        apply (rule step_s.cases[OF step];     remove_first_equality)
              apply (insert a cmd_prefix )
              apply (auto simp add: WaitDbOperation if_simp1  if_simp2 split: prod.splits cong: if_cong)
        apply (rule ccontr)
      proof (goal_cases A)
        case (A store locakKnown cmd' x)

        define PS' where "PS' = PS"

        show False
        proof (rule goal, intro exI conjI impI)
          show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' cmd Inv"
            using `cmd = impl_language_loops.io.WaitDbOperation oper n`
              `x \<in> uniqueIds oper` `x \<notin> ps_localKnown PS`
            by (auto simp add: step_io_def `\<not> Inv` PS'_def)

        qed (simp add: `\<not>Inv`)+
      qed
    next
      case True
      from this
      obtain c Op res where "action = ADbOp c Op res"
        by blast

      have validUids: "uniqueIds oper \<subseteq> ps_localKnown PS"
        using step `action = ADbOp c Op res` `cmd = impl_language_loops.io.WaitDbOperation oper n`
        by (auto simp add: step_s.simps split: if_splits)


      show False
      proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitDbOperation validUids)
        case (A i' ls f Op ls' t c res vis)


        have [simp]: "i = i'" using A by simp
        have [simp]: "ps_i PS = i'"
          using i_def by auto 

        have Inv
          by (simp add: A(12))

        have S'_def: "S' = S
        \<lparr>localState := localState S(i' \<mapsto> ls' res), calls := calls S(c \<mapsto> Call Op res),
           callOrigin := callOrigin S(c \<mapsto> t), visibleCalls := visibleCalls S(i' \<mapsto> vis \<union> {c}),
           happensBefore := happensBefore S \<union> vis \<times> {c}\<rparr>"
          using A by simp

        have [simp]: "oper = Op"
          using A WaitDbOperation i_def ls toImpl `uniqueIds oper \<subseteq> ps_localKnown PS` by auto


        define PS' where "PS' \<equiv> PS\<lparr> 
            ps_localKnown := ps_localKnown PS \<union> uniqueIds res,
            ps_generatedLocalPrivate := ps_generatedLocalPrivate PS - uniqueIds Op,
            calls := (calls PS)(c \<mapsto> Call oper res),
            ps_localCalls := ps_localCalls PS @ [c]
      \<rparr>"

        show False
        proof (rule goal, intro exI conjI impI)

          show "currentCommand S' i = n res \<bind> cmdCont"
            apply (simp add: S'_def)
            using A(2) A(3) A(4) WaitDbOperation i_def ls toImpl validUids by auto

          have vis_def: "vis = ps_vis PS \<union> set (ps_localCalls PS)"
            by (metis A(10) A(8) i_def option.inject proof_state_rel_fact(12) rel)

          have t_def: "t = the (ps_tx PS)"
            by (metis A(10) A(5) i_def option.sel proof_state_rel_fact(13) rel)

          have ps_tx: "ps_tx PS \<triangleq> t"
            by (metis A(10) A(5) i_def proof_state_rel_fact(13) rel)



          show "proof_state_rel PS' S'"
            unfolding proof_state_rel_def 
          proof (intro conjI)

            show "state_wellFormed S'"
              by (simp add: \<open>state_wellFormed S'\<close>)

            show "happensBefore S' = updateHb (happensBefore PS') (ps_vis PS') (ps_localCalls PS')"
              by (auto simp add: vis_def proof_state_rel_fact(3)[OF rel] updateHb_simp1 S'_def PS'_def in_sequence_append in_sequence_cons updateHb_cases updateHb_chain)


            show "callOrigin S' = map_update_all (callOrigin PS') (ps_localCalls PS') (the (ps_tx PS'))"
              by (auto simp add: S'_def PS'_def map_update_all_get t_def proof_state_rel_fact(4)[OF rel] intro!: HOL.ext)


            show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_localKnown PS', ps_ls)"
              using A(2) A(3) A(4) WaitDbOperation ls toImpl validUids by (auto simp add: S'_def PS'_def)

            show "visibleCalls S' (ps_i PS') \<triangleq> (ps_vis PS' \<union> set (ps_localCalls PS'))"
              by (auto simp add: S'_def PS'_def vis_def)

            show "case ps_tx PS' of None \<Rightarrow> ps_localCalls PS' = [] | Some tx' \<Rightarrow> set (ps_localCalls PS') = {c. callOrigin S' c \<triangleq> tx'}"
              apply (auto simp add: proof_state_rel_fact(4)[OF rel] map_update_all_get ps_tx S'_def PS'_def split: option.splits)
              using proof_state_rel_fact(15)[OF rel]
              by (metis (mono_tags, lifting) map_update_all_get mem_Collect_eq option.simps(5) proof_state_rel_fact(4) ps_tx rel)

            have sorted: "sorted_by (happensBefore S) (ps_localCalls PS)"
              by (simp add: proof_state_rel_fact(16) rel)

            have "c \<notin> set (ps_localCalls PS)"
              using A(6) A(8) \<open>state_wellFormed S\<close> vis_def wellFormed_visibleCallsSubsetCalls2 by auto


            show "sorted_by (happensBefore S') (ps_localCalls PS')"
            proof (auto simp add: S'_def PS'_def sorted_by_append_iff sorted_by_single)

              show "sorted_by (happensBefore S \<union> vis \<times> {c}) (ps_localCalls PS)"
                using sorted \<open>c \<notin> set (ps_localCalls PS)\<close> 
                by (auto simp add: sorted_by_def)
              show "\<And>x. \<lbrakk>x \<in> set (ps_localCalls PS); (c, x) \<in> happensBefore S\<rbrakk> \<Longrightarrow> False"
                using A(6) \<open>state_wellFormed S\<close> wellFormed_happensBefore_calls_l by blast
              show "\<lbrakk>c \<in> set (ps_localCalls PS); c \<in> vis\<rbrakk> \<Longrightarrow> False"
                using \<open>c \<notin> set (ps_localCalls PS)\<close> by blast
            qed

            have "c \<notin> ps_vis PS"
              using A(6) A(8) \<open>state_wellFormed S\<close> vis_def wellFormed_visibleCallsSubsetCalls2 by auto


            show "ps_vis PS' \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_fact(17)[OF rel]
              by (auto simp add: PS'_def `c \<notin> ps_vis PS`)

            have co_c: "callOrigin PS c = None"
              by (metis (no_types, lifting) A(6) \<open>c \<notin> set (ps_localCalls PS)\<close> \<open>state_wellFormed S\<close> map_update_all_get proof_state_rel_fact(4) rel wellFormed_callOrigin_dom3) 


            show "dom (callOrigin PS') \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_fact(18)[OF rel]
              by (auto simp add: PS'_def co_c)

            have co_hb: "c \<notin> Field (happensBefore PS)"
              by (metis A(6) Field_Un Un_iff \<open>state_wellFormed S\<close> proof_state_rel_fact(3) rel updateHb_simp_split wellFormed_happensBefore_Field)


            show "Field (happensBefore PS') \<inter> set (ps_localCalls PS') = {}"
              using proof_state_rel_fact(19)[OF rel]
              by (auto simp add: PS'_def co_hb)

            show "distinct (ps_localCalls PS')"
              using proof_state_rel_fact(20)[OF rel]
              by (auto simp add: PS'_def \<open>c \<notin> set (ps_localCalls PS)\<close> )

            show "ps_firstTx PS' =
            (\<nexists>c tx. callOrigin S' c \<triangleq> tx \<and> transactionOrigin S' tx \<triangleq> ps_i PS' \<and> transactionStatus S' tx \<triangleq> Committed)"
              apply ( simp add: PS'_def S'_def)
              apply safe
              using A(5) \<open>state_wellFormed S\<close> not_uncommitted_cases wellFormed_currentTransactionUncommitted apply blast
              using A(10) i_def proof_state_rel_fact(21) rel apply blast
              by (metis A(6) \<open>ps_i PS = i'\<close> \<open>state_wellFormed S\<close> option.distinct(1) proof_state_rel_fact(21) rel wellFormed_callOrigin_dom3)


            have  prog_wf': "program_wellFormed (prog S')"
              by (metis local.step prog_wf steps_s_empty steps_s_step unchangedProg)

            hence "invocations_cannot_guess_ids (prog S')" 
              and "queries_cannot_guess_ids (querySpec (prog S'))"
              by (auto simp add: program_wellFormed_def)


            have toImpl_db: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = DbOperation Op ls'"
              using toImpl `currentProc S i' \<triangleq> f` `f ls = DbOperation Op ls'` `localState S i' \<triangleq> ls` ls by auto



            have "localState S' i' \<triangleq> ls' res" 
              by (auto simp add: S'_def )


            show "invocation_cannot_guess_ids (ps_localKnown PS') (ps_i PS') S'"
            proof (simp add: PS'_def, use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
              show "S ~~ (i', action) \<leadsto> S'"
                using A(10) A(11) local.step step_s_to_step by blast
              show "ps_i PS = i'"
                by simp
              show "action_inputs action = uniqueIds res"
                using ` action = ADbOp c Op res` by auto
            qed

            from use_invocation_cannot_guess_ids_return[OF no_guess]
            have "uniqueIds Op \<subseteq> ps_localKnown PS"
              by (metis A(11) action.distinct(33) action.distinct(53) i_def local.step no_guess step_s_to_step use_invocation_cannot_guess_ids_dbop)

            from prog_wf
            have "query_cannot_guess_ids (uniqueIds opr) (querySpec (prog S) opr)" for opr
              by (auto simp add: program_wellFormed_def queries_cannot_guess_ids_def)

            hence qcgi: "query_cannot_guess_ids (uniqueIds Op) (querySpec (prog S) Op)" .

            from qcgi[simplified query_cannot_guess_ids_def, rule_format, OF `querySpec (prog S) Op (getContext S i') res`]
            have " uniqueIds res
              \<subseteq> uniqueIds Op \<union> \<Union> {x. \<exists>cId c. x = uniqueIds (call_operation c) \<and> calls (getContext S i') cId \<triangleq> c}"
              .

            hence uniqueIdsRes: "\<exists>cId c. calls (getContext S i') cId \<triangleq> c \<and> x \<in> uniqueIds (call_operation c)" 
              if "x \<in> uniqueIds res" 
                and "x \<notin> uniqueIds Op"
              for x
              using that
              using A(7) qcgi by fastforce 


            show " \<forall>v\<in>ps_generatedLocalPrivate PS'.
            uid_is_private (ps_i PS') S' v"
              using A(10) A(11) action_outputs.simps(5) i_def proof_state_rel_def rel uip by (auto simp add: PS'_def, blast)


          qed ((insert proof_state_rel_fact[OF rel], (auto simp add: PS'_def S'_def sorted_by_empty)[1]); fail)+


          show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' (n res) Inv"
          proof (auto simp add: step_io_def WaitDbOperation; (intro exI conjI)?)

            show "ps_tx PS \<triangleq> t"
              by (simp add: ps_tx)

            show "calls PS c = None"
              using A(6) proof_state_rel_fact(2) rel by fastforce

            have  vis: "visibleCalls S i' \<triangleq> (ps_vis PS \<union> set (ps_localCalls PS))"
              using A(8) vis_def by blast

            have ctxt_same: "(getContextH (calls S) (happensBefore S) (Some (ps_vis PS \<union> set (ps_localCalls PS))))
            = (getContextH (calls PS) (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
                  (Some (ps_vis PS \<union> set (ps_localCalls PS))))"
              by (auto simp add: getContextH_def proof_state_rel_fact[OF rel])

            from `querySpec (prog S) Op (getContext S i') res`
            show "querySpec (prog S) Op
         (getContextH (calls PS) (updateHb (happensBefore PS) (ps_vis PS) (ps_localCalls PS))
           (Some (ps_vis PS \<union> set (ps_localCalls PS))))
           res" 
              by (auto simp add: vis ctxt_same)

            show "uniqueIds Op \<subseteq> ps_localKnown PS"
              using validUids by auto



          qed (auto simp add: PS'_def \<open>Inv\<close>)
        qed
      qed
    qed
  next
    case (WaitReturn n)
    with cm_no_return 
    show False
      by auto
  next
    case (Loop body n)
    show False
    proof (cmd_step_cases step: step insert: cmd_prefix simps: Loop)
      case (A i' ls f ok ls')

      have S'_def: "S' = S\<lparr>localState := localState S(i' \<mapsto> ls')\<rparr>" using A by simp

      have "Inv"
        using A(2) A(3) A(4) A(6) A(8) Loop \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> i_def toImpl by auto


      show False
      proof (rule goal, intro exI conjI impI)

        have [simp]: "ps_i PS = i'"
          using A(6) i_def by auto

        


        have toImpl_ls: "toImpl ls = LocalStep ok ls'"
          using `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def)

        have toImpl1: "toImpl (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont) = LocalStep ok ls'"
          using A(2) \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> toImpl_ls by auto


        have ls_S': "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, from_V body \<bind> (\<lambda>r. if r then n \<bind> cmdCont else Loop body (n \<bind> cmdCont)))"

          using \<open>the (localState S (ps_i PS)) = (ps_store PS, ps_localKnown PS, cmd \<bind> cmdCont)\<close> `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def )
         


        hence ls_S': "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) \<bind> cmdCont)"
          apply auto
          by (metis (full_types, hide_lams) impl_language_loops.bind.simps(7))


        show "proof_state_rel PS S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)

          show "state_wellFormed S'"
            by (simp add: \<open>state_wellFormed S'\<close>)

          show " \<exists>ps_ls. localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_localKnown PS, ps_ls)"
            using ls_S' by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS. uid_is_private (ps_i PS) S' v"
            using A(7) proof_state_rel_fact(24) rel uip' by fastforce


          show "invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S'"
          proof (use no_guess in \<open>fuzzy_rule show_invocation_cannot_guess_ids_step\<close>)
            show "S ~~ (ps_i PS, action) \<leadsto> S'"
              using A(7) i_def local.step step_s_to_step by blast

            show "ps_localKnown PS \<union> action_inputs action = ps_localKnown PS"
              using ` action = ALocal ok` by auto
          qed


        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: i_def S'_def   split: option.splits)[1]); fail)+


        show "currentCommand S' i = (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) \<bind> cmdCont"
          using i_def ls_S' by auto

        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS
         (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) Inv"
          by (auto simp add: step_io_def Loop `Inv`)


      qed
    qed
  qed
qed

lemma step_io_same_i:
  assumes "step_io progInv qrySpec S cmd action S' cmd' Inv"
  shows "ps_i S' = ps_i S"
  using assms  by ( auto simp add: step_io_def split: io.splits if_splits)


definition proof_state_wellFormed' :: "('proc, 'any, 'operation) proof_state \<Rightarrow> bool" where 
"proof_state_wellFormed' S \<equiv> 
  finite (dom (ps_store S))
"

lemma step_io_wf_maintained:
  assumes wf: "proof_state_wellFormed' S"
    and step: "step_io progInv qrySpec S cmd action S' cmd' True"
  shows "proof_state_wellFormed' S'"
proof (cases cmd)
case (WaitLocalStep x1)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
  case (WaitBeginAtomic x2)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
  case (WaitEndAtomic x3)
  then show ?thesis
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
  case (WaitNewId x41 x42)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
  case (WaitDbOperation x51 x52)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
case (WaitReturn x6)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
next
  case (Loop x71 x72)
  then show ?thesis 
    using wf step by (auto simp add: step_io_def proof_state_wellFormed'_def)
qed

lemma steps_io_wf_maintained:
  assumes wf: "proof_state_wellFormed' S"
    and steps: "steps_io progInv qrySpec S cmd S' res"
    and ok: "res \<noteq> None"
  shows "proof_state_wellFormed' S'"
  using steps wf ok proof (induct)
  case (steps_io_final  S res)
  then show ?case 
    by auto
next
  case (steps_io_error  S cmd action S' cmd')
  then show ?case 
    by auto
next
  case (steps_io_step S cmd action S' cmd' S'' res)
  then show ?case 
    using step_io_wf_maintained by blast
qed

lemma steps_io_wf_maintained':
  assumes wf: "proof_state_wellFormed' S"
    and steps: "steps_io progInv qrySpec S cmd S' (Some res)"
  shows "proof_state_wellFormed' S'"
  using local.wf steps steps_io_wf_maintained by fastforce


lemma proof_state_wellFormed_implies:
 "proof_state_wellFormed PS \<Longrightarrow> proof_state_wellFormed' PS"
  by (auto simp add: proof_state_wellFormed_def proof_state_rel_def  proof_state_wellFormed'_def)


text \<open>We now show that all errors in an execution of the single-invocation semantics 
can be simulated by the steps-io approximation.
Thus it is sufficient to show that the steps-io approximation is correct.

\<close>

definition invariant_return :: "
  (('proc::valueType, 'operation::valueType, 'any::valueType) invariantContext \<Rightarrow> bool) 
\<Rightarrow> ('proc, 'any, 'operation) proof_state 
\<Rightarrow> 'any option
\<Rightarrow> bool" where
"invariant_return progInv PS resO \<equiv>
  \<exists>res. resO \<triangleq> res 
      \<and> uniqueIds res \<subseteq> ps_localKnown PS
      \<and> progInv (invariantContext.truncate (PS\<lparr> invocationRes := invocationRes PS(ps_i PS \<mapsto> res), knownIds := knownIds PS \<union> uniqueIds res  \<rparr>))"
\<comment> \<open>TODO maybe add: there is no current transaction. \<close>

lemma steps_nonempty_first:
  assumes "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
    and "tr \<noteq> []"
  shows "\<exists>S' a. S ~~ (i, a) \<leadsto>\<^sub>S S'"
  using assms proof (induct rule: step_s_induct)
  case initial
  then show ?case by auto
next
  case (step tr S' a S'')
  show ?case
  proof (cases "tr")
    case Nil
    show ?thesis 
    proof (intro exI)
      show "S ~~ (i, a) \<leadsto>\<^sub>S S''"
        using step Nil by (auto simp add: steps_s_empty)
    qed
  next
    case (Cons a list)
    then show ?thesis
      using step by auto
  qed
qed



lemma steps_io_simulation:
  fixes PS :: "('proc::valueType, 'any::valueType, 'operation::valueType) proof_state"
  assumes rel: "proof_state_rel PS S"
    and steps: "S ~~ (i, tr) \<leadsto>\<^sub>S* S'"
    and i_def: "i = ps_i PS"
    and not_correct: "\<not>traceCorrect_s tr"
    and prog_wf: "program_wellFormed (prog S)"
    and cmd_def: "cmd = currentCommand S i"
  shows "\<exists>PS' res. steps_io (invariant (prog S)) (querySpec (prog S)) PS cmd  PS' res
               \<and> (res = None \<or> \<not>invariant_return (invariant (prog S))  PS' res)
               " \<comment> \<open>TODO or final state after return that does not satisfy invariant.\<close>
  using rel steps i_def not_correct prog_wf cmd_def proof (induct "length tr" arbitrary: S' tr PS S cmd)
  case (0 tr S' PS S cmd)
  hence "tr = []"
    by auto
  hence "traceCorrect_s tr"
    by (simp add: traceCorrect_s_def)
  with `\<not>traceCorrect_s tr` 
  show ?case by auto
next
  case (Suc k tr S' PS S cmd)
  from this obtain action ok tr' 
    where tr_def: "tr = ((action, ok)#tr')"
    by (metis length_Suc_conv prod.collapse)

  with `S ~~ (i, tr) \<leadsto>\<^sub>S* S'`
  obtain S1 
    where first_step:"S ~~ (i, action, ok) \<leadsto>\<^sub>S S1" 
      and other_steps:"S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'"
    using steps_s_cons_simp by blast

  have "prog S1 = prog S"
    using unchangedProg1[OF first_step]
    by simp

  show ?case
  proof (cases "\<exists>res. cmd = WaitReturn res")
    case True
    from this obtain res
      where "cmd = WaitReturn res"
      by blast

    have "currentProc S i \<triangleq> toImpl"
      by (simp add: Suc.prems(1) Suc.prems(3) proof_state_rel_fact(11))


    have "ps_i PS = i"
      by (simp add: Suc.prems(3))


    have wf: "state_wellFormed S"
      using proof_state_rel_wf[OF `proof_state_rel PS S`] by simp

    from first_step `cmd = currentCommand S i`[symmetric]
      `cmd = WaitReturn res`
      `currentProc S i \<triangleq> toImpl`
      wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf]
    have c3: "localState S i \<triangleq> (ps_store PS, ps_localKnown PS, impl_language_loops.io.WaitReturn res)"
      thm Pair_inject Suc.prems(1) Suc.prems(3) option.sel
      using proof_state_rel_fact(10)[OF `proof_state_rel PS S`]
      by ( auto simp add: step_s.simps `ps_i PS = i`)



    show ?thesis
    proof (cases "action = ALocal False")
      case True

      from first_step `cmd = currentCommand S i`[symmetric]
        `cmd = WaitReturn res`
        `currentProc S i \<triangleq> toImpl`
        wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf] 
        c3
        `action = ALocal False`
      obtain u
        where  "u \<notin> ps_localKnown PS"
          and action_def: "action = ALocal False"
          and c5: "u \<in> uniqueIds res"
          and c6: "S1 = S\<lparr>localState := localState S(i \<mapsto> ???)\<rparr>"
          and c7: "\<not> ok"
        by (auto simp add: step_s.simps  split: if_splits) (auto)

      define PS' where "PS' \<equiv> PS"

      have "\<not>invariant_return (invariant (prog S))  PS (Some res)"
        using  `u \<in> uniqueIds res` `u \<notin> ps_localKnown PS` by (auto simp add: invariant_return_def)


      thus ?thesis
        using \<open>cmd = impl_language_loops.io.WaitReturn res\<close> steps_io_final by fastforce
    next
      case False



      from first_step `cmd = currentCommand S i`[symmetric]
        `cmd = WaitReturn res`
        `currentProc S i \<triangleq> toImpl`
        wf_localState_currentProc[OF wf] wf_localState_to_invocationOp[OF wf] 
        c3
      have c0: "cmd = impl_language_loops.io.WaitReturn res"
        and c1: "currentProc S i \<triangleq> impl_language_loops.toImpl"
        and c2: "action = AReturn res"
        and uids_wf: "uniqueIds res \<subseteq> ps_localKnown PS"
        and c4: "currentTransaction S i = None"
        and c5: "S1 = S \<lparr>localState := (localState S)(i := None), currentProc := (currentProc S)(i := None), visibleCalls := (visibleCalls S)(i := None), invocationRes := invocationRes S(i \<mapsto> res), knownIds := knownIds S \<union> uniqueIds res\<rparr>"
        and c6: "ok \<longleftrightarrow> invariant (prog S) (invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S) (knownIds S \<union> uniqueIds res) (invocationOp S) (invocationRes S(i \<mapsto> res)))"
        unfolding atomize_conj 
        by (auto simp add: step_s.simps `action \<noteq> ALocal False`  split: if_splits)

      have "invocationRes S1 i = Some res"
        using c5 by simp


      have "tr' = []"    \<comment> \<open>Can do no step after return \<close>
      proof (rule ccontr)
        assume "tr' \<noteq> []"
        with `S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'`
        obtain S1' a where "S1 ~~ (i, a) \<leadsto>\<^sub>S S1'"
          using steps_nonempty_first by blast

        have "invocationOp S i \<noteq> None"
          using c3 local.wf wf_localState_to_invocationOp by fastforce


        from c5 `invocationOp S i \<noteq> None` `S1 ~~ (i, a) \<leadsto>\<^sub>S S1'`
        show False by (auto simp add: step_s.simps)
      qed

      with `\<not>traceCorrect_s tr`
      have "\<not>ok"
        by (simp add: tr_def traceCorrect_s_def)

      have "ps_tx PS = None"
        using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_fact(13) by fastforce

      show ?thesis
      proof (intro conjI exI)
        show "steps_io (invariant (prog S)) (querySpec (prog S)) PS cmd PS (Some res)"
        proof (fuzzy_rule steps_io_final)
          show "impl_language_loops.io.WaitReturn res = cmd"
            using `cmd = WaitReturn res` by simp

        qed

        have "\<not> invariant_return (invariant (prog S)) PS (Some res)"
          unfolding invariant_return_def not_ex de_Morgan_conj disj_not1
        proof (intro impI allI )
          fix r
          assume "Some res \<triangleq> r"

          have allCommitted: "committedCalls S = dom (calls S)"
            by (smt Suc.prems(1) Suc.prems(3) c4 committedCalls_allCommitted option.discI proof_state_rel_def)

          have h2: "committedCallsH (map_update_all (callOrigin PS) (ps_localCalls PS) (the (ps_tx PS))) (transactionStatus S)
          = dom (calls PS)"
            using Suc.prems(1) allCommitted proof_state_rel_fact(2) proof_state_rel_fact(4) by fastforce


          have ctx_same: "(invContextH (callOrigin S) (transactionOrigin S) (transactionStatus S) (happensBefore S) (calls S)
          (knownIds S \<union> uniqueIds res) (invocationOp S) (invocationRes S(i \<mapsto> res)))
        =(invariantContext.truncate (PS\<lparr>invocationRes := invocationRes PS(ps_i PS \<mapsto> r), knownIds := knownIds PS \<union> uniqueIds r\<rparr>))"
            \<comment> \<open>TODO extract this into lemma (invContextH and truncate if all committed)\<close>
            apply (auto simp add: invContextH_def invariantContext.defs allCommitted h2 restrict_relation_def
                updateHb_simp_distinct2 `i = ps_i PS` restrict_map_def domD domIff
                proof_state_rel_fact[OF `proof_state_rel PS S`]
                intro!: HOL.ext)
            subgoal
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_fact(13) proof_state_rel_fact(15) by fastforce
            subgoal
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_fact(13) proof_state_rel_fact(15) by fastforce
            subgoal
              using Suc.prems(1) happensBefore_in_calls_left local.wf proof_state_rel_fact(2) proof_state_rel_fact(3) updateHb_simp_distinct2 by fastforce
            subgoal
              using Suc.prems(1) happensBefore_in_calls_right local.wf proof_state_rel_fact(2) proof_state_rel_fact(3) updateHb_simp_distinct2 by fastforce
            subgoal
              apply (auto simp add: map_update_all_def)
              using Suc.prems(1) Suc.prems(3) c4 proof_state_rel_fact(13) proof_state_rel_fact(15) by fastforce
            subgoal
              by (metis Suc.prems(1) local.wf map_update_all_None proof_state_rel_fact(2) proof_state_rel_fact(4) wellFormed_callOrigin_dom3)
            subgoal for x
              apply (case_tac "transactionStatus S x", auto)
              using Suc.prems(1) local.wf proof_state_rel_fact(5) wf_transaction_status_iff_origin apply fastforce
              by (metis (no_types, lifting) Suc.prems(1) Suc.prems(3) c4 option.discI proof_state_rel_fact(13) proof_state_rel_fact(14) transactionStatus.exhaust)

            using \<open>Some res \<triangleq> r\<close> by blast+


          from `\<not>ok` c6
          show "\<not> invariant (prog S) (invariantContext.truncate (PS\<lparr>invocationRes := invocationRes PS(ps_i PS \<mapsto> r), knownIds := knownIds PS \<union> uniqueIds r\<rparr>))"
            by (auto simp add: ctx_same)
        qed
        thus "Some res = None \<or> \<not> invariant_return (invariant (prog S)) PS (Some res)"
          by simp
      qed
    qed
  next
    case False

    have current: "currentCommand S i = currentCommand S i \<bind> return"
      by simp

    have "\<exists>PS' cmd'.
       step_io (invariant (prog S)) (querySpec (prog S)) PS (currentCommand S i) action PS' cmd' ok \<and>
       (ok \<longrightarrow> proof_state_rel PS' S1 \<and> currentCommand S1 i = cmd' \<bind> impl_language_loops.return)"
      using `proof_state_rel PS S` first_step `i = ps_i PS` current
    proof (rule step_io_simulation)
      show "\<And>r. currentCommand S i \<noteq> impl_language_loops.io.WaitReturn r"
        using False `cmd = currentCommand S i` by blast
      show "program_wellFormed (prog S)"
        using `program_wellFormed (prog S)` .

      
      show "uniqueIds Op \<subseteq> ps_localKnown PS"
        if c0: "action = ADbOp c Op res"
        for  c Op res
        by (metis Suc.prems(1) Suc.prems(3) \<open>\<And>thesis. (\<And>S1. \<lbrakk>S ~~ (i, action, ok) \<leadsto>\<^sub>S S1; S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> action.distinct(33) action.distinct(53) proof_state_rel_def step_s_to_step that use_invocation_cannot_guess_ids_dbop)



    qed

    from this obtain PS' cmd' 
      where step_io: "step_io (invariant (prog S)) (querySpec (prog S)) PS (currentCommand S i) action PS' cmd' ok"
        and step_io2: "(ok \<Longrightarrow> proof_state_rel PS' S1 \<and> currentCommand S1 i = cmd')"
      by auto

    show ?thesis
    proof (cases ok)
      case True
      hence "proof_state_rel PS' S1"
        and "currentCommand S1 i = cmd' \<bind> impl_language_loops.return"
        using step_io2 by auto

      hence "currentCommand S1 i = cmd'"
        by simp

      have "k = length tr'"
        using  `Suc k = length tr` \<open>tr = (action, ok) # tr'\<close> by auto


      have "i = ps_i PS'"
        using Suc.prems(3) step_io step_io_same_i by fastforce

      have "\<not> traceCorrect_s tr'"
        using `\<not> traceCorrect_s tr` True tr_def traceCorrect_s_split by fastforce


      from `prog S1 = prog S` `program_wellFormed (prog S)`
      have "program_wellFormed (prog S1)"
        by simp

      have "cmd' = currentCommand S1 i"
        using `currentCommand S1 i = cmd'`
        by simp

      from Suc.hyps(1)[OF `k = length tr'` `proof_state_rel PS' S1` `S1 ~~ (i, tr') \<leadsto>\<^sub>S* S'` 
            `i = ps_i PS'` `\<not> traceCorrect_s tr'` `program_wellFormed (prog S1)` `cmd' = currentCommand S1 i`]
      obtain PS'' and res
        where steps_tr': "steps_io (invariant (prog S1)) (querySpec (prog S1)) PS' cmd'  PS'' res"
          and incorrect_cases: "res = None \<or> \<not> invariant_return (invariant (prog S1)) PS'' res"
        by auto

      have steps_combined: "steps_io (invariant (prog S)) (querySpec (prog S)) PS cmd  PS'' res" 
        using step_io 
      proof (fuzzy_rule steps_io_step)
        show "currentCommand S i = cmd"
          by (simp add: Suc.prems(6))
        show " steps_io (invariant (prog S)) (querySpec (prog S)) PS' cmd' PS'' res"
          using steps_tr'
          by (metis (no_types, lifting) Suc.prems(2) other_steps unchangedProg) 
        show "ok = True"
          using `ok` by simp
      qed



      thm `prog S1 = prog S`

      have "prog S1 = prog S"
        using unchangedProg1[OF first_step]
        by simp

      from incorrect_cases
      show ?thesis
      proof
        assume "res = None"

        with steps_combined
        show ?thesis
          by blast
      next
        assume "\<not> invariant_return (invariant (prog S1)) PS'' res"
        hence "\<not> invariant_return (invariant (prog S)) PS'' res"
          using `prog S1 = prog S` by simp
        with steps_combined
        show ?thesis
          by blast
      qed
    next
      case False

      from \<open>step_io (invariant (prog S)) (querySpec (prog S)) PS (currentCommand S i) action PS' cmd' ok\<close>
      have "steps_io (invariant (prog S)) (querySpec (prog S)) PS cmd PS' None"
      proof (fuzzy_rule steps_io_error)
        show "ok = False" using False by simp

        show "currentCommand S i = cmd"
          using ` cmd = currentCommand S i` by simp


      qed
      thus ?thesis
        by auto
    qed
  qed
qed




method subst_all uses r = (subst r | subst(asm) r)+

text "Correctness of execution when executing only a prefix of the trace:"


definition "execution_s_correct_p" where
"execution_s_correct_p S i ls1 P \<equiv> 
    \<forall>trace S' store lk ls2 store' lk' ls1'. 
          (S ~~ (i, trace) \<leadsto>\<^sub>S* S') 
      \<longrightarrow> (localState S i \<triangleq> (store, lk, bind ls1 ls2))
      \<longrightarrow> (localState S' i \<triangleq> (store', lk', bind ls1' ls2))
      \<longrightarrow> traceCorrect_s trace \<and> (\<forall>res. ls1' = WaitReturn res \<longrightarrow>  P S' res)"

lemmas use_execution_s_correct_p = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

lemmas use_execution_s_correct_p_trace = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct1]

lemmas use_execution_s_correct_p_P = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct2, rule_format]

lemma execution_s_correct_to_p:
  assumes ec_p: "execution_s_correct_p S i ls1 P"
    and S_ls: "localState S i \<triangleq> (store, localKnown, ls1)"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and wf_s: "state_wellFormed_s S i"
    and impl: "currentProc S i \<triangleq> toImpl"
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  have wf: "state_wellFormed S"
    using state_wellFormed_s_to_wf wf_s by blast


  from  steps
  show "traceCorrect_s trace"
  proof (induct rule: step_s_induct)
    case initial
    then show ?case
      by (simp add: traceCorrect_s_def) 
  next
    case (step tr S' a S'')

    hence IH: "(x, False) \<notin> set tr" for x
      by (simp add: traceCorrect_s_def)

    have "S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''"
      using step.hyps step.step steps_s_step by blast

    from `S' ~~ (i, a) \<leadsto>\<^sub>S S''`
    have "localState S' i \<noteq> None"
      apply (auto simp add: step_s.simps)
      by (metis S_ls Un_iff \<open>S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''\<close> list.set_intros(1) local.wf no_more_invoc option.simps(3) set_append)




    \<comment> \<open>TODO: move into Lemma\<close>
    from ` S ~~ (i, tr) \<leadsto>\<^sub>S* S'` `localState S' i \<noteq> None`
    have "currentProc S' i \<triangleq> toImpl"
    proof (induct rule: step_s_induct)
      case initial
      then show ?case
        using S_ls impl by blast
    next
      case (step tr S a S')
      then show ?case
        apply (auto simp add: step_s.simps)
        by (metis (no_types, lifting) S_ls has_invocationOp_forever local.wf option.exhaust option.simps(3) wf_localState_needs_invocationOp)
    qed

    have "localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)"
      using S_ls by auto

    show ?case 
    proof (auto simp add: traceCorrect_s_def IH)
      fix x
      assume "a = (x, False)"



      show False
      proof (cases "localState S'' i")
        case None

        from `a = (x, False)` `S' ~~ (i, a) \<leadsto>\<^sub>S S''` `localState S'' i = None` `currentProc S' i \<triangleq> toImpl`
        obtain store'' localKnown'' ls'' res
          where a0: "a = (AReturn res, False)"
            and a1: "x = AReturn res"
            and not_invariant: "\<not> invariant (prog S')             (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S')               (calls S') (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))"
            and a3: "localState S' i \<triangleq> (store'', localKnown'', ls'')"
            and a4: "currentProc S' i \<triangleq> toImpl"
            and a5: "toImpl (store'', localKnown'', ls'') = Return res"
            and a6: "currentTransaction S' i = None"
            and S''_def: "S'' = S'         \<lparr>localState := (localState S')(i := None), currentProc := (currentProc S')(i := None),            visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> res),            knownIds := knownIds S' \<union> uniqueIds res\<rparr>"
          by (auto simp add: step_s.simps)

        from ec_p \<open>S ~~ (i, tr) \<leadsto>\<^sub>S* S'\<close> \<open>localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)\<close> 
        have "P S' res" 
        proof (rule use_execution_s_correct_p_P)
          from `toImpl (store'', localKnown'', ls'') = Return res`
          show "ls'' = impl_language_loops.io.WaitReturn res"
            by (cases ls'', auto split: prod.splits if_splits)

          from `localState S' i \<triangleq> (store'', localKnown'', ls'')`
          show " localState S' i \<triangleq> (store'', localKnown'', ls'' \<bind> impl_language_loops.return)"
            by auto
        qed
        from P[OF this]
        have invariant: "invariant (prog S) (invariantContext.truncate (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))" .

        have "state_wellFormed S'"
          using local.wf state_wellFormed_s_steps step.step by blast

        have "state_wellFormed_s S' i"
          using state_wellFormed_s_def step.step steps_s_append wf_s by blast

        have "currentTransaction S' i = None"
          using a6 by auto


        have no_uncommitted:
          "transactionStatus S' tx \<noteq> Some Uncommitted" for tx
          using \<open>state_wellFormed_s S' i\<close> a6 state_wellFormed_s_currentTransactions_iff_uncommitted by fastforce



        have "prog S' = prog S"
          using step.step unchangedProg by blast



        have allTxnsCommitted: "committedTransactions S' = dom (transactionOrigin S')"
          apply (auto simp add: )
          apply (metis \<open>state_wellFormed S'\<close> option.distinct(1) option.exhaust wf_transactionOrigin_and_status)
          by (metis \<open>state_wellFormed S'\<close> no_uncommitted not_uncommitted_cases option.exhaust state_wellFormed_transactionStatus_transactionOrigin)


        have allCommitted: "committedCalls S' = dom (calls S')"
          apply (auto simp add: committedCallsH_def isCommittedH_def)
          apply (metis \<open>state_wellFormed S'\<close> no_uncommitted option.exhaust wellFormed_currentTransactionUncommitted wf_callOrigin_and_calls)
          by (metis (no_types, hide_lams) \<open>state_wellFormed S'\<close> exists_optionI no_uncommitted not_uncommitted_cases option.distinct(1) wf_callOrigin_and_calls wf_no_transactionStatus_origin_for_nothing)


        have invContextSame:
             "(invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S')
                (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))
            = (invariantContext.truncate (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                                             knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
          apply (auto simp add: invContextH_def invariantContext.defs allCommitted allTxnsCommitted restrict_relation_def)
          apply (simp add: \<open>state_wellFormed S'\<close> domD happensBefore_in_calls_left)
          apply (simp add: \<open>state_wellFormed S'\<close> domD happensBefore_in_calls_right)
          apply (metis \<open>state_wellFormed S'\<close> restrict_map_noop2 wellFormed_callOrigin_dom)
          done

        with invariant
        have "invariant (prog S')
        (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S') (calls S')
          (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))"
          by (simp add: \<open>prog S' = prog S\<close>)


        with not_invariant P
        show False
          by auto


      next
        case (Some S''_ls)

        

        from ec_p 
        have "traceCorrect_s (tr @ [a]) \<and> (\<forall>res. snd (snd S''_ls) = impl_language_loops.io.WaitReturn res \<longrightarrow> P S'' res)"
          using \<open>S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''\<close> \<open>localState S i \<triangleq> (store, localKnown, ls1 \<bind> impl_language_loops.return)\<close>
        proof (rule use_execution_s_correct_p)
          show "localState S'' i \<triangleq> (fst S''_ls, fst (snd S''_ls), snd (snd S''_ls) \<bind> impl_language_loops.return)"
            by (simp add: Some)
        qed
          
        thus False
          by (metis \<open>a = (x, False)\<close> append_is_Nil_conv last_in_set last_snoc list.simps(3) traceCorrect_s_def)

        
      qed
    qed
  qed
qed


lemma steps_io_same_i:
  assumes "steps_io progInv qrySpec S cmd S' res"
  shows "ps_i S' = ps_i S"
using assms proof (induct rule: steps_io.induct)
  case (steps_io_final S  res)
  then show ?case
    by simp
next
  case (steps_io_error  S cmd action S' cmd')
  then show ?case
    by (auto simp add: step_io_same_i)
next
  case (steps_io_step  S cmd action S' cmd' S'' res)
  then show ?case 
    by (auto simp add: step_io_same_i)
qed


definition 
"execution_s_check progInv qrySpec S cmd P \<equiv>
  \<forall>S' res. steps_io progInv qrySpec S cmd  S' res
    \<longrightarrow> proof_state_wellFormed' S
    \<longrightarrow> (case res of Some r \<Rightarrow> P S' r | None \<Rightarrow> False)
  "

lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

definition
"finalCheck Inv i S res \<equiv>
Inv (invariantContext.truncate (S\<lparr>invocationRes := invocationRes S(i \<mapsto> res), knownIds := knownIds S \<union> uniqueIds res\<rparr>))"

lemmas show_finalCheck = finalCheck_def[THEN meta_eq_to_obj_eq, THEN iffD2, rule_format]


text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"


lemma execution_s_check_sound:
  assumes ls_def: "localState S i \<triangleq> (Map.empty, localKnown, ls)"
    and vis_def: "visibleCalls S i \<triangleq> vis"
    and progr_def: "prog S = progr"
    and toImpl: "currentProc S i \<triangleq> toImpl"
    and generatedLocal: "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and generatedLocalPrivate1: "generatedLocalPrivate \<subseteq> generatedLocal"
    and generatedLocalPrivate2: "\<forall>v\<in>generatedLocalPrivate. uid_is_private i S v"
    and S_wf: "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    and no_currentTxn: "currentTransaction S i = None"
    and firstTx_def: "(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed ))"
    and localKnown: "localKnown = generatedLocal \<union> uniqueIds (the (invocationOp S i))"
    and no_guess: "invocation_cannot_guess_ids localKnown i S"
    and P_inv: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and P_ids: "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
    and prog_wf: "program_wellFormed (prog S)"
    and PS_def: "PS = \<lparr>
      calls = (calls S),
      happensBefore = (happensBefore S),
      callOrigin = (callOrigin S),
      transactionOrigin = (transactionOrigin S),
      knownIds = (knownIds S),
      invocationOp = (invocationOp S),
      invocationRes = (invocationRes S),
      ps_i = i,
      ps_generatedLocal = generatedLocal,
      ps_generatedLocalPrivate = generatedLocalPrivate,
      ps_localKnown = localKnown,
      ps_vis = vis,
      ps_localCalls = [],
      ps_tx = (currentTransaction S i),
      ps_firstTx = firstTx,
      ps_store = Map.empty\<rparr>"
    and c: "execution_s_check (invariant progr) (querySpec progr) PS ls P"
    \<comment> \<open>The execution check ensures that executing statement s only produces valid traces ending in a state 
   satisfying P.\<close>
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume steps: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  text "We can simulate this execution with @{term steps_io}:"

  have "i = ps_i PS"
    by (simp add: PS_def)

  have "proof_state_rel PS S"
    unfolding proof_state_rel_def 
  proof (intro conjI)
    show "state_wellFormed S"
      by (simp add: S_wf)

    show "sorted_by (happensBefore S) (ps_localCalls PS)"
      by (simp add: PS_def sorted_by_empty)

    show "\<forall>c. i_callOriginI PS c \<triangleq> ps_i PS \<longrightarrow> c \<in> ps_vis PS"
      apply (auto simp add: PS_def)
      by (metis (mono_tags, lifting) S_wf assms(2) i_callOriginI_h_def not_None_eq option.case_eq_if option.sel state_wellFormed_ls_visibleCalls_callOrigin)


    show "ps_generatedLocal PS \<subseteq> ps_localKnown PS"
      by (auto simp add: PS_def localKnown)

    show " invocation_cannot_guess_ids (ps_localKnown PS) (ps_i PS) S"
      using PS_def no_guess by force
          

  qed (insert assms, simp; fail)+


  define cmd where "cmd = currentCommand S i"

  show "traceCorrect_s trace"
  proof (rule ccontr)
    assume "\<not> traceCorrect_s trace"

    from steps_io_simulation[OF `proof_state_rel PS S` steps `i = ps_i PS` `\<not> traceCorrect_s trace` prog_wf `cmd = currentCommand S i`]
    obtain PS' res
      where steps_io: "steps_io (invariant (prog S)) (querySpec (prog S)) PS cmd PS' res"
        and not_correct: "res = None \<or> \<not> invariant_return (invariant (prog S)) PS' res"
      by blast


    from c 
    have c1:  "(case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r)"
      if "steps_io (invariant progr) (querySpec progr) PS ls  S' res"
        and "proof_state_wellFormed' PS"
      for S' res
      using execution_s_check_def that by blast+

    from steps_io
    have "(case res of None \<Rightarrow> False | Some r \<Rightarrow> P PS' r)"
    proof (fuzzy_rule c1)
      show "cmd = ls"
        by (simp add: cmd_def ls_def)
      show "prog S = progr"
        by (simp add: progr_def)
      thus "prog S = progr".
      have "proof_state_wellFormed PS"
        using S_wf \<open>proof_state_rel PS S\<close> show_proof_state_wellFormed by blast
      thus "proof_state_wellFormed' PS"
        using proof_state_wellFormed_implies by blast

    qed

    with not_correct
    obtain r
      where c0: "\<not> invariant_return (invariant (prog S)) PS' (Some r)"
        and c1: "res \<triangleq> r"
        and c3: "P PS' r"
      by (auto split: option.splits)
      
    from `\<not> invariant_return (invariant (prog S)) PS' (Some r)`
    have notInv1: "(\<not> invariant (prog S) (invariantContext.truncate (PS'\<lparr>invocationRes := invocationRes PS'(ps_i PS' \<mapsto> r), knownIds := knownIds PS' \<union> uniqueIds r\<rparr>)))
             \<or> \<not>(uniqueIds r \<subseteq> ps_localKnown PS')"
      unfolding invariant_return_def by (auto simp add: )

    thus False
    proof 
      assume notInv: "(\<not> invariant (prog S) (invariantContext.truncate (PS'\<lparr>invocationRes := invocationRes PS'(ps_i PS' \<mapsto> r), knownIds := knownIds PS' \<union> uniqueIds r\<rparr>)))"

      thus False
        using P_inv \<open>i = ps_i PS\<close> c3 steps_io steps_io_same_i by fastforce
    next
      assume "\<not> uniqueIds r \<subseteq> ps_localKnown PS'"

      thus False
        using P_ids c3 by blast
    qed
  qed
qed



lemma execution_s_check_sound3:
  assumes a1: "localState S i \<triangleq> (Map.empty, uniqueIds op, ls)"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocationOp S i \<triangleq> op"
    and prog_wf: "program_wellFormed (prog S)"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and P_ids: "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
    and inv: "invariant progr (invariantContext.truncate S)"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
\<lbrakk>
\<And>tx. s_transactionOrigin tx \<noteq> Some i;
invariant progr \<lparr>
  calls = s_calls,
  happensBefore = s_happensBefore,
  callOrigin = s_callOrigin,
  transactionOrigin = s_transactionOrigin,
  knownIds = s_knownIds,
  invocationOp = s_invocationOp(i\<mapsto>op),
  invocationRes = s_invocationRes(i:=None)
\<rparr>
\<rbrakk> \<Longrightarrow>
  execution_s_check (invariant progr) (querySpec progr) \<lparr>
      calls = s_calls,
      happensBefore = s_happensBefore,
      callOrigin = s_callOrigin,
      transactionOrigin = s_transactionOrigin,
      knownIds = s_knownIds,
      invocationOp = s_invocationOp(i\<mapsto>op),
      invocationRes = s_invocationRes(i:=None),
      ps_i = i,
      ps_generatedLocal = {},
      ps_generatedLocalPrivate = {},
      ps_localKnown = uniqueIds op,
      ps_vis = {},
      ps_localCalls = [],
      ps_tx = None,
      ps_firstTx = True,
      ps_store = Map.empty\<rparr> ls P" 
  shows "execution_s_correct S i"
  using a1 
proof (rule execution_s_check_sound[where P=P])

    from `S \<in> initialStates' progr i`
    obtain Sa proc a b impl
      where S_def: "S = Sa \<lparr>localState := localState Sa(i \<mapsto> (a, b)), currentProc := currentProc Sa(i \<mapsto> impl), visibleCalls := visibleCalls Sa(i \<mapsto> {}), invocationOp := invocationOp Sa(i \<mapsto> proc)\<rparr>"
        and progr_def: "progr = prog Sa"
        and proc: "procedure (prog Sa) proc = ((a, b), impl)"
        and uniqueIds: "uniqueIds proc \<subseteq> knownIds Sa"
        and invAll: "invariant_all' Sa"
        and wf: "state_wellFormed Sa"
        and opNone: "invocationOp Sa i = None"
        and noUncommitted: "\<forall>tx. transactionStatus Sa tx \<noteq> Some Uncommitted"
        and noTxns: "\<forall>tx. transactionOrigin Sa tx \<noteq> Some i"
      by (auto simp add: initialStates'_def)  

    have "op = proc"
      using a4 by (auto simp add: S_def)

    show "visibleCalls S i \<triangleq> {}"
      by (simp add: S_def)

    show "prog S = progr"
      using progr_def  by (simp add: S_def)

    show " currentProc S i \<triangleq> impl_language_loops.toImpl"
      by (simp add: a3)

    show "{} = {x. generatedIds S x \<triangleq> i}"
      by (auto simp add: S_def local.wf opNone wf_generated_ids_invocation_exists)

    show "{} \<subseteq> {}"
      by simp

    show "state_wellFormed S"
      using a2 initialStates'_same initialStates_wellFormed by fastforce

    show "currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted" for tx'
      using a2 initialState_noTxns1 initialStates'_same by fastforce

    show "currentTransaction S i = None"
      using a2 initialState_noTxns2 initialStates'_same by fastforce


    have pcgi: "invocations_cannot_guess_ids progr"
      using \<open>prog S = progr\<close> prog_wf program_wellFormed_def by blast

    then 
    show "invocation_cannot_guess_ids (uniqueIds op) i S"
      using `program_wellFormed (prog S)`
        and `S \<in> initialStates' progr i`
      using invocation_cannot_guess_ids_initialStates a4
      by fastforce

    show "\<And>S' res.
       P S' res \<Longrightarrow>
       invariant (prog S)
        (invariantContext.truncate
          (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
      using P by blast

    show "program_wellFormed (prog S)"
      by (simp add: prog_wf)

    show "execution_s_check (invariant progr) (querySpec progr)
     \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S,
        transactionOrigin = transactionOrigin S, knownIds = knownIds S, invocationOp = invocationOp S,
        invocationRes = invocationRes S, ps_i = i, ps_generatedLocal = {}, ps_generatedLocalPrivate = {},
        ps_localKnown = uniqueIds (the (invocationOp S i)), ps_vis = {}, ps_localCalls = [],
        ps_tx = currentTransaction S i,
        ps_firstTx =
          \<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed,
        ps_store = Map.empty\<rparr>
     ls P"
    proof (fuzzy_rule c)
      show "\<And>tx. transactionOrigin S tx \<noteq> Some i"
        by (auto simp add: S_def noTxns)

      show "True = (\<forall>c tx. transactionOrigin S tx \<triangleq> i \<longrightarrow> callOrigin S c \<triangleq> tx \<longrightarrow> transactionStatus S tx \<noteq> Some Committed)"
        by (auto simp add: S_def noTxns)

      show "None = currentTransaction S i"
        by (auto simp add: S_def local.wf opNone wellFormed_invoc_notStarted(1))


      show " op = the (invocationOp S i)"
        by (auto simp add: S_def  \<open>op = proc\<close>)

      show "(invocationRes S)(i := None) = invocationRes S"
        by (auto simp add: S_def fun_upd_idem local.wf opNone state_wellFormed_invocation_before_result)


      show "(invocationOp S)(i \<mapsto> op) = invocationOp S"
        by (auto simp add: S_def \<open>op = proc\<close>)

      show "invariant progr
       \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S,
          transactionOrigin = transactionOrigin S, knownIds = knownIds S, invocationOp = invocationOp S(i \<mapsto> op),
          invocationRes = (invocationRes S)(i := None)\<rparr>"
        using inv \<open>(invocationRes S)(i := None) = invocationRes S\<close> \<open>invocationOp S(i \<mapsto> op) = invocationOp S\<close> by (auto simp add: invariantContext.defs) 


    qed

    show "\<And>S' res. P S' res \<Longrightarrow> uniqueIds res \<subseteq> ps_localKnown S'"
      using P_ids .

qed (simp add: a4)+



lemma traceCorrect_s_empty: "traceCorrect_s  [] "
  by (simp add: traceCorrect_s_def) 

lemma case_trace_not_empty:
  assumes  "\<And>a trace'. trace = a#trace' \<Longrightarrow> traceCorrect_s  (a#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty2:
  assumes  "\<And>action Inv trace'. trace = (action, Inv)#trace' \<Longrightarrow> traceCorrect_s  ((action, Inv)#trace')"
  shows "traceCorrect_s  trace"
  using assms by (cases trace, auto simp add: traceCorrect_s_empty)

lemma case_trace_not_empty3:
  assumes "S ~~ (i,trace) \<leadsto>\<^sub>S* S''"
    and "\<And>action S' Inv trace'. \<lbrakk>
      trace = (action, Inv)#trace'; 
      S ~~ (i,action,Inv) \<leadsto>\<^sub>S S'; 
      S' ~~ (i,trace') \<leadsto>\<^sub>S* S''\<rbrakk> \<Longrightarrow> Inv \<and> traceCorrect_s (trace')"
  shows "traceCorrect_s  trace"
  by (metis assms(1) assms(2) case_trace_not_empty2 sndI steps_s_cons_simp traceCorrect_s_split)


lemma sorted_by_updateHb:
  assumes "set cs \<inter> vis = {}"
    and "set cs \<inter> Field hb = {}"
    and "distinct cs"
  shows "sorted_by (updateHb hb vis cs) cs"
  using assms proof (induct cs arbitrary: hb vis)
case Nil
  then show ?case 
    by (simp add: sorted_by_empty)

next
  case (Cons x xs)

  have "distinct xs"
    using Cons.prems(3) by auto


  from this
  have IH: "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) xs"
  proof (fuzzy_rule Cons)

    show " set xs \<inter> insert x vis = {}"
      using Cons by auto
    show " set xs \<inter> Field (hb \<union> vis \<times> {x}) = {}"
      using Cons by (auto simp add: Field_def)
  qed

  show ?case 
  proof (auto simp add: updateHb.simps)
    show "sorted_by (updateHb (hb \<union> vis \<times> {x}) (insert x vis) xs) (x # xs)"
      apply (auto simp add: sorted_by_cons_iff IH)
      using Cons.prems(1) Cons.prems(2) Cons.prems(3) FieldI1 updateHb_simp2 by fastforce
  qed
qed

lemma no_ainvoc:
  assumes "\<forall>p t. (AInvoc p, t) \<notin> set trace"
    and "trace = (action, Inv) # trace'"
and "\<lbrakk>\<forall>p t. (AInvoc p, t) \<notin> set trace; \<And>proc. action \<noteq> AInvoc proc\<rbrakk> \<Longrightarrow> P"
shows "P"
  using assms by auto

method show_proof_rule = 
  (subst  execution_s_check_def, intro allI impI conjI, erule case_trace_not_empty3, erule(1) no_ainvoc, goal_cases Step)

inductive_cases step_s_NewId: "S ~~ (i, ANewId uidv, Inv) \<leadsto>\<^sub>S S'"






lemma execution_s_check_proof_rule:
  assumes noReturn: "\<And>r. cmd \<noteq> WaitReturn r"
and cont: "
\<And>action PS' cmd' ok. \<lbrakk>
  step_io Inv crdtSpec PS (cmd \<bind> cont) action PS' cmd' ok;
  proof_state_wellFormed' PS
\<rbrakk> \<Longrightarrow> 
  ok
  \<and> (\<exists>res. cmd' = cont res
  \<and> execution_s_check Inv crdtSpec PS' (cont res) P)"
  shows "execution_s_check Inv crdtSpec PS  (cmd \<bind> cont) P"
proof (auto simp add: execution_s_check_def)
  fix S' res
  assume steps_io: "steps_io Inv crdtSpec PS (cmd \<bind> cont) S' res"
    and PS_wf: "proof_state_wellFormed' PS"

  from noReturn
  have noReturn: "cmd \<bind> cont \<noteq> impl_language_loops.io.WaitReturn r" for r
    by (cases cmd, auto)


  from steps_io noReturn cont PS_wf
  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
  proof (induct)
    case (steps_io_final S res)
    then show ?case by auto
  next
    case (steps_io_error  S cmd action S' cmd')
    have False
      using steps_io_error.hyps steps_io_error.prems(2) steps_io_error.prems(3) by blast
    thus ?case ..
  next
    case (steps_io_step S cmd action S' cmd' S'' res)

    from steps_io_step(5)[OF steps_io_step(1) `proof_state_wellFormed' S`]
    obtain r where "cmd' = cont r" and "execution_s_check Inv crdtSpec S' (cont r) P"
      by auto

    from `proof_state_wellFormed' S`
    have "proof_state_wellFormed' S'"
      using step_io_wf_maintained steps_io_step.hyps(1) by blast



    show ?case
      using `cmd' = cont r` `execution_s_check Inv crdtSpec S' (cont r) P` \<open>proof_state_wellFormed' S'\<close> execution_s_check_def steps_io_step.hyps(2) by blast
  qed
qed



subsection "Loop Rule"

text "Loops annotated with loop invariant for easier generation of verification conditions:"

definition  loop_a :: "(('proc, 'any, 'operation) proof_state \<Rightarrow> ('proc, 'any, 'operation) proof_state \<Rightarrow> bool) \<Rightarrow>   (bool, 'operation::small, 'any::small) io \<Rightarrow> (unit, 'operation, 'any) io" where
"loop_a LoopInv body \<equiv> loop body"

lemma annotate_loop:
"loop bdy = loop_a LoopInv bdy"
  unfolding loop_a_def by simp

lemma WaitReturn_combined:
"WaitReturn r = (cmd \<bind> cont)
\<Longrightarrow> (\<exists>ri. cmd = WaitReturn ri \<and> cont ri = WaitReturn r)"
  by (cases cmd) auto

lemma step_io_bind_split:
  assumes "step_io progInv qrySpec S (cmd \<bind> cont) action S' cmdCont' Inv"
  shows "(\<exists>cmd'. step_io progInv qrySpec S cmd action S' cmd' Inv \<and> cmdCont' = cmd' \<bind> cont)
        \<or> (\<exists>r. cmd = WaitReturn r \<and> step_io progInv qrySpec S (cont r) action S' cmdCont' Inv)"
proof (cases cmd)
  case (WaitLocalStep x1)
then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitBeginAtomic x2)
  then show ?thesis using assms  
    by (auto simp add: step_io_def split: prod.splits, force)
next
  case (WaitEndAtomic x3)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitNewId x41 x42)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (WaitDbOperation x51 x52)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits if_splits) 
next
  case (WaitReturn x6)
  then show ?thesis using assms  by (auto simp add: step_io_def split: prod.splits) 
next
  case (Loop bdy cnt)
  then show ?thesis using assms  
    by (auto simp add: step_io_def intro!: arg_cong[where f="bind (from_V bdy)"] split: prod.splits) 
qed
  


lemma steps_io_bind_split1:
  assumes "steps_io Inv crdtSpec S cmdC S' res"
    and "cmdC = (cmd \<bind> cont)"
  shows "(\<exists>ri Si. steps_io Inv crdtSpec S cmd Si (Some ri) \<and> steps_io Inv crdtSpec Si (cont ri) S' res)
          \<or> (\<exists>Si. steps_io Inv crdtSpec S cmd Si None)"
  using assms proof (induct arbitrary: cmd)
  case (steps_io_final S res)
  from this obtain ri
    where "cmd = WaitReturn ri" 
      and "cont ri = WaitReturn res"
    by (meson WaitReturn_combined)

  have "steps_io Inv crdtSpec S cmd S (Some ri)"
    by (auto simp add: `cmd = WaitReturn ri`  steps_io.steps_io_final)

  moreover have "steps_io Inv crdtSpec S (cont ri) S (Some res)"
    by (simp add: \<open>cont ri = impl_language_loops.io.WaitReturn res\<close> steps_io.steps_io_final)

  ultimately show ?case
    using \<open>cmd = impl_language_loops.io.WaitReturn ri\<close> steps_io.steps_io_final by fastforce
next
  case (steps_io_error S cmd1 action S' cmd2)
  then show ?case
    apply (auto simp add: step_io_bind_split)
    by (metis step_io_bind_split steps_io.steps_io_error steps_io_final)
next
  case (steps_io_step  S cmd action S' cmd' S'' res)
  then show ?case 
    apply (auto simp add: step_io_bind_split)
    by (smt step_io_bind_split steps_io.steps_io_step steps_io_final)
qed

lemma steps_io_bind_split:
  assumes "steps_io Inv crdtSpec S (cmd \<bind> cont) S' res"
  shows "(\<exists>ri Si. steps_io Inv crdtSpec S cmd Si (Some ri) \<and> steps_io Inv crdtSpec Si (cont ri) S' res)
          \<or> (\<exists>Si. steps_io Inv crdtSpec S cmd Si None)"
  using assms steps_io_bind_split1 by blast



lemma step_io_combine:
  assumes "step_io progInv qrySpec S cmd action S' cmd' ok"
  shows "step_io progInv qrySpec S (cmd\<bind>cont) action S' (cmd'\<bind>cont) ok"
proof (cases cmd)
  case (WaitLocalStep x1)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitBeginAtomic x2)
  then show ?thesis using assms by (auto simp add: step_io_def; force)
next
  case (WaitEndAtomic x3)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitNewId x41 x42)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (WaitDbOperation Op cmdCont)
  then show ?thesis using assms apply (auto simp add: step_io_def)
    subgoal for c y res
      by (auto intro: exI[where x=c])
    done
next
  case (WaitReturn x6)
  then show ?thesis using assms by (auto simp add: step_io_def)
next
  case (Loop bdy cnt)
  then show ?thesis using assms 
    by (auto simp add: step_io_def intro!: arg_cong[where f="bind (from_V bdy)"] split: prod.splits) 
qed

lemma steps_io_combine_ok:
  assumes steps1: "steps_io Inv crdtSpec S cmd1 S' res1"
    and res1_def: "res1 = Some r"
    and steps2: "steps_io Inv crdtSpec S' (cmd2 r) S'' res2"
  shows "steps_io Inv crdtSpec S (cmd1 \<bind> cmd2) S'' res2"
  using steps1 res1_def steps2 
proof (induct)
  case (steps_io_final S res)
  then show ?case
    by auto
next
  case (steps_io_error  S cmd action S' cmd')
  then show ?case
    by auto
next
  case (steps_io_step S cmd action S' cmd' S''' res)
  show ?case
  proof (rule steps_io.steps_io_step)
    from `step_io Inv crdtSpec S cmd action S' cmd' True`
    show "step_io Inv crdtSpec S (cmd \<bind> cmd2) action S' (cmd' \<bind> cmd2) True"
      by (simp add: step_io_combine)

    show "steps_io Inv crdtSpec S' (cmd' \<bind> cmd2) S'' res2"
      by (simp add: steps_io_step.hyps(3) steps_io_step.prems(1) steps_io_step.prems(2))
  qed
qed


lemma execution_s_check_split:
  assumes ec: "execution_s_check Inv crdtSpec S (cmd \<bind> cont) P"
and steps: "steps_io Inv crdtSpec S cmd S' (Some res)"
and wf: "proof_state_wellFormed' S"
shows "execution_s_check Inv crdtSpec S' (cont res) P"
  unfolding execution_s_check_def proof (intro allI impI)

  fix S'a res'
  assume a0: "steps_io Inv crdtSpec S' (cont res) S'a res'"
    and a1: "proof_state_wellFormed' S'"


  from ec
  have ec': "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r" 
    if "steps_io Inv crdtSpec S (cmd \<bind> cont) S' res"
      and "proof_state_wellFormed' S"
    for S' res
    using execution_s_check_def that by blast
    


  show "case res' of None \<Rightarrow> False | Some r \<Rightarrow> P S'a r"
  proof (rule ec')
    show "steps_io Inv crdtSpec S (cmd \<bind> cont) S'a res'"
      by (meson a0 steps steps_io_combine_ok)
    show "proof_state_wellFormed' S"
      using wf .
  qed
qed

lemma steps_io_loop_unroll:
  shows "steps_io progInv qrySpec S (loop body) S' res
     \<longleftrightarrow> steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then return () else loop body)) S' res" (is "?left \<longleftrightarrow> ?right")
proof
  assume "steps_io progInv qrySpec S (loop body) S' res"

  from this
  show "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then return () else loop body)) S' res"
  proof cases
    case (steps_io_final res)
    then show ?thesis
      by (simp add: loop_def)
  next
    case (steps_io_error action cmd')
    then show ?thesis
      by (simp add: step_io_def loop_def)
  next
    case (steps_io_step action Si cmd')

    from `step_io progInv qrySpec S (loop body) action Si cmd' True`
    have cmd': "cmd' = body \<bind> (\<lambda>r. if r then impl_language_loops.return () else Loop (to_V body) (impl_language_loops.return ()))"
     and "Si = S"
      by (auto simp add: loop_def step_io_def from_V_rev)

    show ?thesis
    proof (fuzzy_rule `steps_io progInv qrySpec Si cmd' S' res`)
      show "Si = S" using `Si = S` .
      show "cmd' = body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)"
        using cmd' by (auto simp add: loop_def intro: arg_cong)
    qed
  qed
next
  assume a: "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) S' res"

  show "steps_io progInv qrySpec S (loop body) S' res"
  proof (rule steps_io_step)
    show "steps_io progInv qrySpec S (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) S' res"
      using a.
    show "step_io progInv qrySpec S (loop body) ??? S
     (body \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop body)) True"
      by (auto simp add: loop_def  step_io_def from_V_rev intro: arg_cong)
  qed
qed

lemma steps_io_return:
  assumes "steps_io progInv qrySpec S (return r) S' res"
shows "S = S' \<and> res \<triangleq> r"
  using assms by cases (auto simp add: return_def step_io_def)


lemma steps_io_return_iff:
  shows "steps_io progInv qrySpec S (return r) S' res \<longleftrightarrow> S = S' \<and> res \<triangleq> r"
proof 
  show "steps_io progInv qrySpec S (impl_language_loops.return r) S' res \<Longrightarrow> S = S' \<and> res \<triangleq> r"
    by (erule steps_io_return)

  show "S = S' \<and> res \<triangleq> r \<Longrightarrow> steps_io progInv qrySpec S (impl_language_loops.return r) S' res"
    by (simp add: return_def steps_io_final)
qed


lemma if_distrib_bind:
"((if c then A else B) \<bind>io cont) = (if c then A \<bind>io cont else B \<bind>io cont)"
  by auto

lemma loop_steps:
  assumes "steps_io progInv qrySpec S (loop bdy) S' res"
and "LoopInv S"
and "\<And>S Sb br. \<lbrakk>LoopInv S; steps_io progInv qrySpec S bdy Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some True \<Rightarrow> P Sb | Some False \<Rightarrow> LoopInv Sb "
shows "P S' \<and> res = Some ()"
proof -

  define cmd where "cmd = (loop bdy)"

  obtain bdyCont 
    where "bdyCont = return False"
       and cmd: "cmd = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)"
    by (auto simp add: cmd_def)

  have p1: "\<And>Sb br. \<lbrakk>steps_io progInv qrySpec S bdyCont Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some True \<Rightarrow> P Sb | Some False \<Rightarrow> LoopInv Sb"
    using \<open>bdyCont = impl_language_loops.return False\<close> assms(2) steps_io_return by force

  have p2: "steps_io progInv qrySpec S cmd S' res"
    using `steps_io progInv qrySpec S (loop bdy) S' res` cmd_def by simp

  have "P S' \<and> res = Some ()"
    if "steps_io progInv qrySpec S cmd S' res"
      and "cmd = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)"
      and "\<And>Sb br. \<lbrakk>steps_io progInv qrySpec S bdyCont Sb br\<rbrakk> 
   \<Longrightarrow> case br of None \<Rightarrow> False | Some True \<Rightarrow> P Sb | Some False \<Rightarrow> LoopInv Sb"
    using that proof (induct arbitrary: bdyCont )
    case (steps_io_final S res)
    from `WaitReturn res = bdyCont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)`
    have "bdyCont = return True"
      by (smt WaitReturn_combined impl_language_loops.io.distinct(41) impl_language_loops.return_def loop_def)

    hence "steps_io progInv qrySpec S bdyCont S (Some True)"
      by (simp add: steps_io_return_iff)

    thus ?case
      using  steps_io_final.prems(2) by force 
  next
    case (steps_io_error S cmd action S' cmd')
    from `step_io progInv qrySpec S cmd action S' cmd' False`
    have "\<exists>cmd'. step_io progInv qrySpec S bdyCont action S' cmd' False"
      unfolding `cmd = bdyCont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)`
      by (cases bdyCont, auto simp add: step_io_def return_def loop_def split: prod.splits if_splits)
    hence "steps_io progInv qrySpec S bdyCont S' None"
      using steps_io.steps_io_error by blast
    hence False
      using steps_io_error.prems(2) by force
    thus ?case ..
  next
    case (steps_io_step Sx cmd1 action Sx' cmd' Sx'' res bdyCont )

    thm steps_io_step.prems

    show ?case
    proof (cases "\<exists>r. bdyCont = return r")
      case True \<comment> \<open>Loop iteration done\<close>
      from this
      obtain bdyR where "bdyCont = return bdyR"
        by blast
      show "?thesis"
      proof (cases bdyR)
        case True \<comment> \<open>Loop done\<close>
        hence "bdyCont = return True"
          using `bdyCont = return bdyR` by simp


        with `cmd1 = bdyCont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)`
        have "cmd1 = return ()"
          by auto

        with `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
        have False \<comment> \<open>Actually this case is handled in steps-io-final as not step is done.\<close>
          by (auto simp add: step_io_def return_def)

        thus ?thesis ..
      next
        case False \<comment> \<open>Start loop again.\<close>
        hence "bdyCont = return False"
          using `bdyCont = return bdyR` by simp

        with `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
        have "cmd1 = loop bdy"
          by auto

        with `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
        have "cmd' = bdy \<bind> (\<lambda>r. if r then return () else loop bdy)"
          and "Sx' = Sx"
          by (auto simp add: loop_def step_io_def from_V_rev intro: arg_cong)

        show ?thesis
          using `cmd' = bdy \<bind> (\<lambda>r. if r then return () else loop bdy)`
        proof (rule steps_io_step)  

          show "case br of None \<Rightarrow> False | Some True \<Rightarrow> P Sb | Some False \<Rightarrow> LoopInv Sb"
            if c0: "steps_io progInv qrySpec Sx' bdy Sb br"
            for  Sb br
            by (metis \<open>Sx' = Sx\<close> \<open>bdyCont = impl_language_loops.return False\<close> assms(3)  impl_language_loops.return_def old.bool.simps(4) option.simps(5) steps_io_final steps_io_step.prems(2) that)
        qed
      qed
    next
      case False
      hence "\<nexists>r. bdyCont = impl_language_loops.return r" .

      with `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
        and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
      obtain bdyCont'
        where "cmd' = bdyCont' \<bind> (\<lambda>r. if r then return () else loop bdy)"
          and "step_io progInv qrySpec Sx bdyCont action Sx' bdyCont' True"
      proof (atomize_elim)

        show "\<exists>bdyCont'. cmd' = bdyCont' \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)
          \<and>  step_io progInv qrySpec Sx bdyCont action Sx' bdyCont' True"
        proof (cases bdyCont)

          case (WaitLocalStep x1)
          then show ?thesis 
            using `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
            by (auto simp add: step_io_def split: prod.splits)
        next
          case (WaitBeginAtomic x2)
          then show ?thesis
            using `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
            by (auto simp add: step_io_def intro!: exI split: prod.splits)

        next
          case (WaitEndAtomic x3)
          then show ?thesis using `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
            by (auto simp add: step_io_def split: prod.splits)
        next
          case (WaitNewId x41 x42)
          then show ?thesis using `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
            by (auto simp add: step_io_def split: prod.splits)
        next
          case (WaitDbOperation x51 x52)
          then show ?thesis using `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
            by (auto simp add: step_io_def split: prod.splits)
        next
          case (WaitReturn x6)
          with ` \<nexists>r. bdyCont = impl_language_loops.return r`
          have False
            by (auto simp add: return_def)
          thus ?thesis ..
        next
          case (Loop Lbdy Lcont)
          with `step_io progInv qrySpec Sx cmd1 action Sx' cmd' True`
              and `cmd1 = bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)`
          have "bdyCont = Loop Lbdy Lcont"
            and cmd'1: "cmd' =
               from_V Lbdy \<bind>
               (\<lambda>r. if r then Lcont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)
                    else Loop Lbdy (Lcont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)))"
            and "Sx' = Sx"
            and s: "step_io progInv qrySpec Sx bdyCont action Sx' (from_V Lbdy \<bind> (\<lambda>r. if r then Lcont else Loop Lbdy Lcont)) True"
            by (auto simp add: step_io_def)


          have cmd'2:
            "cmd' =
               (from_V Lbdy \<bind>
                (\<lambda>r. if r then Lcont else Loop Lbdy Lcont)) \<bind> 
                  (\<lambda>r. if r then impl_language_loops.return () else loop bdy)"
            by (auto simp add: cmd'1  intro!: arg_cong[where f="bind (from_V Lbdy)"])

          show ?thesis
          proof (intro exI conjI)
            show "cmd' =
               (from_V Lbdy \<bind>
                (\<lambda>r. if r then Lcont else Loop Lbdy Lcont)) \<bind> 
                  (\<lambda>r. if r then impl_language_loops.return () else loop bdy)" using cmd'2 .

            show "step_io progInv qrySpec Sx bdyCont action Sx' (from_V Lbdy \<bind> (\<lambda>r. if r then Lcont else Loop Lbdy Lcont)) True"
              using s.
          qed
        qed
      qed

      thm steps_io_step.prems

      show ?thesis 
        using `cmd' = bdyCont' \<bind> (\<lambda>r. if r then return () else loop bdy)`
      proof (rule steps_io_step.hyps(3)) 

        show "case br of None \<Rightarrow> False | Some True \<Rightarrow> P Sb | Some False \<Rightarrow> LoopInv Sb"
          if c0: "steps_io progInv qrySpec Sx' bdyCont' Sb br"
          for  Sb br

        proof (rule steps_io_step)
          show "steps_io progInv qrySpec Sx bdyCont Sb br"
          proof (rule steps_io.steps_io_step)

            show "steps_io progInv qrySpec Sx' bdyCont' Sb br"
              using `steps_io progInv qrySpec Sx' bdyCont' Sb br` .

            from `step_io progInv qrySpec Sx cmd1    action Sx' cmd'     True`
            have s: "step_io progInv qrySpec Sx (bdyCont \<bind> (\<lambda>r. if r then return () else loop bdy)) action
                                            Sx' (bdyCont' \<bind> (\<lambda>r. if r then return () else loop bdy)) True"
              unfolding `cmd1 = bdyCont \<bind> (\<lambda>r. if r then impl_language_loops.return () else loop bdy)` 
                `cmd' = bdyCont' \<bind> (\<lambda>r. if r then return () else loop bdy)` .

            show "step_io progInv qrySpec Sx bdyCont action Sx' bdyCont' True"
              using `step_io progInv qrySpec Sx bdyCont action Sx' bdyCont' True` .
          qed
        qed
      qed
    qed
  qed

  thus "P S' \<and> res \<triangleq> ()"
    using p1 cmd p2 by blast
qed


lemma execution_s_check_loop:
  assumes 
inv_pre: "LoopInv PS PS"
and cont: "
\<And>PSl. \<lbrakk>
  LoopInv PS PSl
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec  PSl body 
    (\<lambda>PS' r. if r then execution_s_check Inv crdtSpec PS' (cont ()) P
             else LoopInv PS PS' )"
shows "execution_s_check Inv crdtSpec PS (loop_a LoopInv body \<bind> cont) P"
  unfolding execution_s_check_def proof (intro allI impI)
  fix S' res
  assume steps_io: "steps_io Inv crdtSpec PS (loop_a LoopInv body \<bind> cont) S' res"
    and PS_wf: "proof_state_wellFormed' PS"

  from steps_io_bind_split[OF steps_io]
  obtain Si
    where cases: "(steps_io Inv crdtSpec PS (loop_a LoopInv body) Si (Some ())
                 \<and> steps_io Inv crdtSpec Si (cont ()) S' res) 
            \<or> (steps_io Inv crdtSpec PS (loop_a LoopInv body) Si None)"
    by auto

  text "loop maintains the invariant"
  have "case loopR of None \<Rightarrow> False 
      | Some True \<Rightarrow> execution_s_check Inv crdtSpec PS' (cont ()) P 
      | Some False \<Rightarrow> LoopInv PS PS'"
    if "LoopInv PS PSl"
      and "proof_state_wellFormed' PS"
      and "steps_io Inv crdtSpec PS body PS' loopR"
    for PSl PS' loopR
    by (smt PS_wf cont inv_pre option.case_eq_if that use_execution_s_check)

  define Pl where "Pl \<equiv> (\<lambda>Si. \<forall>S' res.
    steps_io Inv crdtSpec Si (cont ()) S' res \<longrightarrow>  
      (case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r))"

  {
    fix r
    assume steps_loop: "steps_io Inv crdtSpec PS (loop body) Si r"
    from this
    have "Pl Si \<and> r \<triangleq> ()"
    proof (rule loop_steps[where LoopInv="\<lambda>PSl. LoopInv PS PSl \<and> proof_state_wellFormed' PSl"])
      show "LoopInv PS PS \<and> proof_state_wellFormed' PS"
        by (simp add: inv_pre PS_wf)


      show "case br of None \<Rightarrow> False | Some True \<Rightarrow> Pl Sb | Some False \<Rightarrow> LoopInv PS Sb \<and> proof_state_wellFormed' Sb"
        if "LoopInv PS S \<and> proof_state_wellFormed' S"
          and steps: "steps_io Inv crdtSpec S body Sb br"
        for  S Sb br
      proof -
        from  that
        have inv: "LoopInv PS S" and wf: "proof_state_wellFormed' S" 
          by auto

        from cont[OF inv]
        have check: "execution_s_check Inv crdtSpec S body
           (\<lambda>PS' r. if r then execution_s_check Inv crdtSpec PS' (cont ()) P else LoopInv PS PS')".

        from use_execution_s_check[OF check, OF steps, OF wf]
        have c: "case br of None \<Rightarrow> False | Some r \<Rightarrow> if r then execution_s_check Inv crdtSpec Sb (cont ()) P else LoopInv PS Sb" .

        show "case br of None \<Rightarrow> False | Some True \<Rightarrow> Pl Sb | Some False \<Rightarrow> LoopInv PS Sb \<and> proof_state_wellFormed' Sb"
        proof (cases br)
          case None
          thus ?thesis
            using c by auto
        next
          case (Some brv)
          hence [simp]: "br \<triangleq> brv" by simp
          show ?thesis
          proof (cases brv)
            case True
            hence [simp]: "brv = True" by simp
            from c
            have "execution_s_check Inv crdtSpec Sb (cont ()) P" by auto

            show ?thesis 
            proof auto
              show "Pl Sb" 
                unfolding Pl_def proof auto


                show "case res of None \<Rightarrow> False | Some x \<Rightarrow> P S' x"
                  if  "steps_io Inv crdtSpec Sb (cont ()) S' res"
                  for  S' res
                  using c local.wf steps steps_io_wf_maintained that use_execution_s_check by fastforce
              qed
            qed
          next
            case False
            hence [simp]: "\<not>brv" .

            show ?thesis 
            proof auto
              show "LoopInv PS Sb"
                using c by auto
              show "proof_state_wellFormed' Sb"
                using local.wf steps steps_io_wf_maintained' by fastforce
            qed
          qed
        qed
      qed
    qed
  }
  note loop_correct =  this

  from cases
  show "case res of None \<Rightarrow> False | Some r \<Rightarrow> P S' r"
  proof (rule disjE; clarsimp?)
    \<comment> \<open>First the case where the loop finishes successfully\<close>
    assume steps_loop: "steps_io Inv crdtSpec PS (loop_a LoopInv body) Si (Some ())"
      and steps_cont: "steps_io Inv crdtSpec Si (cont ()) S' res"
    hence steps_loop': "steps_io Inv crdtSpec PS (loop body) Si (Some ())"
      unfolding loop_a_def by simp

    thm loop_steps
    thm loop_steps[OF steps_loop']

    show "case res of None \<Rightarrow> False | Some x \<Rightarrow> P S' x"
      using Pl_def loop_correct steps_cont steps_loop' by blast
  next
    \<comment> \<open>Next the case where the loop fails:\<close>
    assume "steps_io Inv crdtSpec PS (loop_a LoopInv body) Si None"

    have False
      by (metis \<open>steps_io Inv crdtSpec PS (loop_a LoopInv body) Si None\<close> loop_a_def loop_correct option.discI)

    thus "case res of None \<Rightarrow> False | Some x \<Rightarrow> P S' x" ..
  qed
qed

subsection "References"


lemma execution_s_check_makeRef:
  assumes cont: "
\<And>ref. \<lbrakk>
  ref = freshRef (dom (ps_store PS))
\<rbrakk> \<Longrightarrow> execution_s_check Inv crdtSpec 
    (PS\<lparr>
      ps_store := (ps_store PS)(ref \<mapsto> intoAny a)
     \<rparr>) 
    (cont (Ref ref)) 
    P"
  shows "execution_s_check Inv crdtSpec PS  (makeRef a \<bind> cont) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>r. makeRef a \<noteq> impl_language_loops.io.WaitReturn r"
    by (simp add: makeRef_def)

  show "ok \<and> (\<exists>res. cmd' = cont res \<and> execution_s_check Inv crdtSpec PS' (cont res) P)"
    if step: "step_io Inv crdtSpec PS (makeRef a \<bind> cont) action PS' cmd' ok"
      and PS_wf: "proof_state_wellFormed' PS"
    for  action PS' cmd' ok
  proof
    have [simp]: "finite (dom (ps_store PS))"
      using PS_wf proof_state_wellFormed'_def by blast



    from step
    have  c0: "action = ALocal True"
      and c1: "ok"
      and c2: "PS' = PS\<lparr>ps_store := ps_store PS(freshRef (dom (ps_store PS)) \<mapsto> intoAny a)\<rparr>"
      and c3: "cmd' = cont (Ref (freshRef (dom (ps_store PS))))"
      by (auto simp add: makeRef_def step_io_def Let_def )

    show "ok" using `ok` .

    show "\<exists>res. cmd' = cont res \<and> execution_s_check Inv crdtSpec PS' (cont res) P"
      using c2 c3 cont by blast
  qed
qed


lemma execution_s_check_read:
  assumes validRef: "iref r \<in> dom (ps_store PS)"
    and cont: "
    execution_s_check Inv crdtSpec 
      PS 
      (cont (s_read (ps_store PS) r))
      P"
  shows "execution_s_check Inv crdtSpec PS  (read r \<bind>io cont) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>ra. read r \<noteq> impl_language_loops.io.WaitReturn ra"
    by (simp add: read_def)

  show "ok \<and> (\<exists>res. cmd' = cont res \<and> execution_s_check Inv crdtSpec PS' (cont res) P)"
    if c0: "step_io Inv crdtSpec PS (read r \<bind> cont) action PS' cmd' ok"
      and c1: "proof_state_wellFormed' PS"
    for  action PS' cmd' ok
    using that validRef cont[simplified s_read_def] by (auto simp add:  step_io_def read_def proof_state_wellFormed'_def intro!: exI)
qed

lemma execution_s_check_assign:
  assumes validRef: "iref r \<in> dom (ps_store PS)"
    and cont: "
    execution_s_check Inv crdtSpec 
      (PS\<lparr>ps_store := ps_store PS(iref r \<mapsto> intoAny v)\<rparr>)
      (cont ())
      P"
  shows "execution_s_check Inv crdtSpec PS  (assign r v \<bind>io cont) P"
proof (rule execution_s_check_proof_rule)
  show "\<And>ra. r :\<leftarrow> v \<noteq> impl_language_loops.io.WaitReturn ra"
    by (simp add: assign_def)

  show "ok \<and> (\<exists>res. cmd' = cont res \<and> execution_s_check Inv crdtSpec PS' (cont res) P)"
    if c0: "step_io Inv crdtSpec PS (r :\<leftarrow> v \<bind> cont) action PS' cmd' ok"
      and c1: "proof_state_wellFormed' PS"
    for  action PS' cmd' ok
    using that validRef cont by (auto simp add:  step_io_def assign_def proof_state_wellFormed'_def )
qed

lemma execution_s_check_return:
  assumes finalCheck: "proof_state_wellFormed' PS \<Longrightarrow> P PS r"
  shows "execution_s_check Inv crdtSpec PS (return r) P"
  using finalCheck
unfolding execution_s_check_def steps_io_return_iff by auto

subsection "Verification Condition Generation Tactics"


lemmas repliss_proof_rules = 
  execution_s_check_makeRef
  execution_s_check_read
  execution_s_check_assign
  execution_s_check_loop
  execution_s_check_return
  show_finalCheck

method repliss_vcg_step1 uses asmUnfold = 
  (rule repliss_proof_rules; ((subst(asm) asmUnfold)+)?; (intro impI conjI)?; clarsimp?; (intro impI conjI)?)

method repliss_vcg_step uses asmUnfold = 
  (repliss_vcg_step1 asmUnfold: asmUnfold; (repliss_vcg_step asmUnfold: asmUnfold)?)

method repliss_vcg_l uses impl asmUnfold = 
  ((simp add: impl)?, (unfold atomic_def skip_def)?, simp? , repliss_vcg_step asmUnfold: asmUnfold)



(*
lemmas execution_s_check_endAtomic' = execution_s_check_endAtomic[rotated 3, OF context_conjI]
  

lemmas repliss_proof_rules = 
  execution_s_check_newId
  execution_s_check_beginAtomic
  execution_s_check_endAtomic'
  execution_s_check_pause
  execution_s_check_dbop
  execution_s_check_return

method repliss_vcg_step = (rule repliss_proof_rules; (intro impI conjI)?; simp?; (intro impI conjI)?;  repliss_vcg_step?)

method repliss_vcg uses impl = ((simp add: impl)?, (unfold atomic_def skip_def)?, simp? , repliss_vcg_step)
*)

declare newId_def[language_construct_defs] 
atomic_def[language_construct_defs]  
beginAtomic_def [language_construct_defs] 
call_def [language_construct_defs] 
skip_def [language_construct_defs] 
endAtomic_def [language_construct_defs] 
return_def[language_construct_defs] 
makeRef_def[language_construct_defs] 
read_def[language_construct_defs] 
assign_def[language_construct_defs] 
update_def[language_construct_defs]
loop_a_def[language_construct_defs]
\<comment> \<open>loop construct is not added here, since unfolding it might diverge.
    the loops added are just syntactic sugar for loop.\<close>





end