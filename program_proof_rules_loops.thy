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
  \<Rightarrow> ('proc, ('any store \<times> ('any, 'operation, 'any) io), 'operation, 'any) state 
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
       \<and> (\<exists>ps_ls. localState S1 (ps_i S) \<triangleq> (ps_store S, ps_ls))
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
       \<and> (\<forall>v\<in>ps_generatedLocalPrivate S. uid_is_private (ps_i S) (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1) (currentProc S1) v)
       \<and> (finite (dom (ps_store S)))
       \<and> (procedure_cannot_guess_ids (ps_localKnown S) (the (localState S1 (ps_i S))) toImpl)
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

inductive step_s_cmd where
step_s_cmd_refl:
"step_s_cmd S i [] S (WaitReturn res) res"
| steps_s_cmd_step:
"\<lbrakk>
S ~~ (i, a) \<leadsto>\<^sub>S S';
localState S i \<triangleq> (store, c);
toImpl (store, cmd) = la;
step_s_cmd S' i tr S'' cmd2 res
\<rbrakk> \<Longrightarrow> step_s_cmd S i (a#tr) S'' cmd res " 


fun io_nested :: "('a,'operation, 'any) io \<Rightarrow> ('a,'operation, 'any) io set" where
  "io_nested (WaitLocalStep n)  = (snd ` snd ` range n)"
| "io_nested (WaitBeginAtomic n)  =  {n}"
| "io_nested (WaitEndAtomic n)  = {n} "
| "io_nested (WaitNewId P n)  =  range n"
| "io_nested (WaitDbOperation op n)  =  range n"
| "io_nested (WaitReturn s)  =  {}"
| "io_nested (Loop body n)  = {n}" \<comment> \<open>n, from_V body\<close>

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
  \<Rightarrow> ('proc, 'operation, 'any) action
  \<Rightarrow> ('proc, 'any, 'operation) proof_state
  \<Rightarrow> ('a, 'operation, 'any) io
  \<Rightarrow> bool \<comment> \<open>step is correct\<close>
  \<Rightarrow> bool " where
"step_io progInv qrySpec S cmd action S' cmd' Inv \<equiv> 
  case cmd of
    WaitLocalStep cont \<Rightarrow> 
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
       ps_tx S \<noteq> None
       \<and> (\<exists>c res. 
        calls S c = None
         \<and> qrySpec oper (getContextH (calls S) (updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)) (Some (ps_vis S \<union> set (ps_localCalls S)))) res
         \<and> cmd' = n res
         \<and> (S' = S\<lparr>
            ps_localKnown := ps_localKnown S \<union> uniqueIds res, 
            ps_generatedLocalPrivate := ps_generatedLocalPrivate S - uniqueIds oper,
            calls := (calls S)(c \<mapsto> Call oper res),
            ps_localCalls := ps_localCalls S @ [c]
          \<rparr>)
        )
  | Loop body n \<Rightarrow> 
      cmd' = from_V body \<bind> (\<lambda>r. if r then n else Loop body n)
      \<and> (S' = S)
"

\<comment> \<open>TODO: I could extract definitions for the individual cases above to make this shorter.\<close>


\<comment> \<open>TODO: steps_io: inductive definition for combining multiple steps and getting 
  a result value (from WaitReturn)\<close>


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
"currentCommand S i \<equiv> snd (the (localState S i))"



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


  have ls[simp]: "localState S i \<triangleq> (ps_store PS, cmd \<bind> cmdCont)"
    using cmd_prefix i_def proof_state_rel_fact(10) rel by force

  have "state_wellFormed S"
    using proof_state_rel_fact(1) rel by auto
  hence "state_wellFormed S'"
    using local.step state_wellFormed_combine_s1 by blast


  have [simp]: "invocationOp S i \<noteq> None"
    by (simp add: \<open>state_wellFormed S\<close> wf_localState_to_invocationOp)

  have [simp]: "finite (dom (ps_store PS))"
    using proof_state_rel_fact(25) rel by blast


    have no_guess: "(procedure_cannot_guess_ids (ps_localKnown PS) (the (localState S (ps_i PS))) toImpl)"
      by (simp add: proof_state_rel_fact[OF rel])

    have "(the (localState S (ps_i PS))) = (ps_store PS, cmd \<bind> cmdCont)"
    using i_def ls by auto
    
    
  have uniqueIdCases1:
       "  (\<exists> ok ls' . toImpl (the (localState S (ps_i PS))) = LocalStep ok ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
        \<or> (\<exists>ls'.    toImpl (the (localState S (ps_i PS))) = BeginAtomic ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
        \<or> (\<exists> ls'.   toImpl (the (localState S (ps_i PS))) = EndAtomic ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
        \<or> (\<exists>  f . toImpl (the (localState S (ps_i PS))) = NewId f \<and> (\<forall> uid ls'. f uid \<triangleq> ls' \<longrightarrow> procedure_cannot_guess_ids ((ps_localKnown PS) \<union> uniqueIds uid) ls' toImpl ))
        \<or> (\<exists>  opr f . toImpl (the (localState S (ps_i PS))) = DbOperation opr f \<and> uniqueIds opr \<subseteq> (ps_localKnown PS) \<and> (\<forall> res. procedure_cannot_guess_ids ((ps_localKnown PS) \<union> uniqueIds res) (f res) toImpl ))
        \<or> (\<exists>  r . toImpl (the (localState S (ps_i PS))) = Return r \<and> uniqueIds r \<subseteq> (ps_localKnown PS))"
    by (rule procedure_cannot_guess_ids.cases[OF no_guess, simplified], auto)

    
  hence uniqueIdCases:
     "  (\<exists> ok ls' . toImpl (ps_store PS, cmd \<bind> cmdCont) = LocalStep ok ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
      \<or> (\<exists>ls'.    toImpl (ps_store PS, cmd \<bind> cmdCont) = BeginAtomic ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
      \<or> (\<exists> ls'.   toImpl (ps_store PS, cmd \<bind> cmdCont) = EndAtomic ls' \<and> procedure_cannot_guess_ids (ps_localKnown PS) ls' toImpl)
      \<or> (\<exists>  f . toImpl (ps_store PS, cmd \<bind> cmdCont) = NewId f \<and> (\<forall> uid ls'. f uid \<triangleq> ls' \<longrightarrow> procedure_cannot_guess_ids ((ps_localKnown PS) \<union> uniqueIds uid) ls' toImpl ))
      \<or> (\<exists>  opr f . toImpl (ps_store PS, cmd \<bind> cmdCont) = DbOperation opr f \<and> uniqueIds opr \<subseteq> (ps_localKnown PS) \<and> (\<forall>res. procedure_cannot_guess_ids ((ps_localKnown PS) \<union> uniqueIds res) (f res) toImpl ))
      \<or> (\<exists>  r . toImpl (ps_store PS, cmd \<bind> cmdCont) = Return r \<and> uniqueIds r \<subseteq> (ps_localKnown PS))"
      by (auto simp add: `(the (localState S (ps_i PS))) = (ps_store PS, cmd \<bind> cmdCont)`)

      
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
      have toImpl: "toImpl (ps_store PS, cmd \<bind> cmdCont) = LocalStep ok ls'"
        and ls_parts: "ls = (ps_store PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto

      from toImpl
      obtain ok' store' cmd'
        where c0: "n (ps_store PS) = (ok', store', cmd')"
          and c1: "ls' = (store', cmd' \<bind> cmdCont)"
          and c2: "ok = (ok' \<and> finite (dom store'))"
        by (auto simp add: WaitLocalStep split: prod.splits)


      have  cmd_def[simp]: "cmd = impl_language_loops.io.WaitLocalStep n"
        by (simp add: WaitLocalStep)
      have action_def: "action = ALocal Inv"
        using A(7) A(8) by auto

      have Inv: "Inv \<longleftrightarrow> (ok \<and> finite (dom (store')))"
        using A(8) c2 by blast
      have S'_def: "S' = S\<lparr>localState := localState S(i \<mapsto> (store', cmd' \<bind> cmdCont))\<rparr>"
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

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
       uid_is_private (ps_i PS') (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
        (localState S') (currentProc S') v"
            apply (auto simp add: i_def S'_def PS'_def proof_state_rel_fact[OF rel]  split: option.splits)
            by (smt fun_upd_apply new_unique_not_in_other_invocations_def proof_state_rel_def rel uid_is_private_def)

          show "finite (dom (ps_store PS'))"
            by (auto simp add: PS'_def)

            
          show "procedure_cannot_guess_ids (ps_localKnown PS') (the (localState S' (ps_i PS'))) toImpl"
            using uniqueIdCases[simplified toImpl, simplified]
            by (auto simp add: PS'_def S'_def i_def c1)
            
            
            
            
            
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
      case (A S1 i' ls f ls' t Sn Sf vis vis' txns)

      have [simp]: "ps_localCalls PS = []"
        using A(26) A(8) i_def proof_state_rel_fact(13) proof_state_rel_fact(15) rel by fastforce

      have [simp]: "i' = ps_i PS"
        using A(26) i_def by blast

      have [simp]: "ls' = (ps_store PS, n \<bind> cmdCont)"
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
          have uid_private: "uid_is_private (ps_i PS) (calls S) (invocationOp S) (invocationRes S) 
                                      (knownIds S) (generatedIds S) (localState S) (currentProc S) v"
            if "v \<in> ps_generatedLocalPrivate PS"
            for v
            using that by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
               uid_is_private (ps_i PS') (calls Sf) (invocationOp Sf) (invocationRes Sf) (knownIds Sf) (generatedIds Sf)
                (localState Sf) (currentProc Sf) v"
          proof (rule ballI)
            fix v
            assume v_priv: "v \<in> ps_generatedLocalPrivate PS'"

            from `state_monotonicGrowth i' S Sn`
            have "uid_is_private i' (calls Sn) (invocationOp Sn) (invocationRes Sn) (knownIds Sn) (generatedIds Sn)
               (localState Sn) (currentProc Sn) v"
            proof (rule growth_still_hidden)
              show "program_wellFormed (prog S)"
                by (simp add: prog_wf)
              show "uid_is_private i' (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S)
               (currentProc S) v"
              proof (fuzzy_rule uid_private)
                show "v \<in> ps_generatedLocalPrivate PS"
                  using v_priv by (auto simp add: PS'_def)
                show "ps_i PS = i'" by simp
              qed
            qed


            from this
            show "uid_is_private (ps_i PS') (calls Sf) (invocationOp Sf) (invocationRes Sf) (knownIds Sf) (generatedIds Sf)
            (localState Sf) (currentProc Sf) v"
              by (auto simp add: PS'_def A new_unique_not_in_other_invocations_def uid_is_private_def)
          qed 

          have toImpl_ba: "toImpl (ps_store PS, cmd \<bind> cmdCont) = BeginAtomic (ps_store PS, n \<bind> cmdCont)"
          using toImpl `f ls = BeginAtomic ls'` `currentProc S i' \<triangleq> f` `localState S i' \<triangleq> ls` i_def ls
          by auto
          
          have ls_Sf: "localState Sf (ps_i PS) \<triangleq> (ps_store PS, n \<bind> cmdCont)"
            by (auto simp add: A)
          
          show "procedure_cannot_guess_ids (ps_localKnown PS') (the (localState Sf (ps_i PS'))) impl_language_loops.toImpl"
            using uniqueIdCases[simplified toImpl, simplified]
            by (auto simp add: PS'_def  i_def toImpl_ba ls_Sf)
            
          show "ps_generatedLocal PS' \<subseteq> ps_localKnown PS'"
            using \<open>ps_generatedLocal PS \<subseteq> ps_localKnown PS\<close> PS'_def by auto
            
            
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

          show "action = ABeginAtomic t txns"
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
      have toImpl: "toImpl (ps_store PS, cmd \<bind> cmdCont) = EndAtomic ls'"
        and ls_parts: "ls = (ps_store PS, cmd \<bind> cmdCont)"
        using `i' = i` by auto




      from toImpl
      have ls'_def: "ls' = (ps_store PS, n \<bind> cmdCont)"
        by (auto simp add: WaitEndAtomic)

      have S''_def: "S'' = S
    \<lparr>localState := localState S(i' \<mapsto> ls'), currentTransaction := (currentTransaction S)(i' := None),
       transactionStatus := transactionStatus S(t \<mapsto> Committed)\<rparr>"
        using A by auto

      have [simp]: "localState S' (ps_i PS) \<triangleq> (ps_store PS, n \<bind> cmdCont)"
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

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_ls)"
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

          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
       uid_is_private (ps_i PS') (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
        (localState S') (currentProc S') v"
            apply (auto simp add: PS'_def  `S' = S''` S''_def)
            by (smt \<open>i' = ps_i PS\<close> fun_upd_apply new_unique_not_in_other_invocations_def proof_state_rel_def rel uid_is_private_def)

            
          show "procedure_cannot_guess_ids (ps_localKnown PS') (the (localState S' (ps_i PS'))) impl_language_loops.toImpl"
            using uniqueIdCases[simplified toImpl, simplified]
            by (auto simp add: PS'_def  i_def  ls'_def)
            

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


      have ls''_def: "ls'' = (ps_store PS, n uidv \<bind> cmdCont)"
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


        have uid_priv: "uid_is_private (ps_i PS) (calls PS) (invocationOp PS) (invocationRes PS) (knownIds PS)
             (generatedIds S(uid \<mapsto> i')) (localState S(i' \<mapsto> ls'')) (currentProc S) uid"
          apply (auto simp add: uid_is_private_def \<open>i' = ps_i PS\<close>)
          using A(5) \<open>state_wellFormed S\<close> new_unique_not_in_invocationOp_def prog_wf proof_state_rel_fact(7) rel wf_onlyGeneratedIdsInInvocationOps apply fastforce
              apply (metis (no_types, lifting) A(5) \<open>state_wellFormed S\<close> new_unique_not_in_calls_def prog_wf proof_state_rel_fact(2) rel wf_onlyGeneratedIdsInCalls)
          using A(5) \<open>state_wellFormed S\<close> new_unique_not_in_calls_result_def prog_wf proof_state_rel_fact(2) rel wf_onlyGeneratedIdsInCallResults apply fastforce
          using A(5) \<open>state_wellFormed S\<close> new_unique_not_in_invocationRes_def prog_wf proof_state_rel_fact(8) rel wf_onlyGeneratedIdsInInvocationRes apply fastforce
          using A(5) \<open>state_wellFormed S\<close> prog_wf proof_state_rel_fact(6) rel wf_onlyGeneratedIdsInKnownIds apply blast
          by (smt A(5) Un_iff \<open>state_wellFormed S\<close> domIff fun_upd_apply new_unique_not_in_other_invocations_def prog_wf subset_Un_eq wf_knownIds_subset_generatedIds_h(1))


        show "proof_state_rel PS' S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)
          show "state_wellFormed S'"
            using S'_wf by simp

          show "ps_generatedLocal PS' = {x. generatedIds S' x \<triangleq> ps_i PS'}"
            apply (auto simp add: PS'_def S'_def `i' = ps_i PS`)
            using proof_state_rel_fact(9) rel apply auto[1]
            using proof_state_rel_fact(9) rel by auto

          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_ls)"
            by (auto simp add: PS'_def S'_def `i' = ps_i PS` ls''_def)




          show "\<forall>v\<in>ps_generatedLocalPrivate PS'.
           uid_is_private (ps_i PS') (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
            (localState S') (currentProc S') v"
            apply (auto simp add: i_def S'_def PS'_def proof_state_rel_fact[OF rel] uid_priv  split: option.splits)
            by (smt \<open>i' = ps_i PS\<close> map_upd_Some_unfold new_unique_not_in_other_invocations_def proof_state_rel_def rel uid_is_private_def)


          have toImpl_ls: "toImpl (ps_store PS, cmd \<bind> cmdCont) = NewId ls'"
            using A(10) A(2) A(3) A(4) i_def ls toImpl by auto
            

          have ls''_def: "ls'' = (the (localState S' (ps_i PS)))"
            by (auto simp add: S'_def \<open>i' = ps_i PS\<close>)
          
            
            
          show "procedure_cannot_guess_ids (ps_localKnown PS') (the (localState S' (ps_i PS'))) impl_language_loops.toImpl"
            using uniqueIdCases[simplified toImpl, simplified]
            apply (auto simp add: PS'_def  i_def  toImpl_ls)
            apply (drule_tac x=uidv in spec)
            apply (auto simp add: `ls' uidv \<triangleq> ls''` ls''_def `uniqueIds uidv = {uid}`)
            by (metis old.prod.exhaust)
            
            

        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: i_def  S'_def PS'_def  split: option.splits)[1]); fail)+

            
            
        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' cmd' Inv"
        proof (auto simp add: step_io_def WaitNewId, intro exI conjI)
          show "action = ANewId uidv"
            by (simp add: A(11))

          from `f ls = NewId ls'`
          have "toImpl ls = NewId ls'"
            using A(3) \<open>i' = ps_i PS\<close> toImpl by auto


          have ls_def: "ls = (ps_store PS, cmd \<bind> cmdCont)"
            using A(10) A(2) ls by auto



          show "cmd' = n uidv"
            using cmd'_def by simp




          show "uniqueIds uidv = {uid}"
            by (simp add: A(6))

          show "uid \<notin> ps_generatedLocal PS"
            using A(5) proof_state_rel_fact(9) rel by fastforce

          show "uid_fresh uid PS"
            by (meson uid_fresh_def uid_is_private'_implies uid_priv)

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
    proof (cmd_step_cases step: step insert: cmd_prefix simps: WaitDbOperation)
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
        using A(2) A(3) A(4) WaitDbOperation i_def ls toImpl by auto


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
          using A(2) A(3) A(4) WaitDbOperation i_def ls toImpl by auto

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

            
          show "\<exists>ps_ls. localState S' (ps_i PS') \<triangleq> (ps_store PS', ps_ls)"
            using A(2) A(3) A(4) WaitDbOperation ls toImpl by (auto simp add: S'_def PS'_def)

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

          hence "procedures_cannot_guess_ids (procedure (prog S'))" 
            and "queries_cannot_guess_ids (querySpec (prog S'))"
            by (auto simp add: program_wellFormed_def)


          have toImpl_db: "toImpl (ps_store PS, cmd \<bind> cmdCont) = DbOperation Op ls'"
            using toImpl `currentProc S i' \<triangleq> f` `f ls = DbOperation Op ls'` `localState S i' \<triangleq> ls` ls by auto
            


          have "localState S' i' \<triangleq> ls' res" 
            by (auto simp add: S'_def )
            
          show "procedure_cannot_guess_ids (ps_localKnown PS') (the (localState S' (ps_i PS'))) impl_language_loops.toImpl"
          using uniqueIdCases[simplified toImpl, simplified]
           by (auto simp add: PS'_def  i_def toImpl_db `localState S' i' \<triangleq> ls' res` )

          from uniqueIdCases[simplified toImpl, simplified]
          have "uniqueIds Op \<subseteq> ps_localKnown PS"
            by (auto simp add: PS'_def  i_def toImpl_db `localState S' i' \<triangleq> ls' res` )

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
            uid_is_private (ps_i PS') (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
            (localState S') (currentProc S') v"
            proof (auto simp add: PS'_def S'_def)
            fix v
            assume "v \<in> ps_generatedLocalPrivate PS"
            and "v \<notin> uniqueIds Op"

            have "v \<in> ps_localKnown PS"
               using \<open>v \<in> ps_generatedLocalPrivate PS\<close> proof_state_rel_fact(23) proof_state_rel_fact(27) rel by blast
            
            have old: "uid_is_private i' (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S)
            (localState S) (currentProc S) v"
              using A(10) \<open>v \<in> ps_generatedLocalPrivate PS\<close> i_def proof_state_rel_fact(24) rel by blast
            
            
            show "uid_is_private i' (calls S(c \<mapsto> Call Op res)) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S)
            (localState S(i' \<mapsto> ls' res)) (currentProc S) v"
            proof (auto simp add: uid_is_private_def; ((insert old, auto simp add: uid_is_private_def); fail)?)
            
              have "new_unique_not_in_calls (calls S) v"
                by (meson old uid_is_private_def) 
              thus "new_unique_not_in_calls (calls S(c \<mapsto> Call Op res)) v" 
                by (auto simp add: new_unique_not_in_calls_def \<open>v \<notin> uniqueIds Op\<close>)
              
              have "new_unique_not_in_calls_result (calls S) v"
                by (meson old uid_is_private_def)
              thus "new_unique_not_in_calls_result (calls S(c \<mapsto> Call Op res)) v" 
                apply (auto simp add: new_unique_not_in_calls_result_def \<open>v \<notin> uniqueIds Op\<close>)
                apply (frule uniqueIdsRes)
                apply (rule `v \<notin> uniqueIds Op`)
                apply (auto simp add: getContextH_def restrict_map_def split: option.splits if_splits)
                by (metis \<open>new_unique_not_in_calls (calls S) v\<close> call.exhaust_sel new_unique_not_in_calls_def)
              
              
              
              have "new_unique_not_in_other_invocations i' (localState S) (currentProc S) v"
                by (meson old uid_is_private_def) 
              
              
              show "new_unique_not_in_other_invocations i' (localState S(i' \<mapsto> ls' res)) (currentProc S) v" 
              apply (auto simp add: new_unique_not_in_other_invocations_def )
              by (meson \<open>new_unique_not_in_other_invocations i' (localState S) (currentProc S) v\<close> new_unique_not_in_other_invocations_def)
              
              
              
            qed
          qed

        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: PS'_def S'_def sorted_by_empty)[1]); fail)+
      

        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS' (n res) Inv"
        proof (auto simp add: step_io_def WaitDbOperation; intro exI conjI)
        
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
     qed (auto simp add: PS'_def)
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

      show False
      proof (rule goal, intro exI conjI impI)

        have [simp]: "ps_i PS = i'"
          using A(6) i_def by auto

        


        have toImpl_ls: "toImpl ls = LocalStep ok ls'"
          using `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def)

        have toImpl1: "toImpl (ps_store PS, cmd \<bind> cmdCont) = LocalStep ok ls'"
          using A(2) \<open>the (localState S (ps_i PS)) = (ps_store PS, cmd \<bind> cmdCont)\<close> toImpl_ls by auto


        have ls_S': "localState S' (ps_i PS) \<triangleq> (ps_store PS, from_V body \<bind> (\<lambda>r. if r then n \<bind> cmdCont else Loop body (n \<bind> cmdCont)))"

          using \<open>the (localState S (ps_i PS)) = (ps_store PS, cmd \<bind> cmdCont)\<close> `f ls = LocalStep ok ls'` `currentProc S i' \<triangleq> f` toImpl `localState S i' \<triangleq> ls`
            `currentCommand S i = cmd \<bind> cmdCont` Loop
          by (auto simp add: S'_def )
         


        hence ls_S': "localState S' (ps_i PS) \<triangleq> (ps_store PS, (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) \<bind> cmdCont)"
          apply auto
          by (metis (full_types, hide_lams) impl_language_loops.bind.simps(7))


        show "proof_state_rel PS S'"
          unfolding proof_state_rel_def 
        proof (intro conjI)

          show "state_wellFormed S'"
            by (simp add: \<open>state_wellFormed S'\<close>)

          show " \<exists>ps_ls. localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_ls)"
            using ls_S' by auto

          show "\<forall>v\<in>ps_generatedLocalPrivate PS.
       uid_is_private (ps_i PS) (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
        (localState S') (currentProc S') v"
             proof (intro ballI conjI)
            fix v
            assume "v \<in> ps_generatedLocalPrivate PS"
            hence "uid_is_private (ps_i PS) (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S)
              (localState S) (currentProc S) v"
              using proof_state_rel_fact(24) rel by blast
            thus "uid_is_private (ps_i PS) (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
          (localState S') (currentProc S') v"
              by (auto simp add: S'_def uid_is_private_def new_unique_not_in_other_invocations_def)
          qed

          show "procedure_cannot_guess_ids (ps_localKnown PS) (the (localState S' (ps_i PS))) impl_language_loops.toImpl"
            using uniqueIdCases[simplified toImpl, simplified]
            by (auto simp add:  S'_def i_def toImpl1 )


        qed ((insert proof_state_rel_fact[OF rel], (auto simp add: i_def S'_def   split: option.splits)[1]); fail)+


        show "currentCommand S' i = (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) \<bind> cmdCont"
          using i_def ls_S' by auto

        show "step_io (invariant (prog S)) (querySpec (prog S)) PS cmd action PS
         (from_V body \<bind> (\<lambda>r. if r then n else Loop body n)) Inv"
          by (auto simp add: step_io_def Loop)


      qed
    qed
  qed
qed



definition execution_s_check_final where
"execution_s_check_final trace S' i cont P  \<equiv> 
  traceCorrect_s  trace \<and> 
  (\<forall>PS res. 
          proof_state_rel PS S'
      \<longrightarrow> ps_i PS = i
      \<longrightarrow> ps_ls PS = WaitReturn res \<bind> cont
      \<longrightarrow> P PS res  )"

definition execution_s_check :: "
     ('proc::valueType, 'any::valueType, 'operation::valueType) proof_state 
  \<Rightarrow> ('a \<Rightarrow> ('any, 'operation, 'any) io)
  \<Rightarrow> (('proc::valueType, 'any::valueType, 'operation::valueType) proof_state \<Rightarrow> 'a \<Rightarrow> bool)
  \<Rightarrow> ('a, 'operation, 'any) io  
  \<Rightarrow> bool" where
\<comment> \<open> TODO extract below relation into proof_state_rel \<close>
  "execution_s_check S cont P ls
 \<equiv>  \<forall>trace S1 S'. 
           (S1 ~~ (ps_i S, trace) \<leadsto>\<^sub>S* S')
       \<longrightarrow> (\<forall>p t. (AInvoc p, t) \<notin> set trace)
       \<longrightarrow> proof_state_rel S S1
       \<longrightarrow> (ps_ls S = (ls \<bind> cont))
       \<longrightarrow> (\<forall>store' ls'. localState S' (ps_i S) \<triangleq> (store', ls') \<longrightarrow> (\<exists>x. ls' = x \<bind> cont)) 
       \<longrightarrow> execution_s_check_final trace S' (ps_i S) cont P"




lemmas use_execution_s_check = execution_s_check_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, rotated]

lemma beforeInvoc_execution_s_check: 
  assumes "invocationOp S (ps_i S) = None"
  shows "execution_s_check S cont P ls"
  using assms 
proof (auto simp add: execution_s_check_def steps_s_cons_simp  )
  fix trace S1 S'
  assume a0: "invocationOp S (ps_i S) = None"
    and a1: "S1 ~~ (ps_i S, trace) \<leadsto>\<^sub>S* S'"
    and a2: "\<forall>p t. (AInvoc p, t) \<notin> set trace"
    and a3: "proof_state_rel S S1"
    and a4: "ps_ls S = ls \<bind> cont"


  have "state_wellFormed S1"
    using a3 proof_state_rel_wf by blast

  have "invocationOp S1 (ps_i S) = None"
    using a3 assms proof_state_rel_fact(7) by fastforce

  have
    "localState S1 (ps_i S) \<triangleq> (ps_store S, ps_ls S)"
    by (simp add: a3 proof_state_rel_fact(11))


  have False
    using \<open>invocationOp S1 (ps_i S) = None\<close> \<open>localState S1 (ps_i S) \<triangleq> (ps_store S, ps_ls S)\<close> \<open>state_wellFormed S1\<close> wf_localState_to_invocationOp by fastforce

  thus "execution_s_check_final trace S' (ps_i S) cont P"
    by auto
qed
    








method subst_all uses r = (subst r | subst(asm) r)+

text "Correctness of execution when executing only a prefix of the trace:"


definition "execution_s_correct_p" where
"execution_s_correct_p S i ls1 P \<equiv> 
    \<forall>trace S' store ls2 store' ls1'. 
          (S ~~ (i, trace) \<leadsto>\<^sub>S* S') 
      \<longrightarrow> (localState S i \<triangleq> (store, bind ls1 ls2))
      \<longrightarrow> (localState S' i \<triangleq> (store', bind ls1' ls2))
      \<longrightarrow> traceCorrect_s trace \<and> (\<forall>res. ls1' = WaitReturn res \<longrightarrow>  P S' res)"

lemmas use_execution_s_correct_p = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format]

lemmas use_execution_s_correct_p_trace = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct1]

lemmas use_execution_s_correct_p_P = 
  execution_s_correct_p_def[THEN meta_eq_to_obj_eq, THEN iffD1, rule_format, THEN conjunct2, rule_format]

lemma execution_s_correct_to_p:
  assumes ec_p: "execution_s_correct_p S i ls1 P"
    and S_ls: "localState S i \<triangleq> (store, ls1)"
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

    have "localState S i \<triangleq> (store, ls1 \<bind> impl_language_loops.return)"
      using S_ls by auto

    show ?case 
    proof (auto simp add: traceCorrect_s_def IH)
      fix x
      assume "a = (x, False)"



      show False
      proof (cases "localState S'' i")
        case None

        from `a = (x, False)` `S' ~~ (i, a) \<leadsto>\<^sub>S S''` `localState S'' i = None` `currentProc S' i \<triangleq> toImpl`
        obtain store'' ls'' res
          where a0: "a = (AReturn res, False)"
            and a1: "x = AReturn res"
            and not_invariant: "\<not> invariant (prog S')             (invContextH (callOrigin S') (transactionOrigin S') (transactionStatus S') (happensBefore S')               (calls S') (knownIds S' \<union> uniqueIds res) (invocationOp S') (invocationRes S'(i \<mapsto> res)))"
            and a3: "localState S' i \<triangleq> (store'', ls'')"
            and a4: "currentProc S' i \<triangleq> toImpl"
            and a5: "toImpl (store'', ls'') = Return res"
            and a6: "currentTransaction S' i = None"
            and S''_def: "S'' = S'         \<lparr>localState := (localState S')(i := None), currentProc := (currentProc S')(i := None),            visibleCalls := (visibleCalls S')(i := None), invocationRes := invocationRes S'(i \<mapsto> res),            knownIds := knownIds S' \<union> uniqueIds res\<rparr>"
          by (auto simp add: step_s.simps)

        from ec_p \<open>S ~~ (i, tr) \<leadsto>\<^sub>S* S'\<close> \<open>localState S i \<triangleq> (store, ls1 \<bind> impl_language_loops.return)\<close> 
        have "P S' res" 
        proof (rule use_execution_s_correct_p_P)
          from `toImpl (store'', ls'') = Return res`
          show "ls'' = impl_language_loops.io.WaitReturn res"
            by (cases ls'', auto split: prod.splits)

          from `localState S' i \<triangleq> (store'', ls'')`
          show " localState S' i \<triangleq> (store'', ls'' \<bind> impl_language_loops.return)"
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
        have "traceCorrect_s (tr @ [a]) \<and> (\<forall>res. snd S''_ls = impl_language_loops.io.WaitReturn res \<longrightarrow> P S'' res)"
          using \<open>S ~~ (i, tr @ [a]) \<leadsto>\<^sub>S* S''\<close> \<open>localState S i \<triangleq> (store, ls1 \<bind> impl_language_loops.return)\<close>
        proof (rule use_execution_s_correct_p)
          show "localState S'' i \<triangleq> (fst S''_ls, snd S''_ls \<bind> impl_language_loops.return)"
            by (simp add: Some)
        qed
          
        thus False
          by (metis \<open>a = (x, False)\<close> append_is_Nil_conv last_in_set last_snoc list.simps(3) traceCorrect_s_def)

        
      qed
    qed
  qed
qed




text "It is sufficient to check with @{term execution_s_check} to ensure that the procedure is correct:"


lemma execution_s_check_sound:
  assumes ls_def: "localState S i \<triangleq> (Map.empty, ls)"
    and vis_def: "visibleCalls S i \<triangleq> vis"
    and progr_def: "prog S = progr"
    and toImpl: "currentProc S i \<triangleq> toImpl"
    and generatedLocal: "generatedLocal = {x. generatedIds S x \<triangleq> i}"
    and generatedLocalPrivate1: "generatedLocalPrivate \<subseteq> generatedLocal"
    and generatedLocalPrivate2: "\<forall>v\<in>generatedLocalPrivate. uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S) (currentProc S) v"
    and S_wf: "state_wellFormed S"
    and no_uncommitted: "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    and no_currentTxn: "currentTransaction S i = None"
    and firstTx_def: "(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed ))"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and c: "execution_s_check \<lparr>
      calls = (calls S),
      happensBefore = (happensBefore S),
      callOrigin = (callOrigin S),
      transactionOrigin = (transactionOrigin S),
      knownIds = (knownIds S),
      invocationOp = (invocationOp S),
      invocationRes = (invocationRes S),
      ps_progr = progr,
      ps_i = i,
      ps_generatedLocal = generatedLocal,
      ps_generatedLocalPrivate = generatedLocalPrivate,
      ps_vis = vis,
      ps_localCalls = [],
      ps_tx = (currentTransaction S i),
      ps_firstTx = firstTx,
      ps_store = Map.empty,
      ps_ls = ls\<rparr>
      return P ls"
    \<comment> \<open>The execution check ensures that executing statement s only produces valid traces ending in a state 
   satisfying P.\<close>
  shows "execution_s_correct S i"
proof (auto simp add:  execution_s_correct_def)
  fix trace S'
  assume a0: "S ~~ (i, trace) \<leadsto>\<^sub>S* S'"

  thm c[simplified execution_s_check_def proof_state.simps, rule_format, OF a0]

  from a0
  have "execution_s_check_final trace S' i impl_language_loops.return P"
  proof (rule c[simplified execution_s_check_def proof_state.simps, rule_format]; 
      ((subst_all r: operationContext.simps invariantContext.simps proof_state.simps)+)? ; force?)


    show "\<And>p t. (AInvoc p, t) \<notin> set trace"
      using a0 assms no_more_invoc by blast

    show "proof_state_rel
     \<lparr>calls = calls S, happensBefore = happensBefore S, callOrigin = callOrigin S,
        transactionOrigin = transactionOrigin S, knownIds = knownIds S, invocationOp = invocationOp S,
        invocationRes = invocationRes S, ps_progr = progr, ps_i = i, ps_generatedLocal = generatedLocal,
        ps_generatedLocalPrivate = generatedLocalPrivate, ps_vis = vis, ps_localCalls = [],
        ps_tx = currentTransaction S i, ps_firstTx = firstTx, ps_store = Map.empty, ps_ls = ls\<rparr>
     S"
      unfolding proof_state_rel_def state.simps operationContext.simps proof_state.simps invariantContext.simps
    proof (intro conjI allI impI ballI; (simp; fail)?)


      show "state_wellFormed S"
        by (simp add: assms)



      find_theorems ps_localCalls

      show "prog S = progr"
        by (simp add: assms)

      show " generatedLocal = {x. generatedIds S x \<triangleq> i}"
        by (auto simp add: assms)

      show "localState S i \<triangleq> (Map.empty, ls)"
        by (simp add: assms(1))

      show "currentProc S i \<triangleq> toImpl"
        by (simp add: assms)

      show "currentTransaction S i \<noteq> Some tx' \<Longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted" for tx'
        by (simp add: assms)


      show " visibleCalls S i \<triangleq> (vis \<union> set [])"
        by (simp add: assms)

      show "case currentTransaction S i of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S c \<triangleq> tx'}"
        by (simp add: no_currentTxn)

      show "sorted_by (happensBefore S) []"
        by (simp add: sorted_by_empty)
      show "firstTx = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed)"
        using firstTx_def by auto

      show "\<And>c. i_callOriginI S c \<triangleq> i \<Longrightarrow> c \<in> vis"
        apply (auto simp add: i_callOriginI_h_def split: option.splits)
        using S_wf state_wellFormed_ls_visibleCalls_callOrigin vis_def by blast

      show "generatedLocalPrivate \<subseteq> generatedLocal"
        by (simp add: generatedLocalPrivate1)



      show "\<And>x. x \<in> generatedLocalPrivate \<Longrightarrow>
         uid_is_private i (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S) (localState S)
          (currentProc S) x"
        by (simp add: generatedLocalPrivate2)

    qed
  qed
  thus "traceCorrect_s trace"
    using execution_s_check_final_def by blast

qed


lemma execution_s_check_sound2:
  assumes a1: "localState S i \<triangleq> (Map.empty, ls)"
    and a2': "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and P: "\<And>S' res.
           P S' res \<Longrightarrow>
           invariant (prog S)
            (invariantContext.truncate
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
\<lbrakk>
s_invocationOp i = invocationOp S i;
s_invocationRes i = None;
\<And>tx. s_transactionOrigin tx \<noteq> Some i
\<rbrakk> \<Longrightarrow>
  execution_s_check \<lparr>
      calls = s_calls,
      happensBefore = s_happensBefore,
      callOrigin = s_callOrigin,
      transactionOrigin = s_transactionOrigin,
      knownIds = s_knownIds,
      invocationOp = s_invocationOp,
      invocationRes = s_invocationRes,
      ps_progr = progr,
      ps_i = i,
      ps_generatedLocal = {},
      ps_generatedLocalPrivate = {},
      ps_vis = {},
      ps_localCalls = [],
      ps_tx = None,
      ps_firstTx = True,
      ps_store = Map.empty,
      ps_ls = ls\<rparr>
      return P ls" 
  shows "execution_s_correct S i"
  using a1
proof (rule execution_s_check_sound)

  have a2: "S \<in> initialStates progr i"
    using a2' by (simp add: initialStates'_same) 

  show "visibleCalls S i \<triangleq> {}"
    using a2 by (auto simp add: initialStates_def)

  show "prog S = progr"
    using a2 by (auto simp add: initialStates_def)

  show "currentProc S i \<triangleq> toImpl"
    using a3 by simp

  show wf: "state_wellFormed S"

    using a2 initialStates_wellFormed by blast

  show "{} = {x. generatedIds S x \<triangleq> i}"
    using a2 wf_generated_ids_invocation_exists by (auto simp add: initialStates_def, blast)

  show currentTx: "currentTransaction S i = None"
    using a2 initialState_noTxns2 by blast


  show "execution_s_check
     \<lparr>calls = calls S, happensBefore = happensBefore S,
        callOrigin = callOrigin S, transactionOrigin = transactionOrigin S,
        knownIds = knownIds S, invocationOp = invocationOp S,
        invocationRes = invocationRes S, ps_progr = progr, ps_i = i,
        ps_generatedLocal = {},
        ps_generatedLocalPrivate = {}, ps_vis = {},
        ps_localCalls = [], ps_tx = currentTransaction S i,
        ps_firstTx = True, ps_store = Map.empty, ps_ls = ls\<rparr> return P ls"
    unfolding currentTx
  proof (rule c)
    show "invocationOp S i = invocationOp S i" by simp
    show "invocationRes S i = None"
      by (simp add: a1 local.wf state_wellFormed_no_result_when_running)
    show "\<And>tx. transactionOrigin S tx \<noteq> Some i"
      using a2 by (auto simp add: initialStates_def)

  qed

  show "\<And>tx'. currentTransaction S i \<noteq> Some tx' \<longrightarrow> transactionStatus S tx' \<noteq> Some Uncommitted"
    using a2 initialState_noTxns1 by blast

  show "True = (\<nexists>c tx. callOrigin S c \<triangleq> tx \<and> transactionOrigin S tx \<triangleq> i \<and> transactionStatus S tx \<triangleq> Committed)"
    by (meson \<open>visibleCalls S i \<triangleq> {}\<close> empty_iff local.wf state_wellFormed_ls_visibleCalls_callOrigin)


  show "\<And>S' res.
       P S' res \<Longrightarrow>
       invariant (prog S)
        (invariantContext.truncate
          (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    using P .
qed simp+


lemma execution_s_check_sound3:
  assumes a1: "localState S i \<triangleq> (Map.empty, ls)"
    and a2: "S \<in> initialStates' progr i"
    and a3: "currentProc S i \<triangleq> toImpl"
    and a4: "invocationOp S i \<triangleq> op"
    and P: "\<And>S' res. P S' res \<Longrightarrow> 
        invariant (prog S) (invariantContext.truncate 
              (S'\<lparr>invocationRes := invocationRes S'(i \<mapsto> res), 
                  knownIds := knownIds S' \<union> uniqueIds res\<rparr>))"
    and c: "\<And>s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes.
\<lbrakk>
\<And>tx. s_transactionOrigin tx \<noteq> Some i
\<rbrakk> \<Longrightarrow>
  execution_s_check \<lparr>
      calls = s_calls,
      happensBefore = s_happensBefore,
      callOrigin = s_callOrigin,
      transactionOrigin = s_transactionOrigin,
      knownIds = s_knownIds,
      invocationOp = s_invocationOp(i\<mapsto>op),
      invocationRes = s_invocationRes(i:=None),
      ps_progr = progr,
      ps_i = i,
      ps_generatedLocal = {},
      ps_generatedLocalPrivate = {},
      ps_vis = {},
      ps_localCalls = [],
      ps_tx = None,
      ps_firstTx = True,
      ps_store = Map.empty,
      ps_ls = ls\<rparr>
      return P ls" 
  shows "execution_s_correct S i"
  using a1 a2 a3 
proof (rule execution_s_check_sound2[where P=P], goal_cases Final A)
  case (Final S' res)
  then show ?case
    using P by blast
next
  case (A s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp s_invocationRes)
  show "execution_s_check
            \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
               transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp,
               invocationRes = s_invocationRes, ps_progr = progr, ps_i = i, ps_generatedLocal = {},
               ps_generatedLocalPrivate = {}, ps_vis = {}, ps_localCalls = [], ps_tx = None, ps_firstTx = True,
               ps_store = Map.empty, ps_ls = ls\<rparr>
            impl_language_loops.return P ls"

  proof (fuzzy_rule c)
    show "\<And>tx. s_transactionOrigin tx \<noteq> Some i"
      by (simp add: A(3))
    show "s_invocationRes(i := None) = s_invocationRes"
      using A(2) by auto
    show "s_invocationOp(i \<mapsto> op) = s_invocationOp"
      using A(1) a4 by auto
  qed
qed

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



lemma execution_s_check_step:
assumes step: "\<And>S1 action S2 Inv.
\<lbrakk>
currentProc S1 (ps_i S) \<triangleq> toImpl;
S1 ~~ (ps_i S, action, Inv) \<leadsto>\<^sub>S S2;
proof_state_rel S S1
   \<rbrakk> \<Longrightarrow> Inv \<and> 
    (\<exists>S_new res. 
        proof_state_rel S_new S2 
      \<and> ps_i S_new = ps_i S 
      \<and> ps_ls S_new = cont res \<bind> conti
      \<and> execution_s_check S_new conti Pred (cont res))"
and toImpl: "toImpl (ps_store S, cmd) = lAction"
and noReturn: "\<And>res. lAction \<noteq> Return res"
  shows "execution_s_check S conti Pred (cmd \<bind> cont)"
  apply (subst  execution_s_check_def)
  apply (intro allI impI conjI)
proof (goal_cases A)
  case (A trace S1 S')


  from `proof_state_rel S S1`
  have  psc0: "state_wellFormed S1"
    and psc1: "calls S1 = calls S"
    and psc2: "happensBefore S1 = updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)"
    and psc3: "callOrigin S1 = map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S))"
    and psc4: "transactionOrigin S1 = transactionOrigin S"
    and psc5: "knownIds S1 = knownIds S"
    and psc6: "invocationOp S1 = invocationOp S"
    and psc7: "invocationRes S1 = invocationRes S"
    and psc8: "prog S1 = ps_progr S"
    and psc9: "ps_generatedLocal S = {x. generatedIds S1 x \<triangleq> ps_i S}"
    and psc10: "localState S1 (ps_i S) \<triangleq> (ps_store S, ps_ls S)"
    and psc11: "currentProc S1 (ps_i S) \<triangleq> toImpl"
    and psc12: "visibleCalls S1 (ps_i S) \<triangleq> (ps_vis S \<union> set (ps_localCalls S))"
    and psc13: "currentTransaction S1 (ps_i S) = ps_tx S"
    and psc14: "\<forall>tx'. ps_tx S \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted"
    and psc15: "case ps_tx S of None \<Rightarrow> ps_localCalls S = [] | Some tx' \<Rightarrow> set (ps_localCalls S) = {c. callOrigin S1 c \<triangleq> tx'}"
    and psc16: "sorted_by (updateHb (happensBefore S) (ps_vis S) (ps_localCalls S)) (ps_localCalls S)"
    and psc17: "ps_vis S \<inter> set (ps_localCalls S) = {}"
    and psc18: "dom (callOrigin S) \<inter> set (ps_localCalls S) = {}"
    and psc19: "Field (happensBefore S) \<inter> set (ps_localCalls S) = {}"
    and psc20: "distinct (ps_localCalls S)"
    and psc21: "ps_firstTx S = (\<forall>c tx. transactionOrigin S tx \<triangleq> ps_i S \<longrightarrow> map_update_all (callOrigin S) (ps_localCalls S) (the (ps_tx S)) c \<triangleq> tx \<longrightarrow> transactionStatus S1 tx \<noteq> Some Committed)"
    and psc22: "\<forall>c. i_callOriginI S c \<triangleq> ps_i S \<longrightarrow> c \<in> ps_vis S"
    and psc23: "ps_generatedLocalPrivate S \<subseteq> {x. generatedIds S1 x \<triangleq> ps_i S}"
    and psc24: "\<forall>v\<in>ps_generatedLocalPrivate S. uid_is_private (ps_i S) (calls S) (invocationOp S) (invocationRes S) (knownIds S) (generatedIds S1) (localState S1) (currentProc S1) v"
    and psc25: "finite (dom (ps_store S))"
    by (auto simp add: proof_state_rel_def)

  show "execution_s_check_final trace S' (ps_i S) conti Pred"
  proof (cases trace)
    case Nil

    from ` S1 ~~ (ps_i S, trace) \<leadsto>\<^sub>S* S'`
    have "S' = S1"
      by (simp add: local.Nil steps_s_empty)


    show ?thesis
      unfolding execution_s_check_final_def  `S' = S1`
    proof (intro conjI allI impI)
      show "traceCorrect_s trace"
        using Nil by (simp add: traceCorrect_s_empty) 

      

      show "Pred PS res"
        if c0: "proof_state_rel PS S1"
          and c1: "ps_i PS = ps_i S"
          and c2: "ps_ls PS = impl_language_loops.io.WaitReturn res \<bind> conti"
        for  PS res
      proof -
        have "localState S1 (ps_i S) \<triangleq> (ps_store PS, ps_ls PS)"
          using c0 c1 proof_state_rel_fact(11) by fastforce

        from `ps_ls S = (cmd \<bind> cont) \<bind> conti`
        have "ps_ls PS = (cmd \<bind> cont) \<bind> conti"
          using \<open>localState S1 (ps_i S) \<triangleq> (ps_store PS, ps_ls PS)\<close> psc10 by auto

        with c2
        have "(cmd \<bind> cont) \<bind> conti = WaitReturn res \<bind> conti"
          by simp
        hence "(cmd \<bind> cont) \<bind> conti = conti res"
          by simp
        hence "(cmd \<bind> cont) = WaitReturn res"
          apply (cases "cmd \<bind> cont", auto)
          apply auto

        hence cmd_eq: "cmd \<bind> (\<lambda>r. cont r \<bind> conti) = conti res"
          by simp


        have "\<exists>r. toImpl (ps_store S, cmd) = Return r"
        proof (cases cmd)
          case (WaitReturn r)
          then show ?thesis
            by auto
        next
          case (WaitLocalStep x1)
          then show ?thesis 
            using cmd_eq apply auto
            sorry
        next
          case (WaitBeginAtomic x2)
          then show ?thesis sorry
        next
          case (WaitEndAtomic x3)
          then show ?thesis sorry
        next
          case (WaitNewId x41 x42)
          then show ?thesis sorry
        next
          case (WaitDbOperation x51 x52)
          then show ?thesis sorry
        next

          case (Loop x71 x72)
          then show ?thesis sorry
        qed
        hence False
          by (simp add: noReturn toImpl)


          apply (cases cmd, auto)
          apply auto



        find_theorems cmd

        have "ps_ls PS = snd (localState S1 (ps_i S))"
        using `localState S1 (ps_i S) \<triangleq> (ps_store S, ps_ls S)`


        thm toImpl noReturn


    unfolding execution_s_check_final_def 
  proof (intro conjI allI impI)
    from `S1 ~~ (ps_i S, trace) \<leadsto>\<^sub>S* S'`
    show "traceCorrect_s trace"
    proof (rule case_trace_not_empty3)

      


      show "Inv \<and> traceCorrect_s trace'"
        if c0: "trace = (action, Inv) # trace'"
          and c1: "S1 ~~ (ps_i S, action, Inv) \<leadsto>\<^sub>S S'a"
          and c2: "S'a ~~ (ps_i S, trace') \<leadsto>\<^sub>S* S'"
        for  action S'a Inv trace'
      proof

        obtain lAction where "lAction = toImpl (ps_store S, ps_ls S)"
          by simp


        have s: "Inv \<and> (\<exists>S_new res. 
              proof_state_rel S_new S'a 
            \<and> ps_i S_new = ps_i S 
            \<and> ps_ls S_new = cont res \<bind> conti
            \<and> execution_s_check S_new conti Pred (cont res))"
        proof (rule step)
          show "currentProc S1 (ps_i S) \<triangleq> toImpl"
            by (simp add: psc11)
          show "S1 ~~ (ps_i S, action, Inv) \<leadsto>\<^sub>S S'a"
            using `S1 ~~ (ps_i S, action, Inv) \<leadsto>\<^sub>S S'a` .
          show "proof_state_rel S S1" 
            using `proof_state_rel S S1` .
        qed

        from this obtain S_new res 
          where "Inv" 
            and S_new_rel: "proof_state_rel S_new S'a"
            and S_new_exec: "execution_s_check S_new conti Pred (cont res)"
            and ps_i_eq: "ps_i S_new = ps_i S"
            and "ps_ls S_new = cont res \<bind> conti"
          by blast

        from s show "Inv" by simp

        thm use_execution_s_check


        
        have "execution_s_check_final trace' S' (ps_i S_new) conti Pred"
        proof (rule use_execution_s_check[where S=S_new])
          from `S'a ~~ (ps_i S, trace') \<leadsto>\<^sub>S* S'`
          show "S'a ~~ (ps_i S_new, trace') \<leadsto>\<^sub>S* S'"
            using ps_i_eq by simp

          
          show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
            using A(2) c0 by auto
          show "proof_state_rel S_new S'a"
            by (simp add: S_new_rel)
          show "ps_ls S_new = cont res \<bind> conti"
            using \<open>ps_ls S_new = cont res \<bind> conti\<close> by blast
          show "\<And>store' ls'. localState S' (ps_i S_new) \<triangleq> (store', ls') \<Longrightarrow> \<exists>x. ls' = x \<bind> conti"
            using `\<forall>store' ls'. localState S' (ps_i S) \<triangleq> (store', ls') \<longrightarrow> (\<exists>x. ls' = x \<bind> conti)`
            by (simp add: A(5) ps_i_eq)
          show "execution_s_check S_new conti Pred (cont res)"
            by (simp add: S_new_exec)
        qed


        then show "traceCorrect_s trace'"
          using execution_s_check_final_def by blast
      qed
    qed

    show "Pred PS res"
      if c0: "proof_state_rel PS S'"
        and c1: "ps_i PS = ps_i S"
        and c2: "ps_ls PS = impl_language_loops.io.WaitReturn res \<bind> conti"
      for  PS res
    proof -


      thm toImpl noReturn
      have "localState S' (ps_i PS) \<triangleq> (ps_store PS, ps_ls PS)"
        by (simp add: c0 proof_state_rel_fact(11))




  thm case_trace_not_empty3

  then show ?case sorry
qed


lemma execution_s_check_newId:
  assumes "infinite (Collect P)"
    and "program_wellFormed progr"
    and cont: "\<And>v. \<lbrakk>P v; 
to_nat v \<notin> s_knownIds;
to_nat v \<notin> generatedLocal;
uniqueIds v = {to_nat v};
uid_is_private' (ps_i S) (calls S) (invocationOp S) (invocationRes S) (knownIds S) (to_nat v)
\<rbrakk> \<Longrightarrow> execution_s_check (S\<lparr> 
    ps_generatedLocal := ps_generatedLocal S \<union> {to_nat v},
    ps_generatedLocalPrivate := ps_generatedLocalPrivate S \<union> {to_nat v}
    \<rparr>) conti Pred (cont v)"
(*
  progr 
  i
  s_calls 
  s_happensBefore 
  s_callOrigin 
  s_transactionOrigin 
  s_knownIds 
  s_invocationOp
  s_invocationRes
  (generatedLocal \<union> {to_nat v})
  (generatedLocalPrivate \<union> {to_nat v})
  vis
  localCalls
  tx
  firstTx
  store
  (cont v)"
*)
shows "execution_s_check S conti Pred (newId P \<bind> cont)
"
  apply (subst  execution_s_check_def)
  apply (intro allI impI conjI)
  thm case_trace_not_empty3 
\<comment> \<open>TODO make this into a rule \<close>
  apply ( erule case_trace_not_empty3)
  apply ( erule(1) no_ainvoc)
  apply ( goal_cases Step)

proof show_proof_rule
  case (Step trace S1 S' action S'a Inv trace')

  have "localState S1 (ps_i S) \<triangleq> (ps_store S, (newId P \<bind> cont) \<bind> conti)"
    by (simp add: Step(1) Step(2) proof_state_rel_fact(11))

  have "currentProc S1 (ps_i S) \<triangleq> toImpl"
    by (simp add: Step(1) proof_state_rel_fact(12))



  from ` S1 ~~ (ps_i S, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 (ps_i S) \<triangleq> (ps_store S, (newId P \<bind> cont) \<bind> conti)`
    `currentProc S1 (ps_i S) \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  obtain uidv
    where  c0: "localState S1 (ps_i S) \<triangleq> (ps_store S, impl_language_loops.newId P \<bind> (\<lambda>a. cont a \<bind> conti))"
      and c1: "currentProc S1 (ps_i S) \<triangleq> toImpl"
      and c2: "action = ANewId uidv"
      and c3: "Inv"
      and S'a_def: "S'a = S1 \<lparr>localState := localState S1(ps_i S \<mapsto> (ps_store S, cont uidv \<bind> conti)), generatedIds := generatedIds S1(to_nat uidv \<mapsto> ps_i S)\<rparr>"
      and c5: "generatedIds S1 (to_nat uidv) = None"
      and c6: "uniqueIds uidv = {to_nat uidv}"
      and c7: "P uidv"
    by (cases action, auto simp add: step_s.simps split: if_splits)


  show "Inv \<and> traceCorrect_s trace'"
  proof (intro conjI)
    show "Inv" using `Inv` .

    from `S'a ~~ (ps_i S, trace') \<leadsto>\<^sub>S* S'`
    show "traceCorrect_s trace'"
    proof (rule use_execution_s_check)


      have h1: "new_unique_not_in_calls s_calls (to_nat uidv)"
        using Step(1) Step(2) Step(9) assms(2) c5 new_unique_not_in_calls_def wf_onlyGeneratedIdsInCalls by blast


      have h2: "new_unique_not_in_calls_result s_calls (to_nat uidv)"
        using Step(1) Step(2) Step(9) assms(2) c5 new_unique_not_in_calls_result_def wf_onlyGeneratedIdsInCallResults by blast

      have h3: "new_unique_not_in_invocationOp s_invocationOp (to_nat uidv)"
        using Step(1) Step(7) Step(9) assms(2) c5 new_unique_not_in_invocationOp_def wf_onlyGeneratedIdsInInvocationOps by blast

      have h4: "new_unique_not_in_invocationRes s_invocationRes (to_nat uidv)"
        using Step(1) Step(8) Step(9) assms(2) c5 new_unique_not_in_invocationRes_def wf_onlyGeneratedIdsInInvocationRes by blast

      have h5: "new_unique_not_in_other_invocations i (localState S1(i \<mapsto> (store, cont uidv))) (currentProc S1) (to_nat uidv)"
        apply (auto simp add: new_unique_not_in_other_invocations_def)
        by (metis (mono_tags, lifting) Step(1) Step(9) assms(2) c5 domIff in_mono wf_knownIds_subset_generatedIds_h(1))

      have h6: "to_nat uidv \<notin> s_knownIds"
        using Step(1) Step(6) Step(9) assms(2) c5 wf_onlyGeneratedIdsInKnownIds by blast


      show "execution_s_check
            progr 
            i
            s_calls 
            s_happensBefore 
            s_callOrigin 
            s_transactionOrigin 
            s_knownIds 
            s_invocationOp
            s_invocationRes
            (generatedLocal \<union> {to_nat uidv})
            (generatedLocalPrivate \<union> {to_nat uidv})
            vis
            localCalls
            tx
            firstTx
            store
            (cont uidv)"
      proof (rule cont)
        show "P uidv"
          by (simp add: c7)

        
        show "to_nat uidv \<notin> s_knownIds"
          using h6 by auto

        show "to_nat uidv \<notin> generatedLocal"
          by (simp add: Step(10) c5)

        show "uniqueIds uidv = {to_nat uidv}"
          by (simp add: c6)

        show "uid_is_private' i s_calls s_invocationOp s_invocationRes s_knownIds (to_nat uidv)"
          by (simp add: h1 h2 h3 h4 h6 uid_is_private'_def)


      qed


      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        using Step(16) by (auto simp add: S'a_def  split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step by (auto simp add:S'a_def )

      show "generatedLocal \<union> {to_nat uidv} = {x. generatedIds S'a x \<triangleq> i}"
        by (auto simp add: S'a_def Step)

      show "generatedLocalPrivate \<union> {to_nat uidv} \<subseteq> generatedLocal \<union> {to_nat uidv}"
        apply (auto simp add: S'a_def Step)
        by (meson Step(25) uid_is_private_def)

      

      show "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a)
          (localState S'a) (currentProc S'a) v" if "v \<in> generatedLocalPrivate \<union> {to_nat uidv}" for v
        using that proof auto

        show  "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a) (localState S'a)
       (currentProc S'a) (to_nat uidv)"
          by (auto simp add: uid_is_private_def S'a_def Step h1 h2 h3 h4 h5 h6)

        show "v \<in> generatedLocalPrivate \<Longrightarrow>
    uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a) (localState S'a)
     (currentProc S'a) v"
          apply (auto simp add: Step S'a_def)
          by (smt Step(2) Step(25) Step(6) Step(7) Step(8) map_upd_Some_unfold new_unique_not_in_other_invocations_def uid_is_private_def)

      qed
        

    qed (simp add: S'a_def Step; fail)+
  qed
qed





lemma execution_s_check_beginAtomic:
  assumes "program_wellFormed progr"
    and cont: "\<And>tx s_calls' s_happensBefore' s_callOrigin' s_transactionOrigin' s_knownIds' vis'
 s_invocationOp' s_invocationRes' .
\<lbrakk>invariant progr
     \<lparr>calls = s_calls', 
      happensBefore = s_happensBefore',
      callOrigin = s_callOrigin',
      transactionOrigin = s_transactionOrigin', 
      knownIds = s_knownIds',
      invocationOp = (s_invocationOp'(i := s_invocationOp i)), 
      invocationRes = s_invocationRes'(i := None)\<rparr>;
s_transactionOrigin' tx = None;
\<And>i op. s_invocationOp i \<triangleq> op \<Longrightarrow> s_invocationOp' i \<triangleq> op;
\<And>c. s_callOrigin' c \<noteq> Some tx;
vis \<subseteq> vis';
vis' \<subseteq> dom s_calls';
firstTx \<Longrightarrow> (\<And>c tx. s_callOrigin' c \<triangleq> tx \<Longrightarrow> s_transactionOrigin' tx \<noteq> Some i);
\<comment> \<open>consistency: \<close>
causallyConsistent s_happensBefore' vis';
transactionConsistent_atomic s_callOrigin' vis';
\<forall>v\<in>generatedLocalPrivate. uid_is_private' i s_calls' s_invocationOp' s_invocationRes' s_knownIds' v;
\<comment> \<open>generic wellFormed and growth predicates (this is more like a backup, the important facts should be above) : \<close>
\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus.
state_wellFormed \<lparr>
  calls = s_calls',
  happensBefore = s_happensBefore',
  callOrigin = s_callOrigin',
  transactionOrigin = s_transactionOrigin',
  knownIds = s_knownIds',
  invocationOp = s_invocationOp',
  invocationRes = s_invocationRes',
  prog = progr,
  transactionStatus = some_transactionStatus,
  generatedIds =  some_generatedIds,
  localState = some_localState,
  currentProc = some_currentProc,
  visibleCalls =  some_visibleCalls,
  currentTransaction = some_currentTransaction\<rparr>;
 \<exists>some_generatedIds1 some_currentTransaction1 some_localState1 some_currentProc1 some_visibleCalls1 some_transactionStatus1
  some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2 some_visibleCalls2 some_transactionStatus2.
state_monotonicGrowth i \<lparr>
  calls = s_calls,
  happensBefore = s_happensBefore,
  callOrigin = s_callOrigin,
  transactionOrigin = s_transactionOrigin,
  knownIds = s_knownIds,
  invocationOp = s_invocationOp,
  invocationRes = s_invocationRes,
  prog = progr,
  transactionStatus = some_transactionStatus1,
  generatedIds =  some_generatedIds1,
  localState = some_localState1,
  currentProc = some_currentProc1,
  visibleCalls =  some_visibleCalls1,
  currentTransaction = some_currentTransaction1\<rparr> 
\<lparr>
  calls = s_calls',
  happensBefore = s_happensBefore',
  callOrigin = s_callOrigin',
  transactionOrigin = s_transactionOrigin',
  knownIds = s_knownIds',
  invocationOp = s_invocationOp',
  invocationRes = s_invocationRes',
  prog = progr,
  transactionStatus = some_transactionStatus2,
  generatedIds =  some_generatedIds2,
  localState = some_localState2,
  currentProc = some_currentProc2,
  visibleCalls =  some_visibleCalls2,
  currentTransaction = some_currentTransaction2\<rparr>
\<rbrakk> \<Longrightarrow> execution_s_check
  progr 
  i
  s_calls' 
  s_happensBefore' 
  s_callOrigin' 
  (s_transactionOrigin'(tx \<mapsto> i))
  s_knownIds' 
  (s_invocationOp'(i := s_invocationOp i))
  (s_invocationRes'(i := None))
  generatedLocal
  generatedLocalPrivate
  vis'
  []
  (Some tx)
  firstTx
  store
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  []
  None
  firstTx
  store
  (beginAtomic \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (store, beginAtomic \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  obtain t txns S' vis' vis''
    where c0: "localState S1 i \<triangleq> (store, beginAtomic \<bind> cont)"
      and c1: "currentProc S1 i \<triangleq> toImpl"
      and c2: "action = ABeginAtomic t txns"
      and c3: "Inv"
      and c4: "currentTransaction S1 i = None"
      and c5: "transactionStatus S1 t = None"
      and c6: "prog S' = prog S1"
      and growth: "state_monotonicGrowth i S1 S'"
      and c8: "\<forall>x. transactionOrigin S1 x \<triangleq> i = transactionOrigin S' x \<triangleq> i"
      and inv: "invariant (prog S1) (invContext S')"
      and c10: "\<forall>x. transactionStatus S' x \<noteq> Some Uncommitted"
      and wf_S': "state_wellFormed S'"
      and c12: "state_wellFormed (S'\<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> (store, cont ())), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>)"
      and c13: "localState S' i \<triangleq> (store, beginAtomic \<bind> cont)"
      and c14: "currentProc S' i \<triangleq> toImpl"
      and c15: "currentTransaction S' i = None"
      and c16: "visibleCalls S1 i \<triangleq> vis'"
      and c17: "visibleCalls S' i \<triangleq> vis'"
      and c18: "chooseSnapshot vis'' vis' S'"
      and c19: "consistentSnapshot S' vis''"
      and c20: "transactionStatus S' t = None"
      and c21: "\<forall>x. callOrigin S' x \<noteq> Some t"
      and c22: "transactionOrigin S' t = None"
      and S'a_def: "S'a = S' \<lparr>transactionStatus := transactionStatus S'(t \<mapsto> Uncommitted), transactionOrigin := transactionOrigin S'(t \<mapsto> i), currentTransaction := currentTransaction S'(i \<mapsto> t), localState := localState S'(i \<mapsto> (store, cont ())), visibleCalls := visibleCalls S'(i \<mapsto> vis'')\<rparr>"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof (intro conjI)
    show "Inv" using `Inv` .

    from `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    show "traceCorrect_s trace'"
    proof (rule use_execution_s_check)

      show "happensBefore S'a = updateHb (happensBefore S'a) vis'' []"
        by simp

      show "callOrigin S'a = map_update_all (callOrigin S'a) [] (the (Some t))"
        by simp

      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto


      show " state_wellFormed S'a"
        using S'a_def c12 by blast

      show "currentProc S'a i \<triangleq> toImpl"
        by (simp add: S'a_def c14)

      show "localState S'a i \<triangleq> (store, cont ())"
        by (simp add: S'a_def)

      show "visibleCalls S'a i \<triangleq> (vis'' \<union> set [])"
        by (simp add: S'a_def)

      show "currentTransaction S'a i \<triangleq> t"
        by (simp add: S'a_def)

      show " \<And>tx'. Some t \<noteq> Some tx' \<Longrightarrow> transactionStatus S'a tx' \<noteq> Some Uncommitted"
        by (simp add: S'a_def c10)
      show "case Some t of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S'a c \<triangleq> tx'}"
        by (simp add: S'a_def c21)
      show "sorted_by (happensBefore S'a) []"
        by (simp add: S'a_def sorted_by_empty)
      show "vis'' \<inter> set [] = {}"
        by simp
      show "dom (callOrigin S'a) \<inter> set [] = {}"
        by simp
      show "Field (happensBefore S'a) \<inter> set [] = {}"
        by simp

      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a) (transactionOrigin S'a) (knownIds S'a)
     (invocationOp S'a) (invocationRes S'a) generatedLocal generatedLocalPrivate  vis'' [] (Some t) firstTx store (cont ())"
      proof (fuzzy_rule cont)

        show "progr = prog S'a"
          by (simp add: S'a_def `prog S1 = progr` c6)

        show "transactionOrigin S'(t \<mapsto> i) = transactionOrigin S'a"
          by (simp add: S'a_def)

        show "transactionOrigin S' t = None"
          by (simp add: c22)


        show " invariant progr
     \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
        transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = (invocationOp S'a)(i := s_invocationOp i),
        invocationRes = (invocationRes S'a)(i := None)\<rparr>"
        proof (fuzzy_rule inv)
          show "prog S1 = progr"
            by (simp add: Step)

          have cCalls: "committedCalls S' = dom (calls S')"
            by (simp add: c10 wf_S' committedCalls_allCommitted)

          have allTransactionsCommitted: "committedTransactions S' = dom (transactionOrigin S')"
            apply (auto simp add: dom_def)
             apply (metis wf_S' domD domIff option.simps(3) wf_transaction_status_iff_origin)
            by (metis c10 not_None_eq not_uncommitted_cases wf_S' wf_transaction_status_iff_origin)



          show "invContext S' =
           \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
            transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = (invocationOp S'a)(i := s_invocationOp i),
           invocationRes = (invocationRes S'a)(i := None)\<rparr>"
          proof (auto simp add: invContextH_def S'a_def cCalls allTransactionsCommitted)
            show "\<And>a b. (a, b) \<in> happensBefore S' |r dom (calls S') \<Longrightarrow> (a, b) \<in> happensBefore S'"
              by (simp add: restrict_relation_def)
            show "\<And>a b. (a, b) \<in> happensBefore S' \<Longrightarrow> (a, b) \<in> happensBefore S' |r dom (calls S')"
              by (simp add: wf_S' happensBefore_in_calls_left happensBefore_in_calls_right restrict_relation_def)
            show " callOrigin S' |` dom (calls S') = callOrigin S'"
              by (metis wf_S' restrict_map_noop2 wellFormed_callOrigin_dom)
            show "invocationOp S' = (invocationOp S')(i := s_invocationOp i)"
              using Step(7) growth state_monotonicGrowth_invocationOp_i by fastforce
            show "invocationRes S' = (invocationRes S')(i := None)"
              by (simp add: c13 fun_upd_idem wf_S' wf_localState_noReturn)
          qed
        qed

        show "\<And>i op. s_invocationOp i \<triangleq> op \<Longrightarrow> invocationOp S'a i \<triangleq> op"
          apply(simp add: S'a_def)
          using Step(7) growth state_monotonicGrowth_invocationOp by blast

        show "\<And>c. callOrigin S'a c \<noteq> Some t"
          using \<open>case Some t of None \<Rightarrow> [] = [] | Some tx' \<Rightarrow> set [] = {c. callOrigin S'a c \<triangleq> tx'}\<close> by auto
        
        from `chooseSnapshot vis'' vis' S'`
        have "vis' \<subseteq> vis''"
          by (auto simp add: chooseSnapshot_def)

        have "vis \<subseteq> vis'"
          using `visibleCalls S1 i \<triangleq> (vis \<union> set [])` c16 by auto

        show "vis \<subseteq> vis''"
          using \<open>vis \<subseteq> vis'\<close> \<open>vis' \<subseteq> vis''\<close> by auto

        
        show "vis'' \<subseteq> dom (calls S'a)"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def)

        show "causallyConsistent (happensBefore S'a) vis''"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def)

        show "transactionConsistent_atomic (callOrigin S'a) vis''"
          using `consistentSnapshot S' vis''`
          by (simp add: S'a_def consistentSnapshotH_def transactionConsistent_def)

        from `state_wellFormed S'`
        show "\<exists>some_generatedIds some_currentTransaction some_localState some_currentProc some_visibleCalls some_transactionStatus.
       state_wellFormed
        \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
           transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = invocationOp S'a,
           invocationRes = invocationRes S'a, prog = progr, transactionStatus = some_transactionStatus,
           generatedIds = some_generatedIds, localState = some_localState, currentProc = some_currentProc,
           visibleCalls = some_visibleCalls, currentTransaction = some_currentTransaction\<rparr>"
          apply (simp add: S'a_def `prog S1 = progr`[symmetric])
          by (metis (full_types) c6 old.unit.exhaust state.surjective)

        have smg: "state_monotonicGrowth i
         \<lparr>calls = calls S1, happensBefore = happensBefore S1, callOrigin = callOrigin S1,
            transactionOrigin = transactionOrigin S1, knownIds = knownIds S1, invocationOp = invocationOp S1,
            invocationRes = invocationRes S1, prog = prog S1, transactionStatus = transactionStatus S1,
            generatedIds = generatedIds S1, localState = localState S1, currentProc = currentProc S1,
            visibleCalls = visibleCalls S1, currentTransaction = currentTransaction S1\<rparr>
         \<lparr>calls = calls S', happensBefore = happensBefore S', callOrigin = callOrigin S',
            transactionOrigin = transactionOrigin S', knownIds = knownIds S', invocationOp = invocationOp S',
            invocationRes = invocationRes S', prog = prog S', transactionStatus = transactionStatus S',
            generatedIds = generatedIds S', localState = localState S', currentProc = currentProc S',
            visibleCalls = visibleCalls S', currentTransaction = currentTransaction S'\<rparr>"
          by (fuzzy_rule `state_monotonicGrowth i S1 S'`, auto)



        show " \<exists>some_generatedIds1 some_currentTransaction1 some_localState1 some_currentProc1 some_visibleCalls1
         some_transactionStatus1 some_generatedIds2 some_currentTransaction2 some_localState2 some_currentProc2
         some_visibleCalls2 some_transactionStatus2.
         state_monotonicGrowth i
          \<lparr>calls = s_calls, happensBefore = s_happensBefore, callOrigin = s_callOrigin,
             transactionOrigin = s_transactionOrigin, knownIds = s_knownIds, invocationOp = s_invocationOp,
             invocationRes = s_invocationRes, prog = progr, transactionStatus = some_transactionStatus1,
             generatedIds = some_generatedIds1, localState = some_localState1, currentProc = some_currentProc1,
             visibleCalls = some_visibleCalls1, currentTransaction = some_currentTransaction1\<rparr>
          \<lparr>calls = calls S'a, happensBefore = happensBefore S'a, callOrigin = callOrigin S'a,
             transactionOrigin = transactionOrigin S', knownIds = knownIds S'a, invocationOp = invocationOp S'a,
             invocationRes = invocationRes S'a, prog = progr, transactionStatus = some_transactionStatus2,
             generatedIds = some_generatedIds2, localState = some_localState2, currentProc = some_currentProc2,
             visibleCalls = some_visibleCalls2, currentTransaction = some_currentTransaction2\<rparr>"
          apply (simp add: S'a_def)
          apply (rule exI)+
          apply (fuzzy_rule smg)
          by (auto simp add: Step c6)


        

        show "\<forall>v\<in>generatedLocalPrivate.
         uid_is_private' i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) v"
        proof (auto simp add: S'a_def )
          fix v::nat
          assume "v\<in>generatedLocalPrivate"
          with `\<forall>v\<in>generatedLocalPrivate.
                uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1)
               (currentProc S1) v`
          have "uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1) (currentProc S1) v"
            by auto
          hence "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S') (localState S') (currentProc S') v"
            using Step(9) assms(1) growth growth_still_hidden by blast

          thus "uid_is_private' i (calls S') (invocationOp S') (invocationRes S') (knownIds S') v"
            by (meson uid_is_private'_implies)
        qed

        show "(invocationOp S'a)(i := s_invocationOp i) = invocationOp S'a"
          apply (auto simp add: S'a_def)
          apply (rule fun_upd_idem)
          using Step(7) growth state_monotonicGrowth_invocationOp_i by blast

        show "(invocationRes S'a)(i := None) = invocationRes S'a"
          apply (auto simp add: S'a_def)
          apply (rule fun_upd_idem)
          by (simp add: c13 state_wellFormed_no_result_when_running wf_S')


        show "transactionOrigin S' tx \<noteq> Some i"
          if c0: "firstTx"
            and c1: "callOrigin S'a c \<triangleq> tx"
          for  c tx
          using `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed)`
            c0 c1
          apply (auto simp add: S'a_def )
          by (smt Step(1) c16 c17 c4 c8 domD domIff growth state_monotonicGrowth_callOrigin state_wellFormed_ls_visibleCalls_callOrigin transactionConsistent_Committed wellFormed_visibleCallsSubsetCalls2 wf_S' wf_callOrigin_and_calls wf_transactionConsistent_noTx)




      qed
      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        apply (auto simp add: S'a_def)
        apply (smt Step(1) c15 c16 c17 c4 c8 growth in_dom state_monotonicGrowth_callOrigin state_wellFormed_ls_visibleCalls_callOrigin wellFormed_callOrigin_dom wellFormed_currentTransactionUncommitted wellFormed_state_transaction_consistent(1) wellFormed_visibleCallsSubsetCalls_h(2) wf_S')
        by (metis Step(1) c5 growth state_monotonicGrowth_callOrigin state_monotonicGrowth_transactionOrigin state_monotonicGrowth_transactionStatus2 wf_callOrigin_implies_transactionStatus_defined)

      show "\<And>c. i_callOriginI S'a c \<triangleq> i \<Longrightarrow> c \<in> vis''"
        apply (simp add: S'a_def i_callOriginI_h_def c21 split: option.splits if_splits)
        using c17 c18 chooseSnapshot_def state_wellFormed_ls_visibleCalls_callOrigin wf_S' by fastforce

      from `generatedLocal = {x. generatedIds S1 x \<triangleq> i}`
      show "generatedLocal = {x. generatedIds S'a x \<triangleq> i}"
        using growth state_monotonicGrowth_generatedIds_same1  by (simp add: S'a_def, fastforce)

      show "generatedLocalPrivate \<subseteq> generatedLocal"
        by (simp add: Step(24))

      show "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a) (localState S'a) (currentProc S'a) x"
        if c0: "x \<in> generatedLocalPrivate"
        for  x
      proof -
        from c0 have "uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1)      (currentProc S1) x"
          using Step by blast

        hence "uid_is_private i (calls S') (invocationOp S') (invocationRes S') (knownIds S') (generatedIds S')
         (localState S') (currentProc S') x"
          using Step(9) assms(1) growth growth_still_hidden by blast

        thus "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a) (localState S'a) (currentProc S'a) x"
          by (auto simp add: S'a_def uid_is_private_def new_unique_not_in_other_invocations_def)
      qed

    qed (simp add: S'a_def Step; fail)+
  qed
qed



lemma execution_s_check_endAtomic:
  assumes "program_wellFormed progr"
    and "s_transactionOrigin tx = None"
    and tx_nonempty: "localCalls \<noteq> []"
and inv_cont: "
\<lbrakk>
distinct localCalls;
\<And>c. c\<in>set localCalls \<Longrightarrow> s_callOrigin c = None;
\<And>c. c\<in>set localCalls \<Longrightarrow> c \<notin> vis;
\<And>c c'. c\<in>set localCalls \<Longrightarrow> (c,c') \<notin> s_happensBefore;
\<And>c c'. c\<in>set localCalls \<Longrightarrow> (c',c) \<notin> s_happensBefore;
invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore })
\<rbrakk>
 \<Longrightarrow> invariant progr
     \<lparr>calls = s_calls, 
      happensBefore = updateHb s_happensBefore vis localCalls,
      callOrigin = map_update_all s_callOrigin localCalls tx,
      transactionOrigin = s_transactionOrigin(tx \<mapsto> i), 
      knownIds = s_knownIds,
      invocationOp = s_invocationOp, 
      invocationRes = s_invocationRes\<rparr>
\<and> execution_s_check
  progr 
  i
  s_calls 
  (updateHb s_happensBefore vis localCalls) 
  (map_update_all s_callOrigin localCalls tx) 
  (s_transactionOrigin(tx \<mapsto> i))
  s_knownIds 
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  (vis \<union> set localCalls)
  []
  None
  False
  store
  (cont ())
"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  (s_transactionOrigin(tx \<mapsto> i)) 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  (Some tx)
  firstTx
  store
  (endAtomic \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (store, endAtomic \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
    `currentTransaction S1 i \<triangleq> tx`
  have action_def: "action = AEndAtomic"
    and S'a_def: "S'a = S1
     \<lparr>localState := localState S1(i \<mapsto> (store, cont ())), currentTransaction := (currentTransaction S1)(i := None),
        transactionStatus := transactionStatus S1(tx \<mapsto> Committed)\<rparr>"
    and S'a_wf: "state_wellFormed S'a"
    and Inv_def: "Inv \<longleftrightarrow> 
     invariant (prog S1)
      (invContextH (callOrigin S1) (transactionOrigin S1) (transactionStatus S1(tx \<mapsto> Committed)) (happensBefore S1)
        (calls S1) (knownIds S1) (invocationOp S1) (invocationRes S1))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    have allCommitted1: 
      "transactionStatus S1 tx' \<triangleq> Committed" if "tx' \<noteq> tx" and "callOrigin S1 c \<triangleq> tx'" for c tx'
      using that
      by (metis (no_types, lifting) Step(1) Step(15) option.exhaust_sel option.inject transactionStatus.exhaust wf_no_transactionStatus_origin_for_nothing) 

    have tx_uncommitted: "transactionStatus S1 tx \<triangleq> Uncommitted"
      using Step(1) Step(14) not_uncommitted_cases wellFormed_currentTransaction_unique_h(2) by blast

    have allCommitted2: "transactionStatus S1 t \<triangleq> Committed \<longleftrightarrow> t \<noteq> tx \<and> transactionStatus S1 t \<noteq> None" for t
      apply (cases "transactionStatus S1 t", auto simp add: tx_uncommitted)
      using Step(15) transactionStatus.exhaust by force



    have committedCallsH_simp: "committedCallsH (callOrigin S1) (transactionStatus S1(tx \<mapsto> Committed))
      = dom (calls S1)"
      using  wellFormed_callOrigin_dom[OF `state_wellFormed S1`]
 wf_callOrigin_and_calls[OF `state_wellFormed S1`]
      apply (auto simp add: committedCallsH_def isCommittedH_def exists_cases1 allCommitted2 )
      by (metis (mono_tags, lifting) allCommitted1 allCommitted2 domExists_simp)
      
    have h1: "s_calls = calls S1"
        by (simp add: Step)

      have h2: "updateHb s_happensBefore vis localCalls = happensBefore S1 |r dom (calls S1)"
apply (simp add: Step)
        apply (subst restrict_relation_noop, auto simp add: Field_def)
        using Step(1) Step(2) Step(3) happensBefore_in_calls_left happensBefore_in_calls_right by fastforce+
      

      have h3: "map_update_all s_callOrigin localCalls tx = callOrigin S1 |` dom (calls S1)"
        apply (simp add: Step)
        apply (subst restrict_map_noop)
         apply auto
        using Step(1) Step(2) Step(4) wellFormed_callOrigin_dom by fastforce+



      have h4: "s_transactionOrigin(tx\<mapsto>i) =
        transactionOrigin S1 |` {t. t \<noteq> tx \<longrightarrow> transactionStatus S1 t \<triangleq> Committed}"
        apply (simp add: Step )
        apply (subst restrict_map_noop)
        by (auto simp add: `s_transactionOrigin tx = None` Step(1) Step(5) allCommitted2 wf_transaction_status_iff_origin)

      have "localCalls \<noteq> []"
        by (simp add: tx_nonempty)
      have "distinct localCalls"
        by (simp add: Step(21))
      have  co_tx_none: "\<forall>c\<in>set localCalls. s_callOrigin c = None"
        using Step(19) by blast
      have to_tx_none: " s_transactionOrigin tx = None"
        by (simp add: assms(2))
      have co_not_tx: "\<And>c. s_callOrigin c \<noteq> Some tx"
        using Step(16) Step(4) co_tx_none map_update_all_Some_same by fastforce

      have hb_wf_l:"\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c \<triangleq> t"
        by (smt FieldI1 FieldI2 Step(1) Step(20) Step(3) Step(4) disjoint_iff_not_equal domExists_simp domIff map_update_all_get updateHb_simp2 wellFormed_happensBefore_calls_l wf_callOrigin_and_calls)
      have hb_wf_r: "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> \<exists>t. s_callOrigin c' \<triangleq> t"
        by (metis (no_types, lifting) FieldI2 Step(1) Step(20) Step(3) Step(4) disjoint_iff_not_equal domExists_simp domIff map_update_all_get updateHb_simp2 wellFormed_happensBefore_calls_r wf_callOrigin_and_calls)

      have  invocation_hb_simp:
        "invocation_happensBeforeH
    (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i))) 
    (updateHb s_happensBefore vis localCalls)
= 
(if firstTx then
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
 \<union> {i' | i' c'. c' \<in> vis \<and> i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' 
   \<and> (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis ) } \<times> {i}
else
invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore
- {i} \<times> {i'. (i,i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore })"
      proof (rule if_cases)
        assume firstTx


        show "invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)))
           (updateHb s_happensBefore vis localCalls) =
          invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore \<union>
          {i' |  i' c'.
              c' \<in> vis \<and>
              i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and>
              (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis)} \<times>
          {i}"
          using `localCalls \<noteq> []` 
            `distinct localCalls` co_tx_none to_tx_none co_not_tx hb_wf_l hb_wf_r
        proof (fuzzy_rule(noabs) invocation_happensBeforeH_one_transaction_simp2)

          show "s_transactionOrigin t \<noteq> Some i" if "s_callOrigin c \<triangleq> t" for c t
          proof -
            from `s_callOrigin c \<triangleq> t`
            have "c \<notin> set localCalls"
              using co_tx_none by fastforce
            then have "c \<notin> set localCalls \<and> s_callOrigin c \<triangleq> t"
              using that by blast
            then have f1: "t \<noteq> tx \<longrightarrow> callOrigin S1 c \<triangleq> t"
              by (simp add: Step(4) map_update_all_Some_other)
            have "s_callOrigin c \<noteq> Some tx"
              using co_not_tx by blast
            then have "t \<noteq> tx"
              using that by blast
            then have "s_transactionOrigin(t \<mapsto> i) \<noteq> s_transactionOrigin"
              using f1 by (metis (no_types) Step(1) Step(22) Step(5) \<open>firstTx\<close> allCommitted2 fun_upd_same fun_upd_twist state_wellFormed_transactionStatus_transactionOrigin)
            then show "s_transactionOrigin t \<noteq> Some i"
              by (metis (no_types) fun_upd_triv)
          qed

        qed auto
      next
        assume "\<not> firstTx"
        from this obtain old_c old_t 
          where "s_callOrigin old_c \<triangleq> old_t"
            and "s_transactionOrigin old_t \<triangleq> i"
            and "transactionStatus S1 old_t \<triangleq> Committed"
          using Step(22) Step(4) Step(5) allCommitted2 map_update_all_Some_other by fastforce


        show " invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)))
     (updateHb s_happensBefore vis localCalls) =
    invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore -
    {i} \<times> {i'. (i, i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore}"
          using tx_nonempty `s_transactionOrigin old_t \<triangleq> i` co_tx_none `s_callOrigin old_c \<triangleq> old_t`
                hb_wf_l co_not_tx
        proof (fuzzy_rule invocation_happensBeforeH_more_transactions_simp2)

          show "\<And>c c'. (c, c') \<in> s_happensBefore \<Longrightarrow> (c, c') \<in> s_happensBefore"
            by simp

          show "Field s_happensBefore \<inter> set localCalls = {}"
            by (simp add: Step(20))

          show "\<And>c. i_callOriginI_h s_callOrigin s_transactionOrigin c \<triangleq> i \<Longrightarrow> c \<in> vis"
            by (simp add: Step(23) i_callOriginI_h_update_to2)

          show "\<And>c c'. \<lbrakk>c' \<in> vis; (c, c') \<in> s_happensBefore\<rbrakk> \<Longrightarrow> c \<in> vis"
          proof -
            fix c :: callId and c' :: callId
            assume a1: "c' \<in> vis"
            assume a2: "(c, c') \<in> s_happensBefore"
            have f3: "\<forall>c. c \<notin> Field s_happensBefore \<or> (\<forall>ca. ca \<notin> set localCalls \<or> c \<noteq> ca)"
              using Step(20) by auto
            have f4: "c' \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI2)
            have "c \<in> Field s_happensBefore"
              using a2 by (simp add: FieldI1)
            then show "c \<in> vis"
              using f4 f3 a2 a1 by (metis (no_types) Step(1) Step(13) Step(3) UnCI UnE updateHb_simp2 wf_vis_downwards_closed2)
          qed



        qed
      qed



      

      have inv_cont2: "invariant progr
       \<lparr>calls = s_calls, happensBefore = updateHb s_happensBefore vis localCalls,
          callOrigin = map_update_all s_callOrigin localCalls tx, transactionOrigin = s_transactionOrigin(tx \<mapsto> i),
          knownIds = s_knownIds, invocationOp = s_invocationOp, invocationRes = s_invocationRes\<rparr> \<and>
      execution_s_check progr i s_calls (updateHb s_happensBefore vis localCalls)
       (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)) s_knownIds s_invocationOp s_invocationRes
     generatedLocal generatedLocalPrivate (vis \<union> set localCalls) [] None False store (cont ())"
        using  `distinct localCalls`
      proof (rule inv_cont)
        show h5: "\<And>c. c \<in> set localCalls \<Longrightarrow> s_callOrigin c = None"
          using co_tx_none by auto
        show h6: "\<And>c c'. c \<in> set localCalls \<Longrightarrow> (c, c') \<notin> s_happensBefore"
          using co_tx_none hb_wf_l by fastforce
        show h7: "\<And>c c'. c \<in> set localCalls \<Longrightarrow> (c', c) \<notin> s_happensBefore"
          using co_tx_none hb_wf_r by fastforce
        show "\<And>c. c \<in> set localCalls \<Longrightarrow> c \<notin> vis"
          using Step(18) by blast

        show "invocation_happensBeforeH (i_callOriginI_h (map_update_all s_callOrigin localCalls tx) (s_transactionOrigin(tx \<mapsto> i)))
         (updateHb s_happensBefore vis localCalls) =
        (if firstTx
         then invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore \<union>
              {i' | i' c'.
                  c' \<in> vis \<and>
                  i_callOriginI_h s_callOrigin s_transactionOrigin c' \<triangleq> i' \<and>
                  (\<forall>c''. i_callOriginI_h s_callOrigin s_transactionOrigin c'' \<triangleq> i' \<longrightarrow> c'' \<in> vis)} \<times>
              {i}
         else invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore -
              {i} \<times>
              {i'. (i, i') \<in> invocation_happensBeforeH (i_callOriginI_h s_callOrigin s_transactionOrigin) s_happensBefore})"
          by (auto simp add: committedCallsH_simp invocation_hb_simp)
      qed



      show "Inv"
        unfolding Inv_def invContextH_def
      proof (fuzzy_rule inv_cont2[THEN conjunct1])
      qed (auto simp add:  committedCallsH_simp h1 h2 h3 h4, (auto simp add: Step))


    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "currentTransaction S'a i = None"
        by (simp add: S'a_def)

      show "state_wellFormed S'a"
        using S'a_wf by auto

      show "happensBefore S'a = updateHb (happensBefore S'a) (vis\<union>set localCalls)  []"
        by simp

      show "callOrigin S'a = map_update_all (callOrigin S'a) [] (the None)"
        by simp

      show " localState S'a i \<triangleq> (store, cont ())"
        by (simp add: S'a_def Step)
      
      show "currentProc S'a i \<triangleq> toImpl"
        by (simp add: S'a_def Step)

      show "visibleCalls S'a i \<triangleq> (vis \<union> set localCalls \<union> set [])"
        by (simp add: S'a_def Step)

      show "\<And>tx'. None \<noteq> Some tx' \<Longrightarrow> transactionStatus S'a tx' \<noteq> Some Uncommitted"
        by (simp add: S'a_def Step)

      show "sorted_by (happensBefore S'a) []"
        by (simp add: sorted_by_empty)

      show "execution_s_check (prog S'a) i (calls S'a) (happensBefore S'a) (callOrigin S'a)
       (transactionOrigin S'a) (knownIds S'a) (invocationOp S'a) (invocationRes S'a)
       {x. generatedIds S'a x \<triangleq> i} generatedLocalPrivate (vis \<union> set localCalls) [] None False store (cont ())"
      proof (fuzzy_rule inv_cont2[THEN conjunct2])
      qed (simp add: S'a_def Step)+

      obtain c where "c\<in>set localCalls"
        using `localCalls \<noteq> []` by fastforce



      show "False = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        using  \<open>c \<in> set localCalls\<close>  by (auto simp add: S'a_def intro!: exI[where x=c] exI[where x=tx]
            Step(1) Step(14) state_wellFormed_current_transaction_origin
            Step(4) map_update_all_Some_same, simp add: Step(4) map_update_all_Some_same) 

      show "\<And>c. i_callOriginI S'a c \<triangleq> i \<Longrightarrow> c \<in> vis \<union> set localCalls"
        apply (auto simp add: S'a_def i_callOriginI_h_def split: option.splits)
        using Step(1) Step(13) state_wellFormed_ls_visibleCalls_callOrigin by fastforce

      show "generatedLocalPrivate \<subseteq> {x. generatedIds S'a x \<triangleq> i}"
        using Step by (simp add: S'a_def)

      fix x
      assume c0: "x \<in> generatedLocalPrivate"

      from c0
      have "uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1)   (currentProc S1) x"
        by (simp add: Step(25))

      thus "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a) (localState S'a) (currentProc S'a) x"
        by (auto simp add: S'a_def uid_is_private_def new_unique_not_in_other_invocations_def)




    qed (simp add: S'a_def Step; fail)+
  qed
qed


lemma execution_s_check_LocalStep:
  assumes f_res: "f store = (True, store', res)"
    and fin_dom: "finite (dom store) \<Longrightarrow> finite (dom store')"

and cont: "
\<And>Sn.
\<lbrakk>
state_wellFormed Sn;
calls Sn = s_calls;
happensBefore Sn = updateHb s_happensBefore vis localCalls;
callOrigin Sn = map_update_all s_callOrigin localCalls (the tx);
transactionOrigin Sn = s_transactionOrigin;
knownIds Sn = s_knownIds;
invocationOp Sn = s_invocationOp;
invocationRes Sn = s_invocationRes;
prog Sn = progr;
generatedLocal = {x. generatedIds Sn x \<triangleq> i};
localState Sn i \<triangleq> (store, (WaitLocalStep f \<bind> cont));
currentProc Sn i \<triangleq> toImpl;
visibleCalls Sn i \<triangleq>  (vis \<union> set localCalls);
currentTransaction Sn i = tx;
(\<forall>tx'. tx \<noteq> Some tx' \<longrightarrow> transactionStatus Sn tx' \<noteq> Some Uncommitted);
(case tx of Some tx' \<Rightarrow> set localCalls =  {c. callOrigin Sn c \<triangleq> tx'} | None \<Rightarrow> localCalls = []);
(sorted_by (happensBefore Sn) localCalls);
(vis \<inter> set localCalls = {});
(dom s_callOrigin \<inter> set localCalls = {});
(Field s_happensBefore \<inter> set localCalls = {});
distinct localCalls;
(firstTx \<longleftrightarrow> (\<nexists>c tx . callOrigin Sn c \<triangleq> tx \<and> transactionOrigin Sn tx \<triangleq> i \<and> transactionStatus Sn tx \<triangleq> Committed ));
(\<forall>c. i_callOriginI_h s_callOrigin s_transactionOrigin c \<triangleq> i \<longrightarrow> c \<in> vis);
(generatedLocalPrivate \<subseteq> generatedLocal);
(\<forall>v\<in>generatedLocalPrivate. uid_is_private i (calls Sn) (invocationOp Sn) (invocationRes Sn) (knownIds Sn) (generatedIds Sn) (localState Sn) (currentProc Sn) v);
(finite (dom store))
\<rbrakk> \<Longrightarrow>
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store'
  (res \<bind> cont)"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (WaitLocalStep f \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (store, WaitLocalStep f \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
    f_res
  have a0: "localState S1 i \<triangleq>      (store, impl_language_loops.io.WaitLocalStep (\<lambda>s. case f s of (a, b, c) \<Rightarrow> (a, b, c \<bind> cont)))"
   and a1: "currentProc S1 i \<triangleq> toImpl"
   and a2: "f store = (True, store', res)"
   and a3: "action = ALocal True"
   and S'a_def: "S'a = S1\<lparr>localState := localState S1(i \<mapsto> (store', res \<bind> cont))\<rparr>"
   and a5: "Inv"
    by (auto simp add: step_s.simps split: prod.splits)


  show "Inv \<and> traceCorrect_s trace'"
  proof

    show "Inv"
      using a5 by auto


    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      from `case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S1 c \<triangleq> tx'}`
      show "case tx of None \<Rightarrow> localCalls = [] | Some tx' \<Rightarrow> set localCalls = {c. callOrigin S'a c \<triangleq> tx'}"
        by (auto simp add: S'a_def split: option.splits)

      show "sorted_by (happensBefore S'a) localCalls"
        using Step(17) Step(3) by (simp add: S'a_def )




      show "generatedLocalPrivate \<subseteq> {x. generatedIds S1 x \<triangleq> i}"
        apply auto
        by (meson Step(25) uid_is_private_def)

      show "finite (dom store')"
        using Step(26) fin_dom by blast

      show " execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds s_invocationOp
         s_invocationRes {x. generatedIds S1 x \<triangleq> i} generatedLocalPrivate vis localCalls tx
         (\<forall>c txa.
             s_transactionOrigin txa \<triangleq> i \<longrightarrow>
             map_update_all s_callOrigin localCalls (the tx) c \<triangleq> txa \<longrightarrow> transactionStatus S1 txa \<noteq> Some Committed)
         store' (res \<bind> cont)"
        thm cont
      proof (fuzzy_rule cont[where Sn=S1])
        show "generatedLocal = {x. generatedIds S1 x \<triangleq> i}"
          by (simp add: Step(10))

        show "firstTx =
            (\<forall>c txa.
                s_transactionOrigin txa \<triangleq> i \<longrightarrow>
                map_update_all s_callOrigin localCalls (the tx) c \<triangleq> txa \<longrightarrow> transactionStatus S1 txa \<noteq> Some Committed)"
          by (simp add: Step(22) Step(4) Step(5))

        show "sorted_by (happensBefore S1) localCalls"
          by (simp add: Step(17))

        show "generatedLocalPrivate \<subseteq> generatedLocal"
          by (simp add: Step(24))

        show "\<forall>v\<in>generatedLocalPrivate.
           uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1)
            (localState S1) (currentProc S1) v"
          using Step(25) by blast


      qed (simp add: Step; fail)+

      fix x
      assume a0: "x \<in> generatedLocalPrivate"
      hence "uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1) (currentProc S1) x"
        using Step(25) by blast

      thus "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a)           (localState S'a) (currentProc S'a) x"
        by (auto simp add:S'a_def uid_is_private_def new_unique_not_in_other_invocations_def)

      


    qed (simp add: S'a_def Step; fail)+

      
  qed
qed


lemma execution_s_check_pause:
  assumes cont: "

 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (pause \<bind> cont)
"
  unfolding pause_def
proof (rule execution_s_check_LocalStep; (assumption | rule refl | fuzzy_rule cont)?, goal_cases)
  case (1 Sn)

  show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
               s_invocationOp s_invocationRes generatedLocal generatedLocalPrivate vis localCalls tx firstTx store
               (impl_language_loops.io.WaitReturn () \<bind> cont)"
  proof (fuzzy_rule cont)
    show "cont () = impl_language_loops.io.WaitReturn () \<bind> cont"
      by auto
  qed
qed



lemma execution_s_check_makeRef:
  assumes cont: "\<And>ref. 
\<lbrakk>ref \<notin> dom store

\<rbrakk> \<Longrightarrow>
\<comment> \<open>

\<close>
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  (store(ref \<mapsto> v))
  (cont ref)"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (makeRef v \<bind> cont)
"
  unfolding makeRef_def
proof (rule execution_s_check_LocalStep, goal_cases A B C)
  case A
  show "(let r = LEAST i. store i = None in (True, store(r \<mapsto> v), impl_language_loops.io.WaitReturn r)) =
    (True, store((LEAST i. store i = None) \<mapsto> v), WaitReturn (LEAST i. store i = None))"
    by (auto simp add: Let_def)

next
  case B
  thus "finite (dom (store(LEAST i. store i = None \<mapsto> v)))"
    by force
next 
  case C

  show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
               s_invocationOp s_invocationRes generatedLocal generatedLocalPrivate vis localCalls tx firstTx
               (store(LEAST i. store i = None \<mapsto> v))
               (impl_language_loops.io.WaitReturn (LEAST i. store i = None) \<bind> cont)"
  proof (fuzzy_rule cont)

    have "finite (dom store)"
      using `finite (dom store)` .

    show "(LEAST i. store i = None) \<notin> dom store"
      by (metis (mono_tags, lifting) LeastI \<open>finite (dom store)\<close> domIff ex_new_if_finite infinite_UNIV_char_0)

    show "cont (LEAST i. store i = None) = impl_language_loops.io.WaitReturn (LEAST i. store i = None) \<bind> cont"
      by auto
  qed
qed


lemma execution_s_check_read:
  assumes ref_defined: "ref \<in> dom store"
  assumes cont: "
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (cont (the (store ref)))"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (read ref \<bind> cont)
"
  unfolding read_def
proof (rule execution_s_check_LocalStep, goal_cases A B C)
  case A
  show "(case store ref of None \<Rightarrow> (False, store, impl_language_loops.io.WaitReturn default)
     | Some v \<Rightarrow> (True, store, impl_language_loops.io.WaitReturn v)) =
    (True, store, WaitReturn (the (store ref)))"
    using ref_defined by (auto simp add:  split: option.splits)


next
  case B
  show "finite (dom store) \<Longrightarrow> finite (dom store)"
    by assumption
next 
  case (C Sn)

  show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
               s_invocationOp s_invocationRes generatedLocal generatedLocalPrivate vis localCalls tx firstTx store
               (impl_language_loops.io.WaitReturn (the (store ref)) \<bind> cont)"
  proof (fuzzy_rule cont)

    have "finite (dom store)"
      using `finite (dom store)` .

    show "cont (the (store ref)) = impl_language_loops.io.WaitReturn (the (store ref)) \<bind> cont"
      by auto
  qed
qed



lemma execution_s_check_assign:
  assumes ref_defined: "ref \<in> dom store"
  assumes cont: "
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  (store(ref \<mapsto> v))
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (assign ref v \<bind> cont)
"
  unfolding assign_def
proof (rule execution_s_check_LocalStep, goal_cases A B C)
  case A
  show "(case store ref of None \<Rightarrow> (False, store, impl_language_loops.io.WaitReturn ())
     | Some x \<Rightarrow> (True, store(ref \<mapsto> v), impl_language_loops.io.WaitReturn ())) =
    (True, store(ref \<mapsto> v), WaitReturn ())"
    using ref_defined by (auto simp add:  split: option.splits)


next
  case B
  thus "finite (dom (store(ref \<mapsto> v)))"
    by force
next 
  case (C Sn)

  show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
               s_invocationOp s_invocationRes generatedLocal generatedLocalPrivate vis localCalls tx firstTx
               (store(ref \<mapsto> v)) (impl_language_loops.io.WaitReturn () \<bind> cont)"
  proof (fuzzy_rule cont)

    have "finite (dom store)"
      using `finite (dom store)` .

    show "cont () = impl_language_loops.io.WaitReturn () \<bind> cont"
      by auto
  qed
qed


lemma execution_s_check_update:
  assumes ref_defined: "ref \<in> dom store"
  assumes cont: "
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  (store(ref \<mapsto> f (the (store ref))))
  (cont ())"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  tx
  firstTx
  store
  (update ref f \<bind> cont)
"
  unfolding update_def
proof (rule execution_s_check_LocalStep, goal_cases A B C)
  case A
  show "(case store ref of None \<Rightarrow> (False, store, impl_language_loops.io.WaitReturn ())
     | Some v \<Rightarrow> (True, store(ref \<mapsto> f v), impl_language_loops.io.WaitReturn ())) =
    (True,  store(ref \<mapsto> f (the (store ref))), WaitReturn ())"
    using ref_defined by (auto simp add:  split: option.splits)


next
  case B
  thus " finite (dom (store(ref \<mapsto> f (the (store ref)))))"
    by force
next 
  case (C Sn)

  show "execution_s_check progr i s_calls s_happensBefore s_callOrigin s_transactionOrigin s_knownIds
               s_invocationOp s_invocationRes generatedLocal generatedLocalPrivate vis localCalls tx firstTx
               (store(ref \<mapsto> f (the (store ref)))) (impl_language_loops.io.WaitReturn () \<bind> cont)"
  proof (fuzzy_rule cont)

    have "finite (dom store)"
      using `finite (dom store)` .

    show "cont () = impl_language_loops.io.WaitReturn () \<bind> cont"
      by auto
  qed
qed


subsection "Loops"




lemma execution_s_check_loop:
  assumes cont: " \<lbrakk>
True
\<comment> \<open>

\<close>
\<rbrakk> \<Longrightarrow> 
 execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  currentTx
  firstTx
  store
  (cont res)"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  currentTx
  firstTx
  store
  (Loop body afterBody \<bind> cont)
"




lemma updateHb_restrict:
 " updateHb hb vis cs |r S =
   updateHb (hb |r S) (vis \<inter> S) (filter (\<lambda>x. x \<in> S) cs)"
  by (induct cs arbitrary: vis hb,
   auto simp add: restrict_relation_def updateHb.simps,
  (metis (no_types, lifting) Int_iff Un_iff mem_Sigma_iff singletonD updateHb_cases)+)



lemma execution_s_check_dbop:
  assumes progr_wf: "program_wellFormed progr"
    (* might add this to ensure progress:  
     and query_res_exists: "True"*)
and cont: "\<And>c res. \<lbrakk>
querySpec progr op \<lparr>
      calls = s_calls |` (vis \<union> set localCalls), 
      happensBefore=updateHb (s_happensBefore |r vis) vis localCalls\<rparr> res
\<comment> \<open>

\<close>
\<rbrakk> \<Longrightarrow> 
 execution_s_check
  progr 
  i
  (s_calls(c \<mapsto> Call op res))
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  (generatedLocalPrivate - uniqueIds op - uniqueIds res)
  vis
  (localCalls @ [c])
  (Some tx)
  firstTx
  store
  (cont res)"


shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPrivate
  vis
  localCalls
  (Some tx)
  firstTx
  store
  (call op \<bind> cont)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (store, call op \<bind> cont)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
    ` currentTransaction S1 i \<triangleq> tx`
`visibleCalls S1 i \<triangleq> (vis \<union> set localCalls)`
  obtain c res
    where c0: "localState S1 i \<triangleq> (store, call op \<bind> cont)"
   and c1: "currentProc S1 i \<triangleq> toImpl"
   and c2: "currentTransaction S1 i \<triangleq> tx"
   and c3: "visibleCalls S1 i \<triangleq> (vis \<union> set localCalls)"
   and c4: "action = ADbOp c op res"
   and c5: "Inv"
   and S'a_def: "S'a = S1 \<lparr>localState := localState S1(i \<mapsto> (store, cont res)), calls := calls S1(c \<mapsto> Call op res), callOrigin := callOrigin S1(c \<mapsto> tx), visibleCalls := visibleCalls S1(i \<mapsto> insert c (vis \<union> set localCalls)), happensBefore := happensBefore S1 \<union> (vis \<union> set localCalls) \<times> {c}\<rparr>"
   and fresh_c: "calls S1 c = None"
   and qry: "querySpec (prog S1) op (getContextH (calls S1) (happensBefore S1) (Some (vis \<union> set localCalls))) res"
    by (auto simp add: step_s.simps)


  show "Inv \<and> traceCorrect_s trace'"
  proof

    show "Inv" using `Inv` .

    show "traceCorrect_s trace'"
      using `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
    proof (rule use_execution_s_check)
      show "\<And>p t. (AInvoc p, t) \<notin> set trace'"
        using Step by auto

      show "state_wellFormed S'a"
        using Step state_wellFormed_combine_s1 by blast

      show "calls S'a = s_calls(c \<mapsto> Call op res)"
        by (simp add: S'a_def Step)

      show "happensBefore S'a = updateHb s_happensBefore vis (localCalls@[c])"
        by (auto simp add: S'a_def Step
          updateHb_chain[symmetric, where vis'="set localCalls \<union> vis"]
          updateHb_single)

      have s: "map_of (map (\<lambda>c. (c, tx)) localCalls) c = Some t
        \<longleftrightarrow> (c\<in>set localCalls \<and> t = tx) " for c t
        by (auto simp add:  map_of_Some comp_def Step)


      show "callOrigin S'a =  map_update_all s_callOrigin (localCalls@[c]) (the (Some tx))"
        by (auto simp add: map_update_all_get  S'a_def Step map_add_def intro!: ext dest!: map_of_SomeD split: option.splits)

      show "case Some tx of None \<Rightarrow> localCalls @ [c] = []
            | Some tx' \<Rightarrow> set (localCalls @ [c]) = {c. callOrigin S'a c \<triangleq> tx'}"
        using Step(16) Step(4)  by (auto simp add: s S'a_def Step map_add_def map_of_None split: option.splits del: )

      have "c \<notin> set localCalls"
        by (meson Step(1) UnCI c3 fresh_c wellFormed_visibleCallsSubsetCalls2)

      have "c \<notin> vis"
        by (meson Step(1) UnCI c3 fresh_c wellFormed_visibleCallsSubsetCalls2)


      have "callOrigin S1 c = None"
        using wellFormed_callOrigin_dom[OF `state_wellFormed S1`] fresh_c by blast

      hence "s_callOrigin c = None"
        using `callOrigin S1 = map_update_all s_callOrigin localCalls (the (Some tx))`
        by (auto simp add: map_update_all_get split: if_splits)


      show "sorted_by (happensBefore S'a) (localCalls @ [c])"
      proof (auto simp add: sorted_by_append_iff sorted_by_single)
        from `sorted_by (happensBefore S1) localCalls`
        show "sorted_by (happensBefore S'a) localCalls"
          apply (auto simp add: S'a_def)
          apply (auto simp add: sorted_by_def)
          by (metis (mono_tags, lifting) Step(1) Step(16) fresh_c less_trans mem_Collect_eq nth_mem option.distinct(1) option.simps(5) wellFormed_callOrigin_dom2)

        show "\<And>x. \<lbrakk>x \<in> set localCalls; (c, x) \<in> happensBefore S'a\<rbrakk> \<Longrightarrow> False"
          apply (auto simp add: S'a_def Step)
          using Step(1) Step(3) fresh_c wellFormed_happensBefore_calls_l apply blast
          using Step(18) apply auto[1]
          using \<open>c \<notin> set localCalls\<close> by auto
      qed

      from `vis \<inter> set (localCalls) = {}`
      show "vis \<inter> set (localCalls @ [c]) = {}"
        by (auto simp add: `c \<notin> vis`)


      show "dom s_callOrigin \<inter> set (localCalls @ [c]) = {}"
        apply (auto simp add: `s_callOrigin c = None`)
        using Step(19) by blast

      have "c \<notin> Field s_happensBefore"
        by (metis Field_Un Step(1) Step(3) UnCI fresh_c updateHb_simp_split wellFormed_happensBefore_Field)

      from this and `Field s_happensBefore \<inter> set localCalls = {}`
      show "Field s_happensBefore \<inter> set (localCalls @ [c]) = {}"
        by auto

      from `distinct localCalls` and `c\<notin>set localCalls`
      show "distinct (localCalls @ [c])"
        by auto

      show " execution_s_check progr i (s_calls(c \<mapsto> Call op res)) s_happensBefore s_callOrigin
       s_transactionOrigin s_knownIds s_invocationOp s_invocationRes {x. generatedIds S1 x \<triangleq> i} (generatedLocalPrivate - uniqueIds op - uniqueIds res) vis
       (localCalls @ [c]) (Some tx) firstTx store (cont res)"
      proof (fuzzy_rule cont)
        show "querySpec progr op
             \<lparr>calls = s_calls |` (vis \<union> set localCalls),
              happensBefore = updateHb (s_happensBefore |r vis) vis localCalls\<rparr>
             res"
        proof (fuzzy_rule qry; auto simp add: Step getContextH_def del: equalityI)
          have [simp]: "s_happensBefore |r (vis \<union> set localCalls) = (s_happensBefore |r vis)"
            using `Field s_happensBefore \<inter> set localCalls = {}`
            by (auto simp add: restrict_relation_def Field_def)


          show " updateHb s_happensBefore vis localCalls |r (vis \<union> set localCalls) =
            updateHb (s_happensBefore |r vis) vis localCalls"
            by (auto simp add: updateHb_restrict)
        qed

        from `generatedLocal = {x. generatedIds S1 x \<triangleq> i}`
        show "generatedLocal = {x. generatedIds S1 x \<triangleq> i}" .
      qed

      from `firstTx = (\<nexists>c tx. callOrigin S1 c \<triangleq> tx \<and> transactionOrigin S1 tx \<triangleq> i \<and> transactionStatus S1 tx \<triangleq> Committed)`
      show "firstTx = (\<nexists>c tx. callOrigin S'a c \<triangleq> tx \<and> transactionOrigin S'a tx \<triangleq> i \<and> transactionStatus S'a tx \<triangleq> Committed)"
        apply auto
         apply (auto simp add: S'a_def split: if_splits)
        using Step(1) c2 not_uncommitted_cases wellFormed_currentTransaction_unique_h(2) apply blast
        using \<open>callOrigin S1 c = None\<close> by force

      show "generatedLocalPrivate - uniqueIds op - uniqueIds res \<subseteq> {x. generatedIds S1 x \<triangleq> i}"
        apply auto
        by (meson Step(25) uid_is_private_def)

      
      fix x
      assume a0: "x \<in> generatedLocalPrivate - uniqueIds op - uniqueIds res"
      hence "uid_is_private i (calls S1) (invocationOp S1) (invocationRes S1) (knownIds S1) (generatedIds S1) (localState S1) (currentProc S1) x"
        using Step(25) by auto


      thus "uid_is_private i (calls S'a) (invocationOp S'a) (invocationRes S'a) (knownIds S'a) (generatedIds S'a)           (localState S'a) (currentProc S'a) x"
        using a0 by (auto simp add: S'a_def uid_is_private_def new_unique_not_in_calls_def new_unique_not_in_calls_result_def new_unique_not_in_other_invocations_def)


      

    qed (simp add: S'a_def Step; fail)+
  qed
qed



lemma execution_s_check_return:
  assumes progr_wf: "program_wellFormed progr"
    and query_res_exists: "True"
and inv: "invariant progr
  \<lparr>
        calls = s_calls, 
        happensBefore = s_happensBefore , 
        callOrigin  = s_callOrigin,
        transactionOrigin = s_transactionOrigin,
        knownIds = s_knownIds  \<union> uniqueIds res,
        invocationOp = s_invocationOp,
        invocationRes = s_invocationRes(i \<mapsto> res)
      \<rparr>"
shows"execution_s_check
  progr 
  i
  s_calls
  s_happensBefore 
  s_callOrigin
  s_transactionOrigin 
  s_knownIds
  s_invocationOp
  s_invocationRes
  generatedLocal
  generatedLocalPriate
  vis
  []
  None
  firstTx
  store
  (return res)
"
proof show_proof_rule
  case (Step trace S1 S_end action S'a Inv trace')


  from ` S1 ~~ (i, action, Inv) \<leadsto>\<^sub>S S'a`
    `localState S1 i \<triangleq> (store, return res)`
    `currentProc S1 i \<triangleq> toImpl`
    `\<And>proc. action \<noteq> AInvoc proc`
  have c2: "action = AReturn res"
   and c3: "currentTransaction S1 i = None"
   and S'a_def: "S'a = S1 \<lparr>localState := (localState S1)(i := None), currentProc := (currentProc S1)(i := None), visibleCalls := (visibleCalls S1)(i := None), invocationRes := invocationRes S1(i \<mapsto> res), knownIds := knownIds S1 \<union> uniqueIds res\<rparr>"
   and Inv_def: "Inv \<longleftrightarrow> invariant (prog S1) (invContextH (callOrigin S1) (transactionOrigin S1) (transactionStatus S1) (happensBefore S1) (calls S1) (knownIds S1 \<union> uniqueIds res) (invocationOp S1) (invocationRes S1(i \<mapsto> res)))"
    by (auto simp add: step_s.simps)

  show "Inv \<and> traceCorrect_s trace'"
  proof

    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus1: "transactionStatus S1 tx' \<noteq> Some Uncommitted" for tx'
      by auto

    have txStatus2: "transactionStatus S1 tx \<triangleq> y
      \<longleftrightarrow> (transactionStatus S1 tx \<triangleq> Committed \<and> y = Committed)" for tx y
      apply auto
      using transactionStatus.exhaust txStatus1 by auto



    from `\<forall>tx'. None \<noteq> Some tx' \<longrightarrow> transactionStatus S1 tx' \<noteq> Some Uncommitted`
    have txStatus3: "transactionStatus S1 tx \<triangleq> Committed
      \<longleftrightarrow>transactionStatus S1 tx \<noteq> None" for tx
      using transactionStatus.exhaust by (auto, blast)


    have commmitted: "committedTransactions S1 = dom s_transactionOrigin"
      apply (auto simp add: `transactionOrigin S1 = s_transactionOrigin`[symmetric] txStatus1)
      apply (simp add: Step(1) txStatus3 wf_transaction_status_iff_origin)
      by (simp add: Step(1) state_wellFormed_transactionStatus_transactionOrigin txStatus3)

    have committed2: "committedCalls S1 = dom (calls S1)"
      using Step(1) committedCalls_allCommitted txStatus1 by blast 

    hence committed3: "committedCallsH s_callOrigin (transactionStatus S1) =  dom s_calls"
      by (simp add: Step)


    show "Inv" 
      unfolding Inv_def invContextH_def
    proof (fuzzy_rule inv; (simp add: Step commmitted committed3))

      show "s_callOrigin = s_callOrigin |` dom s_calls"
      proof (rule restrict_map_noop[symmetric])
        show "dom s_callOrigin \<subseteq> dom s_calls"
          using Step(1) Step(2) Step(4) wellFormed_callOrigin_dom by fastforce
      qed

      show "s_happensBefore = s_happensBefore |r dom s_calls"
      proof (rule restrict_relation_noop[symmetric])
        show "Field s_happensBefore \<subseteq> dom s_calls"
          apply (auto simp add: Field_def)
          using Step(1) Step(2) Step(3) happensBefore_in_calls_left happensBefore_in_calls_right by fastforce+
      qed
    qed


    show "traceCorrect_s trace'"
    proof (cases trace')
      case Nil
      then show ?thesis
        using traceCorrect_s_empty by auto 
    next
      case (Cons a list)

      obtain action' Inv' where a_def: "a = (action', Inv')"
        by force

      have no_invoc: "\<And>proc. action' \<noteq> AInvoc proc"
        using `trace = (action, Inv) # trace'` `\<forall>p t. (AInvoc p, t) \<notin> set trace` a_def local.Cons by auto



      from Cons `S'a ~~ (i, trace') \<leadsto>\<^sub>S* S_end`
      obtain S'' where "S'a ~~ (i, (action', Inv')) \<leadsto>\<^sub>S S''"
        using steps_s_cons_simp a_def by blast 
      hence False
        using S'a_def no_invoc
        by (auto simp add: step_s.simps)
      thus "traceCorrect_s trace'" ..
    qed
  qed
qed




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





end