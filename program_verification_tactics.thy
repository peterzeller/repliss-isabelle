section "Program Verification Tactics"

theory program_verification_tactics
  imports 
    invariant_simps 
    unique_ids
    single_invocation_correctness2
    "Case_Labeling.Case_Labeling"
    execution_invariants2
    execution_invariants_s
    execution_invariants_unused
    program_proof_rules
    crdt_specs
begin

text "We define some tactics to generate proof obligations for showing a programs correctness.
This theory mainly adds nicer labels to already existing methods using the case labeling package."


context begin
interpretation Labeling_Syntax .

lemma increase_bound:
  assumes "\<exists>bound. (checkCorrect2F ^^Suc bound) bot (progr, {}, S, i)"
  shows "\<exists>bound. (checkCorrect2F ^^bound) bot (progr, {}, S, i)"
  using assms by blast



lemma DC_show_programCorrect:
  fixes ct defines "ct' \<equiv> \<lambda>pos name. (name, pos,[]) # ct"
  assumes invInitial: "C\<langle>Suc n1, ct' n1 ''invariant_initial_state'', n2: invariant_all' (initialState progr)\<rangle>"
    and procedureCorrect: "\<And>S i. \<lbrakk>B\<langle>''in_initial_state'', n2: S\<in>initialStates' progr i\<rangle>\<rbrakk> 
          \<Longrightarrow> C\<langle>Suc n2, (''procedure_correct'', n2, [VAR S, VAR i])#ct, n3: procedureCorrect S i\<rangle>"
  shows "C\<langle>n1,ct,n3: programCorrect progr\<rangle>"
  using assms
  unfolding LABEL_simps
  by (metis initialStates'_same procedureCorrect_def show_programCorrect_using_checkCorrect1)  


lemma DC_show_procedureCorrect:
  fixes ct defines "ct' \<equiv> \<lambda>pos name. (name, pos,[]) # ct"
  assumes "C\<langle>Suc n1, ct' n1 ''after_invocation'', n2: invariant_all' S\<rangle>"
    and  "C\<langle>Suc n2, (''execution'', n2, [])#ct, n3: execution_s_correct S i\<rangle>"
  shows "C\<langle>n1,ct,n3: procedureCorrect S i\<rangle>"
  using assms
  unfolding LABEL_simps by (auto simp add: procedureCorrect_def)

lemma DC_final:
  assumes "V\<langle>(''g'',inp,[]), ct: a\<rangle>"
  shows "C\<langle>inp,ct,Suc inp: a\<rangle>"
  using assms unfolding LABEL_simps by auto


  lemma DC_final2:
    assumes "V\<langle>(n,i,v), ct: a\<rangle>"
    shows "C\<langle>inp,(n,i,v)#ct,Suc inp: a\<rangle>"
    using assms unfolding LABEL_simps by auto

lemma show_initial_state_prop:
  assumes a1: "Si\<in>initialStates' progr i"
and a2: "\<And>S_pre proc initState impl.
       \<lbrakk>
        B\<langle>''Si_def'', n1 : Si = S_pre
        \<lparr>localState := localState S_pre(i \<mapsto> initState), 
         currentProc := currentProc S_pre(i \<mapsto> impl), 
         visibleCalls := visibleCalls S_pre(i \<mapsto> {}),
         invocationOp := invocationOp S_pre(i \<mapsto> (proc))\<rparr>\<rangle>;
        B\<langle>''progr_def'', n1 : prog S_pre = progr\<rangle>; 
        B\<langle>''proc_initState'', n1 : initState = fst (procedure progr proc)\<rangle>; 
        B\<langle>''proc_impl'', n1 : impl = snd (procedure progr proc)\<rangle>; 
        B\<langle>''ids_in_args_are_knownIds'', n1 : uniqueIds proc \<subseteq> knownIds S_pre\<rangle>; 
        B\<langle>''invariant_pre'', n1 : invariant_all' S_pre\<rangle>;
        B\<langle>''wf_pre'', n1 : state_wellFormed S_pre\<rangle>; 
        B\<langle>''i_fresh'', n1 : invocationOp S_pre i = None\<rangle>; 
        B\<langle>''no_uncommitted_txns'', n1 : \<forall>tx. transactionStatus S_pre tx \<noteq> Some Uncommitted\<rangle>;
        B\<langle>''no_txns_in_i'', n1 : \<forall>tx. transactionOrigin S_pre tx \<noteq> Some i\<rangle>
        \<rbrakk> \<Longrightarrow> C\<langle>Suc n1, (''show_P'', n1, [VAR S_pre, VAR proc, VAR  initState, VAR  impl])#ct, n2 :   P Si i\<rangle>"
  shows "C\<langle>n1, ct, n : P Si i\<rangle>"
  unfolding LABEL_simps 
proof -
  from a1[unfolded initialStates'_def]
  obtain S proc initState impl 
    where "prog S = progr"
      and "procedure progr proc = (initState, impl)"
      and "uniqueIds proc \<subseteq> knownIds S"
      and "invariant_all' S"
      and "state_wellFormed S"
      and "invocationOp S i = None"
      and "\<forall>tx. transactionStatus S tx \<noteq> Some Uncommitted"
      and "\<forall>tx. transactionOrigin S tx \<noteq> Some i"
      and "Si = S\<lparr>localState := localState S(i \<mapsto> initState), currentProc := currentProc S(i \<mapsto> impl), visibleCalls := visibleCalls S(i \<mapsto> {}),
             invocationOp := invocationOp S(i \<mapsto> proc)\<rparr>"
    by auto
  note facts = this 

  show "P Si i"
    apply (rule a2[unfolded LABEL_simps])
    using facts by auto

qed

end

method M_show_programCorrect = 
  ((rule Initial_Label, 
    rule DC_show_programCorrect;
   (rule DC_final2 | rule DC_final)), 
   casify)

method M_show_procedureCorrect = 
  ((rule Initial_Label, 
    rule DC_show_procedureCorrect;
   (rule DC_final2 | rule DC_final)), 
   casify)



\<comment> \<open>ony unfold definitions, when needed for evaluation:\<close>
lemma state_def[simp]:  "S' ::= S \<Longrightarrow> (currentProc S' i \<triangleq> x) \<longleftrightarrow> (currentProc S i \<triangleq> x)"  by (auto simp add: Def_def)
lemma state_def_h1[simp]: "S' ::= S \<Longrightarrow>  ls_pc (the (localState S' i)) = ls_pc (the (localState S i))" by (auto simp add: Def_def)
lemma state_def_h2[simp]: "S' ::= S \<Longrightarrow>  (currentTransaction S' i = None) \<longleftrightarrow> (currentTransaction S i = None)"  by (auto simp add: Def_def)
lemma state_def_currentProc[simp]: "S' ::= S \<Longrightarrow>  currentProc S' i = currentProc S i" by (auto simp add: Def_def)
lemma state_def_currentTransaction[simp]: "S' ::= S \<Longrightarrow> currentTransaction S' i = currentTransaction S i"  by (auto simp add: Def_def)


method show_procedures_cannot_guess_ids = 
  (((auto simp add: newId_def bind_def atomic_def beginAtomic_def call_def skip_def endAtomic_def return_def 
        uniqueIds_mapOp_def  uniqueIds_registerOp_def 
        split: if_splits)[1])?;
    ((rule procedure_cannot_guess_ids.intros, force); show_procedures_cannot_guess_ids?)?)


end