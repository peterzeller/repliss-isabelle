section "Simulation proofs"

theory simulation_proofs
  imports execution_invariants
begin


text "We establish a general rule for doing simulation proofs on the semantics.
The function @{term f} transforms an original trace to the simulation trace.
The predicate @{term P} relates the original trace and state with the simulation trace and state."



lemma trace_simulationProof[consumes 1, case_names initial f_empty_to_empty induct_step[coupling steps1 steps2 step]]:
  assumes steps_tr: "init ~~ tr \<leadsto>* S"
    and P_initial: "P [] [] init init"
    and f_empty_to_empty: "f [] = []"
    and induct_step: "\<And>tr a S1 S2 S1'. \<lbrakk>P tr (f tr) S1 S2; init ~~ tr \<leadsto>* S1; init ~~ f tr \<leadsto>* S2; S1 ~~ a \<leadsto> S1'\<rbrakk> 
      \<Longrightarrow> \<exists>S2'. (init ~~ f (tr@[a]) \<leadsto>* S2') \<and> P (tr@[a]) (f (tr@[a])) S1' S2'"
  shows "\<exists>S'. (init ~~ f tr \<leadsto>* S') \<and>  P tr (f tr) S S'"
  using steps_tr proof (induct rule: steps_induct)
  case initial
  show ?case
    using P_initial steps_refl by (auto simp add: f_empty_to_empty  )

next
  case (step S' tr a S'')
  from this
  obtain S1' 
    where S1'_step: "init ~~ f tr \<leadsto>* S1'" 
      and S1'_P: "P tr (f tr) S' S1'"
    by blast

  from induct_step[OF S1'_P \<open>init ~~ tr \<leadsto>* S'\<close> S1'_step \<open> S' ~~ a \<leadsto> S''\<close>]  
  obtain S2' 
    where S2'_steps: "init ~~ f (tr @ [a]) \<leadsto>* S2'"
      and S2'_P: "P (tr @ [a]) (f (tr @ [a])) S'' S2'"
    by blast

  then show " \<exists>S'. (init ~~ f (tr @ [a]) \<leadsto>* S') \<and> P (tr @ [a]) (f (tr @ [a])) S'' S'"
    by blast
qed



end