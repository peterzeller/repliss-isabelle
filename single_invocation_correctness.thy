theory single_invocation_correctness
imports approach
begin

text {*
  Start with initial state,
  
  then steps
  
  finally return and last check
  
  somehow automated

*}


definition initialStates :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state set"  where
"initialStates progr \<equiv> {S | S S' procName args initState impl i.
  procedure progr procName args \<triangleq> (initState, impl)  
  \<and> uniqueIdsInList args \<subseteq> knownIds S
  \<and> invariant_all S
  \<and> invocationOp S i = None
  \<and> S' = (S\<lparr>localState := (localState S)(i \<mapsto> initState),
                 currentProc := (currentProc S)(i \<mapsto> impl),
                 visibleCalls := (visibleCalls S)(i \<mapsto> {}),
                 invocationOp := (invocationOp S)(i \<mapsto> (procName, args))\<rparr>)
}"

(* check program (with a given start-state, bound by a number of steps) *)
fun checkCorrect :: "('localState, 'any) prog \<Rightarrow> ('localState, 'any) state \<Rightarrow> invocation \<Rightarrow> nat \<Rightarrow> bool" where
"checkCorrect progr S i 0 = False"
| "checkCorrect progr S i (Suc bound) =
(case currentProc S i of
    None \<Rightarrow> True
  | Some impl \<Rightarrow>
      (case impl (the (localState S i)) of
          LocalStep ls \<Rightarrow> 
            checkCorrect progr (S\<lparr>localState := (localState S)(i \<mapsto> ls)\<rparr>) i bound
        | BeginAtomic ls \<Rightarrow> 
            currentTransaction S i = None
            \<and> (\<forall>t S'.
                transactionStatus S t = None
              \<and> invariant_all S'
              \<and> state_wellFormed S'
              \<and> state_monotonicGrowth S S'
              \<and> localState S' i \<triangleq> ls
              \<and> currentTransaction S' i \<triangleq> t
              \<and> transactionStatus S' t \<triangleq> Uncommited
              \<and> transactionOrigin S' t \<triangleq> i
              \<longrightarrow> checkCorrect progr S' i bound)
        | EndAtomic ls \<Rightarrow> 
            (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                let S' = (S\<lparr>
                  localState := (localState S)(i \<mapsto> ls), 
                  currentTransaction := (currentTransaction S)(i := None),
                  transactionStatus := (transactionStatus S)(t \<mapsto> Commited) \<rparr>) in
                invariant_all S'
                \<and> checkCorrect progr S' i bound
            )
        | NewId ls \<Rightarrow> 
          (\<forall>uid.
            uid \<notin> generatedIds S
            \<longrightarrow> checkCorrect progr (S\<lparr>localState := (localState S)(i \<mapsto> ls uid), generatedIds := generatedIds S \<union> {uid} \<rparr>) i bound
          )
        | DbOperation Op args ls \<Rightarrow> 
           (case currentTransaction S i of
                None \<Rightarrow> False
              | Some t \<Rightarrow>
                  (\<exists>res. querySpec progr Op args (getContext S i) res)
                  \<and>
                  (\<forall>c res vis. 
                      calls S c = None
                    \<and> querySpec progr Op args (getContext S i) res
                    \<and> visibleCalls S i \<triangleq> vis
                    \<longrightarrow> checkCorrect progr (S\<lparr>
                          localState := (localState S)(i \<mapsto> ls res), 
                          calls := (calls S)(c \<mapsto> Call Op args res ),
                          callOrigin := (callOrigin S)(c \<mapsto> t),
                          visibleCalls := (visibleCalls S)(i \<mapsto> vis \<union> {c}),
                          happensBefore := happensBefore S \<union> vis \<times> {c}  \<rparr>) i bound
                  )
           )
        | Return res \<Rightarrow> 
            currentTransaction S i = None
            \<and> (let S' = (S\<lparr>
                 localState := (localState S)(i := None),
                 currentProc := (currentProc S)(i := None),
                 visibleCalls := (visibleCalls S)(i := None),
                 invocationRes := (invocationRes S)(i \<mapsto> res),
                 knownIds := knownIds S \<union> uniqueIds res\<rparr>) in
               invariant_all S'    
            )
        ))
"

lemma show_program_correct_single_invocation:
assumes initialCorrect: "\<And>S. S\<in>initialStates program \<Longrightarrow> invariant_all S "
    and check: "\<And>S i. S\<in>initialStates program \<Longrightarrow> checkCorrect program S i bound"
shows "programCorrect_s program"
proof (auto simp add: programCorrect_s_def)
  fix trace i S_fin
  assume "initialState program ~~ (i, trace) \<leadsto>\<^sub>S* S_fin"
  
  show "traceCorrect_s program trace"




end