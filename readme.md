# Build

Install [Isabelle 2017](https://isabelle.in.tum.de/), then run:

	isabelle build -D .

or:

	isabelle build -D . -j 4 -o quick_and_dirty

# Structure

The following theory files are included:

 - `prefix`: Lemmas about prefixes of lists.
 - `repliss_sem`: This theory describes the distributed semantics used by Repliss.
 - `execution_invariants`: This theory includes proof for invariants that hold for all executions.
 - `commutativity`: This theory proves commutativity between certain actions in executions.
 - `repliss_sem_single_invocation`: This theory describes the single-invocation semantics used for our proof approach.
 - `execution_invariants_s`: This theory includes proof for invariants that hold for all single-invocation executions.
 - `approach`: This theory includes the soundness proof of our proof approach.
 - `single_invocation_correctness`: This theory includes techniques to prove that a program is correct in the single-invocation semantics.
 - `invariant_simps`: This theory includes helpers for working with invariants.


The lemmas and theorems from the paper can be found under the following names in the theories:

- Lemma 5.1: `show_programCorrect_noTransactionInterleaving` in `commutativity`
- Lemma 5.2: `convert_to_single_session_trace_invFail` in `approach`
- Lemma 5.3: `show_correctness_via_single_session` in `approach`

