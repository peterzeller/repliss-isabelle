section "Universality of CRDT specifications"

theory crdt_specs_universal
  imports crdt_specs
begin

text \<open>We show that CRDT specs can describe any synchronization-free system.

A syncfree system is one where the result of requests only depends on local states.
For the theorem we also need the assumption that communication is single-step: 
Requests trigger messages, which can be processed asynchronously, but handling these messages cannot 
trigger further messages (that would be kind of synchronous, wouldn't it?).

The proof idea is an inductive argument:

\<^item> In the initial state there can only be one answer to an request.

\<^item> We define happens-before as having an effect on the state / message reached.

\<^item> Since System is deterministic we can recover state recursively going back along happens-before relation.

\<^item> If we know the state, we know the result.


\<close>


locale syncfree_system = 
  fixes node_state :: "'node \<Rightarrow> 'state"
    and perform_op :: "'state \<Rightarrow> 'op \<Rightarrow> 'res \<times> 'message"
begin


end


text \<open>Now for the reverse direction: 

\<^item> We just implement a CRDT that records happens-before and requests and keeps the complete history in the state.

\<^item> Then answering a request is just applying the computable specification.

\<^item> This system trivially implements the spec.

\<close>


end