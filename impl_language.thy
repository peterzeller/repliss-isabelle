theory impl_language
  imports Main 
    "~~/src/HOL/Library/Monad_Syntax"
"~~/src/HOL/Library/State_Monad"
  repliss_sem
begin

context begin

(*
datatype iostate =
    WaitInput
    | WaitOutput int
    | Idle
*)

(* let's build an io monad as an example*)
datatype 'a io = 
    WaitInput (onInput: "int \<Rightarrow> 'a io") 
  | WaitOutput int (onOutput: "'a io") 
  | Done 'a

definition io_write :: "int \<Rightarrow> unit io" where
"io_write i = WaitOutput i (Done ()) "

definition io_read :: "int io" where
"io_read = WaitInput (\<lambda>i. (Done i))"

function (domintros) bind :: "'a io \<Rightarrow> ('a \<Rightarrow> 'b io) \<Rightarrow> 'b io"  where
"bind (WaitInput oi) f = (WaitInput (\<lambda>i. bind (oi i) f)) "
| "bind (WaitOutput i n) f = (WaitOutput i (bind n f)) "
| "bind (Done v) f = (f v)"

  by (pat_completeness, auto)
termination
proof auto
  fix io :: "'a io" and f :: "'a \<Rightarrow> 'b io"
  show "bind_dom (io, f)"
  proof (induct io)
    case (WaitInput x)
    then show ?case
      by (simp add: bind.domintros(1)) 
  next
    case (WaitOutput x1a io)
    then show ?case
      using bind.domintros(2) by blast 
  next
    case (Done x)
    then show ?case
      by (simp add: bind.domintros(3))
  qed
qed

adhoc_overloading Monad_Syntax.bind bind

definition proc :: "int io" where
 "proc \<equiv>  do {
  x \<leftarrow> io_read;
  y \<leftarrow> io_read;
  io_write (x+y);
  Done (x*y)
}"

datatype action = In int | Out int

inductive step :: "'a io \<Rightarrow> action list \<Rightarrow> 'a \<Rightarrow> bool" where
step_done: "step (Done x) [] x"
| step_in: "step (f x) tr y \<Longrightarrow>  step (WaitInput f) (In x#tr) y"
| step_out: "step n tr y \<Longrightarrow>  step (WaitOutput x n) (Out x#tr) y"

lemma "step proc [In 3, In 4, Out 7] 12"
  find_theorems name: "impl_language.bind"
  by (auto simp add: proc_def  io_read_def io_write_def intro!: step_in step_out step_done)

fun single_step:: "'a io \<Rightarrow> (bool \<times> 'a io) option" where
"single_step (WaitInput f) = Some (True, f 0)"
| "single_step (WaitOutput i n) = Some (False, n)"
| "single_step (Done i) = None"

lemma "single_step proc = Some (True, WaitInput (\<lambda>i. WaitOutput i (Done 0)))"
  by (auto simp add: proc_def  io_read_def io_write_def bind.psimps bind.domintros)



definition proc2 :: "int list io" where
 "proc2 \<equiv>  do {
  x \<leftarrow> io_read;
  y \<leftarrow> io_read;
  io_write (x+y);
  Done [x,y]
}"


(* example *)


(*type_synonym ('localState, 'any) procedureImpl = "'localState \<Rightarrow> ('localState, 'any) localAction"*)


(* lets *)

typ "('a,'b) localAction"




(* symbolic values *)
datatype sval = SVal nat 

datatype sym_localAction =
    SymLocalStep
  | SymBeginAtomic
  | SymEndAtomic
  | SymNewId 
  | SymDbOperation operation "sval list"
  | SymReturn sval

type_synonym ('a,'s) step = "'s \<Rightarrow> (sym_localAction \<times> 'a \<times> 's)"

fun bind :: "('a,'s) step \<Rightarrow> ('a \<Rightarrow> ('b,'s) step) \<Rightarrow> ('b,'s) step"  where
"bind s f = (\<lambda>x. let (a,r,s') = s x in f r s')"

definition "s_newid" :: "('a, 's) step" where
"s_newid \<equiv> "

(* symbolic state *)
datatype 'a sym_state = 
  SymState 'a "nat" "sym_localAction list"


fun bind :: "'a sym_state \<Rightarrow> ('a \<Rightarrow> 'b sym_state) \<Rightarrow> 'b sym_state"  where
"bind (x i as) = "

datatype cmd = 
    Call "int"
  | Seq "cmd" "cmd"
  | Return int
  | Skip

datatype 'any lstate = LState (ls_val:"'any") (ls_cmd:"cmd")


definition bind :: "'a lstate \<Rightarrow> ('a \<Rightarrow> 'b lstate) \<Rightarrow> 'b lstate"  where
"bind s f \<equiv> let s' = f (ls_val s) in LState (ls_val s') (Seq (ls_cmd s) (ls_cmd s'))"

adhoc_overloading Monad_Syntax.bind bind

definition call :: "int \<Rightarrow> int lstate" where
 "call c \<equiv> LState (2*c) (Call c)"

definition "return x \<equiv> LState x Skip"

definition "test1 \<equiv> bind (call 2) (return)"

definition proc :: "int lstate" where
 "proc \<equiv>  do {
  x \<leftarrow> call 1;
  y \<leftarrow> call (x+1);
  return y
}"

lemma "proc = ???"
  thm proc_def
  apply (auto simp add: proc_def)
  apply (auto simp add: bind_def Let_def call_def return_def)

lemma "run test 0 = ???"
  apply (auto simp add: test_def run_def op_a_def op_b_def bind_def return_def split: ) 
  oops

definition run :: "'any blub \<Rightarrow>  ('localState, 'any) procedureImpl"
  where "run \<equiv> ???"

end


end