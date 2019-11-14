theory impl_language
  imports Main 
    "~~/src/HOL/Library/Monad_Syntax"
"~~/src/HOL/Library/State_Monad"
  repliss_sem
begin

context begin

(*
datatype ('localState, 'any) localAction =
  LocalStep 'localState
  | BeginAtomic 'localState
  | EndAtomic 'localState
  | NewId "'any \<rightharpoonup> 'localState"
  | DbOperation operation "'any list" "'any \<Rightarrow> 'localState"
  | Return 'any
*)


datatype ('a,'any) io =
    WaitLocalStep "('a,'any) io"
  | WaitBeginAtomic "('a,'any) io"
  | WaitEndAtomic "('a,'any) io"
  | WaitNewId "'any \<Rightarrow> bool" "'any \<Rightarrow> ('a,'any) io"
  | WaitDbOperation operation "'any list" "'any \<Rightarrow> ('a,'any) io"
  | WaitReturn "'a" 
  | Fail string


function (domintros) bind :: "('a,'any) io \<Rightarrow> ('a \<Rightarrow> ('b,'any) io) \<Rightarrow> ('b,'any) io"  where
  "bind (WaitLocalStep n) f = (WaitLocalStep (bind n f))"
| "bind (WaitBeginAtomic n) f = (WaitBeginAtomic (bind n f))"
| "bind (WaitEndAtomic n) f = (WaitEndAtomic (bind n f))"
| "bind (WaitNewId P n) f = (WaitNewId P (\<lambda>i.  bind (n i) f))"
| "bind (WaitDbOperation op args n) f = (WaitDbOperation op args (\<lambda>i.  bind (n i) f))"
| "bind (WaitReturn s) f = (f s)"
| "bind (Fail s) f = (Fail s)"

  by (pat_completeness, auto)
termination
  using [[show_sorts]]
proof auto
  fix a :: "('a,'any) io"  and b :: "'a \<Rightarrow> ('c, 'any) io"
  show "bind_dom (a, b)"
    by (induct a, auto simp add: bind.domintros)
qed

adhoc_overloading Monad_Syntax.bind bind

definition pause :: "(unit,'any) io" where
"pause \<equiv> WaitLocalStep (WaitReturn ())"

definition beginAtomic :: "(unit,'any) io" where
"beginAtomic \<equiv> WaitBeginAtomic (WaitReturn ())"

definition endAtomic :: "(unit,'any) io" where
"endAtomic \<equiv> WaitEndAtomic (WaitReturn ())"

definition newId :: "('any \<Rightarrow> bool) \<Rightarrow> ('any,'any) io" where
"newId P \<equiv> WaitNewId P (\<lambda>i. WaitReturn i)"

definition call :: "operation \<Rightarrow> 'any list  \<Rightarrow> ('any,'any) io" where
"call op args \<equiv> WaitDbOperation op args (\<lambda>i. WaitReturn i)"

definition return :: "'a  \<Rightarrow> ('a,'any) io" where
"return x \<equiv> WaitReturn x"


definition 
"skip \<equiv> return undefined"

fun toImpl :: "(('val, 'val) io, 'val) procedureImpl" where
"toImpl (WaitLocalStep n) = LocalStep n"
| "toImpl (WaitBeginAtomic n) = BeginAtomic n"
| "toImpl (WaitEndAtomic n) = EndAtomic n"
| "toImpl (WaitNewId P n) = NewId (\<lambda>i. if P i then Some (n i) else None)"
| "toImpl (WaitDbOperation op args n) = DbOperation op args n"
| "toImpl (WaitReturn v) = Return v"
| "toImpl (Fail s) = ???"


lemma return_bind[simp]: "return x \<bind> f = f x"
  by (auto simp add: return_def)


lemma toImpl_simps[simp]:
"toImpl (newId P) = NewId (\<lambda>i. if P i then Some (return i) else None)"
"toImpl (pause) = LocalStep (return ())"
"toImpl (beginAtomic) = BeginAtomic (return ())"
"toImpl (endAtomic) = EndAtomic (return ())"
"toImpl (call op args) = DbOperation op args (\<lambda>r. return r)"
"toImpl (return x) = Return x"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)



lemma toImpl_bind_simps[simp]:
"\<And>P x. toImpl (newId P \<bind> x) = NewId (\<lambda>i. if P i then Some (x i) else None)"
"\<And> x. toImpl (pause \<bind> x) = LocalStep (x ())"
"\<And> x. toImpl (beginAtomic \<bind> x) = BeginAtomic (x ())"
"\<And> x. toImpl (endAtomic \<bind> x) = EndAtomic (x ())"
"\<And> x. toImpl (call op args \<bind> x) = DbOperation op args (\<lambda>r. x r)"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)



end


end