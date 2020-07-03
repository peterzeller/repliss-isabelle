section "Implementation Language"
theory impl_language
  imports Main 
    "HOL-Library.Monad_Syntax"
  repliss_sem
begin


text "So far, we have assumed that procedure implementations are given by arbitrary state machines.
Here we define an implementation language using a shallow embedding with the monad syntax package.
"

context begin



datatype ('a,'op, 'any) io =
    WaitLocalStep bool "('a,'op, 'any) io"
  | WaitBeginAtomic "('a,'op, 'any) io"
  | WaitEndAtomic "('a,'op, 'any) io"
  | WaitNewId "'any \<Rightarrow> bool" "'any \<Rightarrow> ('a,'op, 'any) io"
  | WaitDbOperation 'op "'any \<Rightarrow> ('a,'op, 'any) io"
  | WaitReturn "'a" 


function (domintros) bind :: "('a, 'op, 'any) io \<Rightarrow> ('a \<Rightarrow> ('b, 'op,'any) io) \<Rightarrow> ('b, 'op,'any) io"  where
  "bind (WaitLocalStep ok n) f = (WaitLocalStep ok (bind n f))"
| "bind (WaitBeginAtomic n) f = (WaitBeginAtomic (bind n f))"
| "bind (WaitEndAtomic n) f = (WaitEndAtomic (bind n f))"
| "bind (WaitNewId P n) f = (WaitNewId P (\<lambda>i.  bind (n i) f))"
| "bind (WaitDbOperation op n) f = (WaitDbOperation op (\<lambda>i.  bind (n i) f))"
| "bind (WaitReturn s) f = (f s)"

  by (pat_completeness, auto)
termination
  using [[show_sorts]]
proof auto
  show "bind_dom (a, b)" for a b
    by (induct a, auto simp add: bind.domintros)
qed

adhoc_overloading Monad_Syntax.bind bind

definition pause :: "(unit,'op,'any) io" where
"pause \<equiv> WaitLocalStep True (WaitReturn ())"

definition beginAtomic :: "(unit,'op,'any) io" where
"beginAtomic \<equiv> WaitBeginAtomic (WaitReturn ())"

definition endAtomic :: "(unit,'op,'any) io" where
"endAtomic \<equiv> WaitEndAtomic (WaitReturn ())"


definition newId :: "('any \<Rightarrow> bool) \<Rightarrow> ('any,'op,'any) io" where
"newId P \<equiv> WaitNewId P (\<lambda>i. WaitReturn i)"

definition call :: "'op \<Rightarrow> ('any,'op,'any) io" where
"call op \<equiv> WaitDbOperation op (\<lambda>i. WaitReturn i)"

definition return :: "'a  \<Rightarrow> ('a,'op, 'any) io" where
"return x \<equiv> WaitReturn x"


definition atomic ::"('a,'op, 'any) io \<Rightarrow> ('a,'op, 'any) io"  where
"atomic f \<equiv> do {
  beginAtomic;
  r \<leftarrow> f;
  endAtomic;
  return r
}"


definition 
"skip \<equiv> return undefined"

fun toImpl :: "(('val,'op, 'val) io, 'op, 'val) procedureImpl" where
"toImpl (WaitLocalStep ok n) = LocalStep ok n"
| "toImpl (WaitBeginAtomic n) = BeginAtomic n"
| "toImpl (WaitEndAtomic n) = EndAtomic n"
| "toImpl (WaitNewId P n) = NewId (\<lambda>i. if P i then Some (n i) else None)"
| "toImpl (WaitDbOperation op n) = DbOperation op n"
| "toImpl (WaitReturn v) = Return v"





lemma toImpl_simps[simp]:
"toImpl (newId P) = NewId (\<lambda>i. if P i then Some (return i) else None)"
"toImpl (pause) = LocalStep True (return ())"
"toImpl (beginAtomic) = BeginAtomic (return ())"
"toImpl (endAtomic) = EndAtomic (return ())"
"toImpl (call op ) = DbOperation op  (\<lambda>r. return r)"
"toImpl (return x) = Return x"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)


lemma toImpl_bind_simps[simp]:
"\<And>P x. toImpl (newId P \<bind> x) = NewId (\<lambda>i. if P i then Some (x i) else None)"
"\<And> x. toImpl (pause \<bind> x) = LocalStep True (x ())"
"\<And> x. toImpl (beginAtomic \<bind> x) = BeginAtomic (x ())"
"\<And> x. toImpl (endAtomic \<bind> x) = EndAtomic (x ())"
"\<And> x. toImpl (call op  \<bind> x) = DbOperation op  (\<lambda>r. x r)"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)



paragraph "Monad Laws"

text "We prove the typical monad laws: identity of return and associativity."

lemma return_left_ident[simp]: 
  fixes x and f :: "'a \<Rightarrow> ('b,'op, 'any) io"
  shows "return x \<bind> f = f x"
  by (auto simp add: return_def)

lemma right_ident[simp]: 
  fixes m :: "('a,'op, 'any) io"
  shows "(m \<bind> return) = m"
  by (induct m, auto simp add: return_def)

lemma bind_assoc[simp]: 
  fixes x :: "('a,'op, 'any) io"
    and y :: "'a \<Rightarrow> ('b,'op, 'any) io"
    and z :: "'b \<Rightarrow> ('c,'op, 'any) io"
  shows "((x \<bind> y) \<bind> z) = (x \<bind> (\<lambda>a. y a \<bind> z))"
  by (induct x, auto)




lemma atomic_simp1[simp]: 
"toImpl (atomic f) = BeginAtomic (f \<bind> (\<lambda>r. endAtomic \<bind> (\<lambda>_. return r)))"
  by (auto simp add: atomic_def bind_assoc)

lemma atomic_simp2[simp]: 
"toImpl (atomic f \<bind> x) = BeginAtomic (f \<bind> (\<lambda>a. endAtomic \<bind> (\<lambda>b. x a)))"
  by (auto simp add: atomic_def bind_assoc)



end


end
