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



datatype ('a,'operation, 'any) io =
    WaitLocalStep "('a,'operation, 'any) io"
  | WaitBeginAtomic "('a,'operation, 'any) io"
  | WaitEndAtomic "('a,'operation, 'any) io"
  | WaitNewId "'any \<Rightarrow> bool" "'any \<Rightarrow> ('a,'operation, 'any) io"
  | WaitDbOperation 'operation "'any \<Rightarrow> ('a,'operation, 'any) io"
  | WaitReturn "'a" 


function (domintros) bind :: "('a, 'operation, 'any) io \<Rightarrow> ('a \<Rightarrow> ('b, 'operation,'any) io) \<Rightarrow> ('b, 'operation,'any) io"  where
  "bind (WaitLocalStep n) f = (WaitLocalStep (bind n f))"
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

definition pause :: "(unit,'operation,'any) io" where
"pause \<equiv> WaitLocalStep (WaitReturn ())"

definition beginAtomic :: "(unit,'operation,'any) io" where
"beginAtomic \<equiv> WaitBeginAtomic (WaitReturn ())"

definition endAtomic :: "(unit,'operation,'any) io" where
"endAtomic \<equiv> WaitEndAtomic (WaitReturn ())"


definition newId :: "('any \<Rightarrow> bool) \<Rightarrow> ('any,'operation,'any) io" where
"newId P \<equiv> WaitNewId P (\<lambda>i. WaitReturn i)"

definition call :: "'operation \<Rightarrow> ('any,'operation,'any) io" where
"call op \<equiv> WaitDbOperation op (\<lambda>i. WaitReturn i)"

definition return :: "'a  \<Rightarrow> ('a,'operation, 'any) io" where
"return x \<equiv> WaitReturn x"


definition atomic ::"('a,'operation, 'any) io \<Rightarrow> ('a,'operation, 'any) io"  where
"atomic f \<equiv> do {
  beginAtomic;
  r \<leftarrow> f;
  endAtomic;
  return r
}"


definition 
"skip \<equiv> return undefined"

fun toImpl :: "(('val,'operation, 'val) io, 'operation, 'val) procedureImpl" where
"toImpl (WaitLocalStep n) = LocalStep n"
| "toImpl (WaitBeginAtomic n) = BeginAtomic n"
| "toImpl (WaitEndAtomic n) = EndAtomic n"
| "toImpl (WaitNewId P n) = NewId (\<lambda>i. if P i then Some (n i) else None)"
| "toImpl (WaitDbOperation op n) = DbOperation op n"
| "toImpl (WaitReturn v) = Return v"





lemma toImpl_simps[simp]:
"toImpl (newId P) = NewId (\<lambda>i. if P i then Some (return i) else None)"
"toImpl (pause) = LocalStep (return ())"
"toImpl (beginAtomic) = BeginAtomic (return ())"
"toImpl (endAtomic) = EndAtomic (return ())"
"toImpl (call op ) = DbOperation op  (\<lambda>r. return r)"
"toImpl (return x) = Return x"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)


lemma toImpl_bind_simps[simp]:
"\<And>P x. toImpl (newId P \<bind> x) = NewId (\<lambda>i. if P i then Some (x i) else None)"
"\<And> x. toImpl (pause \<bind> x) = LocalStep (x ())"
"\<And> x. toImpl (beginAtomic \<bind> x) = BeginAtomic (x ())"
"\<And> x. toImpl (endAtomic \<bind> x) = EndAtomic (x ())"
"\<And> x. toImpl (call op  \<bind> x) = DbOperation op  (\<lambda>r. x r)"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)



paragraph "Monad Laws"

text "We prove the typical monad laws: identity of return and associativity."

lemma return_left_ident[simp]: 
  fixes x and f :: "'a \<Rightarrow> ('b,'operation, 'any) io"
  shows "return x \<bind> f = f x"
  by (auto simp add: return_def)

lemma right_ident[simp]: 
  fixes m :: "('a,'operation, 'any) io"
  shows "(m \<bind> return) = m"
  by (induct m, auto simp add: return_def)

lemma bind_assoc[simp]: 
  fixes x :: "('a,'operation, 'any) io"
    and y :: "'a \<Rightarrow> ('b,'operation, 'any) io"
    and z :: "'b \<Rightarrow> ('c,'operation, 'any) io"
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