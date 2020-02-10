section "Implementation Language with Loops"
theory impl_language_loops
  imports Main 
    "HOL-Library.Monad_Syntax"
  repliss_sem
"ZFC_in_HOL.ZFC_Typeclasses"
begin

text "We need to hide some ZFC constants so that the normal ones are still visible:"

hide_const (open) "ZFC_in_HOL.set"



text "So far, we have assumed that procedure implementations are given by arbitrary state machines.
Here we define an implementation language using a shallow embedding with the monad syntax package.
"

type_synonym iref = nat
datatype 'a ref = Ref (iref:iref)
type_synonym 'v store = "iref \<rightharpoonup> 'v"

instantiation ref :: (type) small begin
instance proof
  obtain V_of :: "nat \<Rightarrow> V" and A :: "V" where "inj V_of" and "range V_of \<subseteq> elts A"
    using small by blast


  show "\<exists>(V_of::'a ref \<Rightarrow> V) A. inj V_of \<and> range V_of \<subseteq> elts A"
  proof (intro conjI exI)
    show "inj (V_of \<circ> iref)"
      by (metis (mono_tags, lifting) \<open>inj V_of\<close> comp_apply injD inj_on_def ref.expand)

    show " range (V_of \<circ> iref) \<subseteq> elts A"
      using \<open>range V_of \<subseteq> elts A\<close> by auto
  qed
qed
end


class natConvert =
  fixes fromNat :: "nat \<Rightarrow> 'a"
  assumes fromNat_inj: "inj fromNat"

definition "toNat \<equiv> the_inv fromNat"

lemma "toNat (fromNat x) = x"
  by (simp add: fromNat_inj the_inv_f_f toNat_def)

instantiation ref :: (type) natConvert begin
definition [simp]: "fromNat_ref = Ref"
instance 
  apply standard
  using injI by fastforce
end




datatype ('a,'operation, 'any) io =
    WaitLocalStep "'any store \<Rightarrow> bool \<times> 'any store \<times> ('a,'operation, 'any) io"
  | WaitBeginAtomic "('a,'operation, 'any) io"
  | WaitEndAtomic "('a,'operation, 'any) io"
  | WaitNewId "'any \<Rightarrow> bool" "'any \<Rightarrow> ('a,'operation, 'any) io"
  | WaitDbOperation 'operation "'any \<Rightarrow> ('a,'operation, 'any) io"
  | WaitReturn "'a" 
  | Loop "V" "('a,'operation, 'any) io" \<comment> \<open>body is an (bool, 'operation, 'any) io encoded a type V. 
                                            Had to use dynamic typing here as Isabelle has no GADTs. \<close>


text "Actually show that we can embedd io into ZFCs V type:"

definition to_V :: "'a::embeddable \<Rightarrow> V" where
"to_V \<equiv> SOME f. inj f"

definition from_V :: "V \<Rightarrow> 'a::embeddable" where
"from_V \<equiv> the_inv to_V"


lemma to_V_inj: "inj to_V"
  unfolding to_V_def proof -

  show "inj (SOME f::'a::embeddable \<Rightarrow> V. inj f)"
    by (rule someI_ex[where P=inj], rule ex_inj)
qed

lemma to_V_use_inj: "to_V x = to_V y \<Longrightarrow> x = y"
  by (meson injD to_V_inj)


lemma from_V_rev: 
"from_V (to_V x) = x"
  by (simp add: from_V_def the_inv_f_f to_V_inj)




function (domintros) io_to_V :: "('a::small,'operation::small, 'any::small) io \<Rightarrow> V" where
  "io_to_V (WaitLocalStep n)  = to_V (0::nat, to_V (\<lambda>s. let (a,b,c) = n s in to_V (a, b, io_to_V c)))"
| "io_to_V (WaitBeginAtomic n)  =  to_V (1::nat, io_to_V n)"
| "io_to_V (WaitEndAtomic n)  = to_V (2::nat, io_to_V n) "
| "io_to_V (WaitNewId P n)  =  to_V (3::nat, to_V (P, (\<lambda>x. io_to_V (n x))))"
| "io_to_V (WaitDbOperation op n)  =  to_V (4::nat, to_V (op, (\<lambda>x. io_to_V (n x))))"
| "io_to_V (WaitReturn s)  =  to_V (5::nat, to_V s)"
| "io_to_V (Loop body n)  =  to_V (6::nat, to_V (body, io_to_V n))"
  by (pat_completeness, auto)
termination
proof auto
  show "io_to_V_dom x" for x
    apply (induct x, auto simp add: io_to_V.domintros)
    by (metis io_to_V.domintros(1) range_eqI)
qed

lemma fun_cong2: "f = g \<Longrightarrow> \<forall>x. f x = g x"
  by simp



lemma io_to_V_inj: "inj io_to_V"
proof
  fix x y :: "('a::small,'operation::small, 'any::small) io"
  assume a0: "x \<in> UNIV"
    and a1: "y \<in> UNIV"
    and a2: "io_to_V x = io_to_V y"

  from `io_to_V x = io_to_V y`
  show "x = y"
  proof (induct x arbitrary: y)
    case (WaitLocalStep a y)
    show ?case
    proof (cases y)
      fix c
      assume " y = WaitLocalStep c"
      hence h: "io_to_V (WaitLocalStep a) = io_to_V (WaitLocalStep c)"
        using WaitLocalStep.prems by blast
      from h have eq1: "fst (a x) = fst (c x)" for x
        by (auto dest!: to_V_use_inj fun_cong[where x=x] split: prod.splits)
      from h have eq2: "fst (snd (a x)) = fst (snd (c x))" for x
        by (auto dest!: to_V_use_inj fun_cong[where x=x] split: prod.splits)

      from h have "io_to_V (snd (snd (a x))) = io_to_V (snd (snd (c x)))" for x
        by (auto dest!: to_V_use_inj fun_cong[where x=x] split: prod.splits)
      have eq3: "snd (snd (a x)) = snd (snd (c x))" for x

      proof (rule WaitLocalStep)
        show "io_to_V (snd (snd (a x))) = io_to_V (snd (snd (c x)))"
          using `io_to_V (snd (snd (a x))) = io_to_V (snd (snd (c x)))` .

        show "snd (snd (a x)) \<in> Basic_BNFs.snds (snd (a x))"
          by (simp add: snds.simps)

        show "snd (a x) \<in> Basic_BNFs.snds (a x)"
          by (simp add: snds.intros)

        show " a x \<in> range a"
          by blast
      qed

      have "a = c"
        by (auto simp add: prod_eq_iff eq1 eq2 eq3)

      thus " WaitLocalStep a = y"
        using `y = WaitLocalStep c` by simp
    next
    qed (insert `io_to_V (WaitLocalStep a) = io_to_V y`, auto dest!: to_V_use_inj)
  next
    case (WaitBeginAtomic a)
     thus ?case by (cases y, auto dest!: to_V_use_inj)
  next
    case (WaitEndAtomic a)
    thus ?case by (cases y, auto dest!: to_V_use_inj)
  next
    case (WaitNewId a b)
    thus ?case 
      by (cases y, auto dest!: to_V_use_inj, meson HOL.ext rangeI)
  next
    case (WaitDbOperation a b)
     thus ?case by (cases y, auto dest!: to_V_use_inj, meson HOL.ext rangeI)
  next
    case (WaitReturn r)
     thus ?case by (cases y, auto dest!: to_V_use_inj)
  next
    case (Loop a b)
     thus ?case by (cases y, auto dest!: to_V_use_inj)
  qed
qed



instance io :: (small, small, small) embeddable
  by (standard, force intro: io_to_V_inj)


function (domintros) bind :: "('a, 'operation, 'any) io \<Rightarrow> ('a \<Rightarrow> ('b, 'operation,'any) io) \<Rightarrow> ('b, 'operation,'any) io" (infixl "\<bind>io" 54)  where
  "bind (WaitLocalStep n) f = (WaitLocalStep (\<lambda>s. let (a,b,c) = n s in (a, b, bind c f)))"
| "bind (WaitBeginAtomic n) f = (WaitBeginAtomic (bind n f))"
| "bind (WaitEndAtomic n) f = (WaitEndAtomic (bind n f))"
| "bind (WaitNewId P n) f = (WaitNewId P (\<lambda>i.  bind (n i) f))"
| "bind (WaitDbOperation op n) f = (WaitDbOperation op (\<lambda>i.  bind (n i) f))"
| "bind (WaitReturn s) f = (f s)"
| "bind (Loop body n) f = (Loop body (bind n f))"
  by (pat_completeness, auto)
termination
  using [[show_sorts]]
proof auto
  show "bind_dom (i, f)" for i :: "('a, 'operation, 'any) io" and f :: "'a \<Rightarrow> ('d, 'operation, 'any) io"
    apply (induct i, auto simp add: bind.domintros)
    by (metis bind.domintros(1) range_eqI)
qed






fun toImpl :: "(('val store \<times> (('val,'operation::small, 'val::small) io)), 'operation, 'val) procedureImpl" where
  "toImpl (store, WaitLocalStep n) = (let (ok, store', n') = n store in LocalStep (ok \<and> (finite (dom store) \<longrightarrow> finite (dom (store')))) (store', n'))"
| "toImpl (store, WaitBeginAtomic n) = BeginAtomic (store, n)"
| "toImpl (store, WaitEndAtomic n) = EndAtomic (store, n)"
| "toImpl (store, WaitNewId P n) = NewId (\<lambda>i. if P i then Some (store, n i) else None)"
| "toImpl (store, WaitDbOperation op n) = DbOperation op (\<lambda>r. (store, n r))"
| "toImpl (store, WaitReturn v) = Return v"
| "toImpl (store, Loop body n) = LocalStep True (store, bind (from_V body) (\<lambda>r. if r then n else Loop body n))"



adhoc_overloading Monad_Syntax.bind bind

definition pause :: "(unit,'operation,'any) io" where
"pause \<equiv> WaitLocalStep (\<lambda>s. (True, s, WaitReturn ()))"

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

text "Next, we define some operations to work with references: 
We simply encode references using natural numbers."

definition "fromAny x \<equiv> from_nat (toNat x)"
definition "intoAny x \<equiv> fromNat (to_nat x)"

definition makeRef :: "'a::countable \<Rightarrow> ('a ref, 'operation, 'any::natConvert) io" where
"makeRef v \<equiv> WaitLocalStep (\<lambda>s. let r = LEAST i. s i = None in (True, s(r \<mapsto> intoAny v), WaitReturn (Ref r)))"

definition read :: "'a ref \<Rightarrow> ('a::countable, 'operation, 'any::natConvert) io" where
"read ref \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
      Some v \<Rightarrow> (True, s, WaitReturn (fromAny v)) 
    | None  \<Rightarrow> (False, s, WaitReturn (from_nat 0)))"

definition assign :: "('a::countable) ref \<Rightarrow> 'a \<Rightarrow> (unit, 'operation, 'any::natConvert) io" (infix "::=" 60) where
"assign ref v \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
    Some _ \<Rightarrow> (True, s((iref ref) \<mapsto> intoAny v), WaitReturn ()) 
  | None  \<Rightarrow> (False, s, WaitReturn ())) "

definition update :: "('a::countable) ref \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (unit, 'operation, 'any::natConvert) io" where
"update ref upd \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
      Some v \<Rightarrow> (True, s((iref ref) \<mapsto> intoAny (upd (fromAny v))), WaitReturn ()) 
    | None  \<Rightarrow> (False, s, WaitReturn ())) "




lemma toImpl_simps[simp]:
"\<And>store. toImpl (store, newId P) = NewId (\<lambda>i. if P i then Some (store, return i) else None)"
"\<And>store. toImpl (store, pause) = LocalStep True (store, return ())"
"\<And>store. toImpl (store, beginAtomic) = BeginAtomic (store, return ())"
"\<And>store. toImpl (store, endAtomic) = EndAtomic (store, return ())"
"\<And>store. toImpl (store, call op ) = DbOperation op  (\<lambda>r. (store, return r))"
"\<And>store. toImpl (store, return x) = Return x"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)

schematic_goal "toImpl (store, newId P \<bind> x) = ?x"
 by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)


lemma toImpl_bind_simps[simp]:
"\<And>store P x. toImpl (store, newId P \<bind> x) = NewId (\<lambda>i. if P i then Some (store, x i) else None)"
"\<And>store x. toImpl (store, pause \<bind> x) = LocalStep True (store, x ())"
"\<And>store x. toImpl (store, beginAtomic \<bind> x) = BeginAtomic (store, x ())"
"\<And>store x. toImpl (store, endAtomic \<bind> x) = EndAtomic (store, x ())"
"\<And>store x. toImpl (store, call op  \<bind> x) = DbOperation op  (\<lambda>r. (store, x r))"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)



paragraph "Monad Laws"

text "We prove the typical monad laws: identity of return and associativity."

declare Basic_BNFs.snds.simps[simp]
declare Basic_BNFs.fsts.simps[simp]


lemma return_left_ident[simp]: 
  fixes x and f :: "'a \<Rightarrow> ('b,'operation, 'any) io"
  shows "return x \<bind> f = f x"
  by (auto simp add: return_def)

lemma right_ident[simp]: 
  fixes m :: "('a,'operation, 'any) io"
  shows "(m \<bind> return) = m"
proof (induct m)
  case (WaitLocalStep x)
  then show ?case 
    by (auto simp add: return_def intro!: HOL.ext   split: prod.splits, metis range_eqI)
next
  case (WaitBeginAtomic m)
  then show ?case  by (auto simp add: return_def)
next
  case (WaitEndAtomic m)
  then show ?case  by (auto simp add: return_def)
next
  case (WaitNewId x1a x2a)
  then show ?case  by (auto simp add: return_def)
next
  case (WaitDbOperation x1a x2a)
  then show ?case  by (auto simp add: return_def)
next
  case (WaitReturn x)
  then show ?case  by (auto simp add: return_def)
next
  case (Loop x1a m)
  then show ?case  by (auto simp add: return_def)
qed


lemma bind_assoc[simp]: 
  fixes x :: "('a,'operation, 'any) io"
    and y :: "'a \<Rightarrow> ('b,'operation, 'any) io"
    and z :: "'b \<Rightarrow> ('c,'operation, 'any) io"
  shows "((x \<bind> y) \<bind> z) = (x \<bind> (\<lambda>a. y a \<bind> z))"
proof (induct x)
  case (WaitLocalStep x)
  then show ?case 
    by (auto simp add: return_def intro!: HOL.ext   split: prod.splits, metis rangeI)
next
  case (WaitBeginAtomic x)
  then show ?case  by auto
next
  case (WaitEndAtomic x)
  then show ?case  by auto
next
  case (WaitNewId x1a x2a)
  then show ?case  by auto
next
  case (WaitDbOperation x1a x2a)
  then show ?case  by auto
next
  case (WaitReturn x)
  then show ?case  by auto
next
  case (Loop x1a x)
  then show ?case  by auto
qed



lemma atomic_simp1[simp]: 
"toImpl (s, atomic f) = BeginAtomic (s, f \<bind> (\<lambda>r. endAtomic \<bind> (\<lambda>_. return r)))"
  by (auto simp add: atomic_def)

lemma atomic_simp2[simp]: 
"toImpl (s, atomic f \<bind> x) = BeginAtomic (s, f \<bind> (\<lambda>a. endAtomic \<bind> (\<lambda>b. x a)))"
  by (auto simp add: atomic_def)


subsection "Syntactic sugar for loops"

definition loop :: "(bool, 'operation::small, 'any::small) io \<Rightarrow> (unit, 'operation, 'any) io" where
"loop body \<equiv> Loop (to_V body) (return ())"


end


