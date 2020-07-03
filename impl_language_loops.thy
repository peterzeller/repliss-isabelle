section "Implementation Language with Loops"
theory impl_language_loops
  imports Main 
    "HOL-Library.Monad_Syntax"
    repliss_sem
    ZFC_utils
    "fuzzyrule.fuzzy_goal_cases"
begin

text "We need to hide some ZFC constants so that the normal ones are still visible:"

hide_const (open) "ZFC_in_HOL.set"



text "So far, we have assumed that procedure implementations are given by arbitrary state machines.
Here we define an implementation language using a shallow embedding with the monad syntax package.
"


text_raw \<open>\DefineSnippet{io_defs_types}{\<close>
type_synonym iref = nat
type_synonym 'v store = "iref \<rightharpoonup> 'v"
text_raw \<open>}%EndSnippet\<close>

datatype 'a ref = Ref (iref:iref)
instantiation ref :: (type) small begin
instance proof
  obtain V_of :: "nat \<Rightarrow> V" and A :: "V" where "inj V_of" and "range V_of \<subseteq> elts A"
    by (metis infinite_\<omega> infinite_countable_subset)
                    

  have "\<exists>(V_of::'a ref \<Rightarrow> V) A. inj V_of \<and> range V_of \<subseteq> elts A"
  proof (intro conjI exI)
    show "inj (V_of \<circ> iref)"
      by (metis (mono_tags, lifting) \<open>inj V_of\<close> comp_apply injD inj_on_def ref.expand)

    show " range (V_of \<circ> iref) \<subseteq> elts A"
      using \<open>range V_of \<subseteq> elts A\<close> by auto
  qed

  show "small (UNIV::'a ref set)"
    by (meson \<open>\<exists>V_of A. inj V_of \<and> range V_of \<subseteq> elts A\<close> down small_image_iff)

qed
end

text \<open>The typeclass natConvert is the dual to the typeclass countable. 
A natConvert type is at least as big as the natural numbers, so any natural number can be converted 
to the type using fromNat.
\<close>
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


datatype ('c,'b) loopResult = Continue 'c | Break 'b

text_raw \<open>\DefineSnippet{io_defs_datatype}{\<close>
datatype ('a,'op, 'any) io =
    WaitLocalStep "'any store \<Rightarrow> bool \<times> 'any store \<times> ('a,'op, 'any) io"
  | WaitBeginAtomic "('a,'op, 'any) io"
  | WaitEndAtomic "('a,'op, 'any) io"
  | WaitNewId "'any \<Rightarrow> bool" "'any \<Rightarrow> ('a,'op, 'any) io"
  | WaitDbOperation 'op "'any \<Rightarrow> ('a,'op, 'any) io"
  | WaitReturn "'a" 
  | Loop 'any "V" "'any \<Rightarrow> ('a,'op, 'any) io" 
text_raw \<open>}%EndSnippet\<close>

\<comment> \<open>body is an @{typ \<open>'any \<Rightarrow> (('any,'any) loopResult, 'op, 'any) io\<close>} encoded a type V.
                                            Had to use dynamic typing here as Isabelle has no GADTs. \<close>



text "Actually show that we can embedd io into ZFCs V type:"



function (domintros) io_to_V :: "('a::embeddable,'op::embeddable, 'any::small) io \<Rightarrow> V" where
  "io_to_V (WaitLocalStep n)  = to_V (0::nat, to_V (\<lambda>s. let (a,b,c) = n s in to_V (a, b, io_to_V c)))"
| "io_to_V (WaitBeginAtomic n)  =  to_V (1::nat, io_to_V n)"
| "io_to_V (WaitEndAtomic n)  = to_V (2::nat, io_to_V n) "
| "io_to_V (WaitNewId P n)  =  to_V (3::nat, to_V (P, (\<lambda>x. io_to_V (n x))))"
| "io_to_V (WaitDbOperation op n)  =  to_V (4::nat, to_V (op, (\<lambda>x. io_to_V (n x))))"
| "io_to_V (WaitReturn s)  =  to_V (5::nat, to_V s)"
| "io_to_V (Loop i body n)  =  to_V (6::nat, to_V (i, body, (\<lambda>x. io_to_V (n x))))"
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
  fix x y :: "('a::embeddable,'op::embeddable, 'any::small) io"
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
    case (Loop i bdy cont)
    thus ?case proof (cases y, auto dest!: to_V_use_inj, rename_tac cont')
      fix cont'
      assume a0: "y = Loop i bdy cont'"
        and IH: "\<And>x3aa y. \<lbrakk>x3aa \<in> range cont; io_to_V x3aa = io_to_V y\<rbrakk> \<Longrightarrow> x3aa = y"
        and a2: "(\<lambda>x. io_to_V (cont x)) = (\<lambda>x. io_to_V (cont' x))"
        and a3: "io_to_V (Loop i bdy cont) = io_to_V y"

      from a2
      have "io_to_V (cont x) = io_to_V (cont' x)" for x
        by meson
      hence "(cont x) = (cont' x)" for x
        by (simp add: IH rangeI)
      thus "cont = cont' "
        by blast
    qed
  qed
qed



instance io :: (embeddable, embeddable, small) embeddable
  by (standard, force intro: io_to_V_inj)

definition loopResult_to_V :: "('a::embeddable, 'b::embeddable) loopResult \<Rightarrow> V" where
  "loopResult_to_V l = (case l of 
    (Break x) \<Rightarrow> to_V (False, x, undefined::'a)
  | (Continue x) \<Rightarrow> to_V (True, undefined::'b, x))"


lemma loopResult_to_V_inj: "inj loopResult_to_V"
  by standard (use to_V_use_inj in \<open>auto simp add: loopResult_to_V_def  split: loopResult.splits\<close>)



instance loopResult :: (embeddable, embeddable) embeddable
  by (standard, force intro: loopResult_to_V_inj)


instance loopResult :: (small, small) small
proof (rule show_small_type_class, intro conjI exI)

  have "\<exists>(f::'a \<Rightarrow> V). inj f \<and>   small (range f)"
    using small down to_V_property to_V_small by blast

  show "inj loopResult_to_V"
    by (simp add: loopResult_to_V_inj)

  have "small (range (to_V :: (bool\<times>'b\<times>'a)\<Rightarrow>V))"
    using to_V_small by blast


  thus "small (range (loopResult_to_V::('a,'b) loopResult\<Rightarrow>V))"
  proof (rule smaller_than_small)

    show "range (loopResult_to_V::('a,'b)  loopResult\<Rightarrow>V) \<subseteq>range (to_V :: (bool\<times>'b\<times>'a)\<Rightarrow>V)"
      by (auto simp add: loopResult_to_V_def split: loopResult.splits)
  qed
qed

definition loop_body_from_V :: "V \<Rightarrow> 'any \<Rightarrow> (('any,'any) loopResult, 'op::embeddable, 'any::small) io" where
"loop_body_from_V \<equiv> from_V"

definition loop_body_to_V :: "('any \<Rightarrow> (('any,'any) loopResult, 'op::embeddable, 'any::small) io) \<Rightarrow> V" where
"loop_body_to_V \<equiv> to_V"

lemma loop_body_from_V_rev[simp]: "loop_body_from_V (loop_body_to_V x) = x"
  by (simp add: loop_body_from_V_def loop_body_to_V_def)


text_raw \<open>\DefineSnippet{io_defs_bind}{\<close>
function (*<*) (domintros) (*>*) bind (*<*) :: "('a, 'op, 'any) io \<Rightarrow> ('a \<Rightarrow> ('b, 'op,'any) io) \<Rightarrow> ('b, 'op,'any) io" (*>*) (infixl "\<bind>io" 54)  where
  "WaitLocalStep n \<bind>io f = (WaitLocalStep (\<lambda>s. let (a,b,c) = n s  
                                                  in (a, b, bind c f)))"
| "WaitBeginAtomic n \<bind>io f = (WaitBeginAtomic (n \<bind>io f))"
| "WaitEndAtomic n \<bind>io f = (WaitEndAtomic (n \<bind>io f))"
| "WaitNewId P n \<bind>io f = (WaitNewId P (\<lambda>i. n i \<bind>io f))"
| "WaitDbOperation op n \<bind>io f = (WaitDbOperation op (\<lambda>i. n i \<bind>io f))"
| "WaitReturn s \<bind>io f = (f s)"
| "Loop i body n \<bind>io f = (Loop i body (\<lambda>x. n x \<bind>io f))"
text_raw \<open>}%EndSnippet\<close>
  by (pat_completeness, auto)
termination
  using [[show_sorts]]
proof auto
  show "bind_dom (i, f)" for i :: "('a, 'op, 'any) io" and f :: "'a \<Rightarrow> ('d, 'op, 'any) io"
    apply (induct i, auto simp add: bind.domintros)
    by (metis bind.domintros(1) range_eqI)
qed





fun toImpl :: "(('val store \<times> uniqueId set \<times> (('val,'op::{small,valueType}, 'val::{small,valueType}) io)), 'op, 'val) procedureImpl" where
  "toImpl (store, knownUids, WaitLocalStep n) = (
        let (ok, store', n') = n store 
        in LocalStep (ok \<and> (finite (dom store) \<longrightarrow> finite (dom (store')))) 
                      (store', knownUids, n'))"
| "toImpl (store, knownUids, WaitBeginAtomic n) = 
        BeginAtomic (store, knownUids, n)"
| "toImpl (store, knownUids, WaitEndAtomic n) = 
        EndAtomic (store, knownUids,  n)"
| "toImpl (store, knownUids, WaitNewId P n) = 
        NewId (\<lambda>i. if P i then Some (store, knownUids \<union> uniqueIds i,  n i) else None)"
| "toImpl (store, knownUids, WaitDbOperation op n) = (
        if uniqueIds op \<subseteq> knownUids then 
          DbOperation op (\<lambda>r. (store, knownUids \<union> uniqueIds r, n r)) 
        else 
          LocalStep False (store, knownUids, WaitDbOperation op n))"
| "toImpl (store, knownUids, WaitReturn v) = (
        if uniqueIds v \<subseteq> knownUids then 
          Return v 
        else 
          LocalStep False (store, knownUids, WaitReturn v))"
| "toImpl (store, knownUids, Loop i body n) = 
        LocalStep True 
            (store, knownUids, (loop_body_from_V body i) \<bind>io (\<lambda>r. 
               case r of Break x \<Rightarrow> n x 
                       | Continue x \<Rightarrow> Loop x body n))"

abbreviation  toImpl' where
 "toImpl' proc (x :: ('val,'op,'val) io) \<equiv> ((Map.empty, uniqueIds proc, x) , toImpl)"


adhoc_overloading Monad_Syntax.bind bind

definition pause :: "(unit,'op,'any) io" where
"pause \<equiv> WaitLocalStep (\<lambda>s. (True, s, WaitReturn ()))"

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



text "Next, we define some operations to work with references: 
We simply encode references using natural numbers."

definition "fromAny x \<equiv> from_nat (toNat x)"
definition "intoAny x \<equiv> fromNat (to_nat x)"

lemma fromAny_intoAny[simp]: "fromAny (intoAny x) = x"
  by (simp add: fromAny_def fromNat_inj intoAny_def the_inv_f_f toNat_def)

definition freshRefH :: "nat \<Rightarrow> nat set \<Rightarrow> nat" where
"freshRefH mi D \<equiv> (if finite D then LEAST x. x \<ge> mi \<and> (\<forall>y\<in>D. x>y) else 0)"

abbreviation freshRef :: "nat set \<Rightarrow> nat" where
"freshRef \<equiv> freshRefH 0"


lemma freshRef_empty[simp]: "freshRefH x {} = x"
  by (auto simp add: freshRefH_def Least_equality)

lemma freshRef_insert[simp]: 
"freshRefH mi (insert x S) = freshRefH (max mi (Suc x)) S"
  by (auto simp add: freshRefH_def intro!: arg_cong[where f=Least])
  

definition makeRef :: "'a::countable \<Rightarrow> ('a ref, 'op, 'any::natConvert) io" where
"makeRef v \<equiv> WaitLocalStep (\<lambda>s. let r = freshRef (dom s) in (True, s(r \<mapsto> intoAny v), WaitReturn (Ref r)))"

definition s_read :: "('any::natConvert) store \<Rightarrow> ('a::countable) ref \<Rightarrow> 'a" where
"s_read s ref \<equiv> 
    case s (iref ref) of 
      Some v \<Rightarrow> fromAny v 
    | None  \<Rightarrow> from_nat 0"

definition read :: "'a ref \<Rightarrow> ('a::countable, 'op, 'any::natConvert) io" where
"read ref \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
      Some v \<Rightarrow> (True, s, WaitReturn (fromAny v)) 
    | None  \<Rightarrow> (False, s, WaitReturn (from_nat 0)))"

definition assign :: "('a::countable) ref \<Rightarrow> 'a \<Rightarrow> (unit, 'op, 'any::natConvert) io" (infix ":\<leftarrow>" 60) where
"assign ref v \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
    Some _ \<Rightarrow> (True, s((iref ref) \<mapsto> intoAny v), WaitReturn ()) 
  | None  \<Rightarrow> (False, s, WaitReturn ())) "

definition update :: "('a::countable) ref \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> (unit, 'op, 'any::natConvert) io" where
"update ref upd \<equiv> WaitLocalStep (\<lambda>s. case s (iref ref) of 
      Some v \<Rightarrow> (True, s((iref ref) \<mapsto> intoAny (upd (fromAny v))), WaitReturn ()) 
    | None  \<Rightarrow> (False, s, WaitReturn ())) "




lemma toImpl_simps_newId[simp]:
"toImpl (store, u, newId P) = NewId (\<lambda>i. if P i then Some (store, u \<union> uniqueIds i, return i) else None)"
by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)
lemma toImpl_simps_pause[simp]:
"toImpl (store, u, pause) = LocalStep True (store, u, return ())"
by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)
lemma toImpl_simps_beginAtomic[simp]:
"toImpl (store, u, beginAtomic) = BeginAtomic (store, u, return ())"
by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)
lemma toImpl_simps_endAtomic[simp]:
"toImpl (store, u, endAtomic) = EndAtomic (store, u, return ())"
by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)
lemma toImpl_simps_call[simp]:
   "toImpl (store, u, call op ) = (if uniqueIds op \<subseteq> u then DbOperation op  (\<lambda>r. (store, u \<union> uniqueIds r, return r)) else LocalStep False (store, u, call op))"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: HOL.ext split: io.splits)
lemma toImpl_simps_return[simp]:
  "toImpl (store, u, return x) = (if uniqueIds x \<subseteq> u then Return x else LocalStep False (store, u, return x))"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def return_def intro!: ext split: io.splits)

schematic_goal "toImpl (store, u, newId P \<bind> x) = ?x"
 by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)


lemma toImpl_bind_simps_newid[simp]:
"toImpl (store, u, newId P \<bind> x) = NewId (\<lambda>i. if P i then Some (store, u \<union> uniqueIds i, x i) else None)"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)

lemma toImpl_bind_simps_pause[simp]:
"toImpl (store, u, pause \<bind> x) = LocalStep True (store, u, x ())"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)

lemma toImpl_bind_simps_beginAtomic[simp]:
"toImpl (store, u, beginAtomic \<bind> x) = BeginAtomic (store, u, x ())"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)

lemma toImpl_bind_simps_endAtomic[simp]:
" toImpl (store, u, endAtomic \<bind> x) = EndAtomic (store, u, x ())"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)

lemma toImpl_bind_simps_call[simp]:
"toImpl (store, u, call op  \<bind> x) = (if uniqueIds op \<subseteq> u then DbOperation op  (\<lambda>r. (store, u \<union> uniqueIds r, x r)) else LocalStep False (store, u, call op  \<bind> x))"
  by (auto simp add: newId_def pause_def beginAtomic_def endAtomic_def call_def intro!: ext split: io.splits)



paragraph "Monad Laws"

text "We prove the typical monad laws: identity of return and associativity."

declare Basic_BNFs.snds.simps[simp]
declare Basic_BNFs.fsts.simps[simp]


lemma return_left_ident[simp]: 
  fixes x and f :: "'a \<Rightarrow> ('b,'op, 'any) io"
  shows "return x \<bind> f = f x"
  by (auto simp add: return_def)

lemma right_ident[simp]: 
  fixes m :: "('a,'op, 'any) io"
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
  fixes x :: "('a,'op, 'any) io"
    and y :: "'a \<Rightarrow> ('b,'op, 'any) io"
    and z :: "'b \<Rightarrow> ('c,'op, 'any) io"
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


 text \<open>
 \DefineSnippet{io_bind_monad_rules}{
    @{thm [display] return_left_ident}
    @{thm [display] right_ident}
    @{thm [display] bind_assoc}
 }%EndSnippet
 \<close>



lemma atomic_simp1[simp]: 
"toImpl (s, u, atomic f) = BeginAtomic (s, u, f \<bind> (\<lambda>r. endAtomic \<bind> (\<lambda>_. return r)))"
  by (auto simp add: atomic_def)

lemma atomic_simp2[simp]: 
"toImpl (s, u, atomic f \<bind> x) = BeginAtomic (s, u, f \<bind> (\<lambda>a. endAtomic \<bind> (\<lambda>b. x a)))"
  by (auto simp add: atomic_def)


subsection "Syntactic sugar for loops"

definition loop :: "'a::countable \<Rightarrow> ('a \<Rightarrow> (('a,'b::countable) loopResult, 'op::small, 'any::{small,natConvert} ) io) \<Rightarrow> ('b, 'op, 'any) io" where
"loop init body \<equiv> Loop 
      (intoAny init)
      (loop_body_to_V (\<lambda>acc. 
          body (fromAny acc) \<bind>io (\<lambda>res. return (
            case res of Continue x \<Rightarrow> (Continue (intoAny x)) 
                      | Break x \<Rightarrow> (Break (intoAny x)))))) 
      (return \<circ> fromAny)"


definition while :: "(bool, 'op::small, 'any::small) io \<Rightarrow> (unit, 'op, 'any) io" where
"while body \<equiv> Loop 
      undefined 
      (loop_body_to_V (\<lambda>_. body \<bind>io (\<lambda>x. return ((if x then Break else Continue) undefined)))) 
      (return \<circ> (\<lambda>_. ()))"


definition "forEach"  :: "'e::countable list \<Rightarrow> ('e \<Rightarrow> ('a::countable, 'op::small, 'any::{small,natConvert}) io) \<Rightarrow> ('a list, 'op, 'any) io" where
"forEach elements body \<equiv> 
    loop (elements,[]) (\<lambda>(elems, acc).
        case elems of
        [] \<Rightarrow> return (Break (rev acc))
        | (x#xs) \<Rightarrow> body x \<bind>io (\<lambda>r. return (Continue (xs, r#acc)))   
    )"
  


 text \<open>
 \DefineSnippet{io_language_constructs}{
    @{thm [display] pause_def}
    @{thm [display] beginAtomic_def}
    @{thm [display] endAtomic_def}
    @{thm [display] newId_def}
    @{thm [display] call_def}
    @{thm [display] return_def}
    @{thm [display] skip_def}
    @{thm [display] atomic_def}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{io_language_constructs_refs}{
    @{thm [display] makeRef_def}
    @{thm [display] read_def}
    @{thm [display] assign_def}
    @{thm [display] update_def}
 }%EndSnippet
 \<close>

 text \<open>
 \DefineSnippet{io_language_constructs_loops}{
    @{thm [display] loop_def}
    @{thm [display] while_def}
    @{thm [display] forEach_def}
 }%EndSnippet
 \<close>


end


