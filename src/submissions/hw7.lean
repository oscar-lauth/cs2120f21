import data.set
import tactic.ring
namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric,
  unfold reflexive,
  assume h,
  cases h with b pf,
  assume j k,
  have rbb:= (k b),
  have notrbb:= (j rbb),
  contradiction,
end



/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃(b:β),true)→transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume h,
  assume trans refl,
  assume asymm,
  cases h with b pf,
  have rbb:= refl b,
  have notrbb:= asymm rbb,
  contradiction,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  split,
  assume xins1,
  apply s1s2 xins1,
  assume xins2,
  apply s2s1 xins2,
end


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  unfold divides,
  assume h,
  cases h with n pf,
  apply exists.intro 0,
  apply refl,
  apply exists.intro n.succ,
  ring,
  --rw nat.mul_one,
end

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  unfold divides,
  assume h,
  cases h with n pf,
  apply exists.intro 0,
  apply refl,
  apply exists.intro 1,
  ring,
  --rw nat.one_mul,
end

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume h,
  cases h with n pf,
  apply exists.intro 0,
  apply refl,
  apply exists.intro 1,
  ring,
  --rw nat.one_mul,
end 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume h j,
  cases h with hn hpf,
  cases j with jn jpf,
  apply exists.intro (hn*jn),
  rw jpf,
  rw hpf,
  ring,
end

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

-- Answer here
/-
Divides is not symmetric. Divides means that for two nats, m,n
there exists a nat k such that m = k * n.
For divides to be symmetric, then m = k * n. and n = k * m.
This can be simply disproven with the counterexample m=4,n=2. 4=k*2 is true for k=2.
However, there exists no nat k such at 2=k*4. Thus, divides is not a symmetric relation.
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin
  unfold anti_symmetric divides,
  assume x y,
  assume h j,
  cases h with hn hpf,
  cases j with jn jpf,
  rw hpf,
  have foo: hn=1:=sorry,
  rw foo,
  ring,
end


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume h b rbb,
  apply h rbb,
  assumption,
end

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume h j,
  assume x y rxy,
  assume ryx,
  have notrxx:=(h x),
  have rxx:=(j rxy ryx),
  contradiction,
end

-- C
example : (∃(b:β),true)→transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume h j k i,
  cases h with b pf,
  --have rbb:=(j b b),
  have notrbb:=(i b),
end


end relation
