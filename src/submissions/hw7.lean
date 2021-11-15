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
English: To prove this proposition, we must show reflexivity of the relation implies false. 
So, we assume the relation is reflexive and then apply a beta to reflexivity to obtain r b b.
Now that we have a proof that r b b, we obtain a proof of ¬r b b by applying asymmetry to r b b.
This leaves us with a contradiction, thus reflexivity of r implies false. QED.
The proposition is not true if the existence of β is removed as then the empty set serves as a counterexample to the proposition.
-/



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
English: To prove s1 = s2, we must show that for any x, if x is in s1, x is in s2 and vice versa.
Given that s1 is a subset of s2, it obviously follows that that all x in s1 are in s2 by defintion of subset.
Further, given that s2 is a subset of s1, it obviously follows that that all x in s2 are in s1 by defintion of subset.QED  
-/


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
/-
English: To prove 1 divides n forall n, we must show there's a k such that n=k*1.
First, we examine the case where n=0, it obviously follows that 0=k*1 for k=0 as
0=0*1 by the basic rules of algebra and reflexivity of equality.
Next, we examine the case where n is some non-zero nat. It obviously follows that n=k*1
for k=n as n=n*1 by the basic rules of algebra. QED
-/

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
/-
English: To prove n divides n forall n, we must show there's a k such that n=k*n.
First, we examine the case where n=0, it obviously follows that 0=k*0 for k=0(or really any k) as
0=0*0 by the basic rules of algebra and reflexivity of equality.
Next, we examine the case where n is some non-zero nat. It obviously follows that n=k*n
for k=1 as n=1*n by the basic rules of algebra. QED
-/

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
/-
English: To prove divides is reflexive, we must show forall x, there's a k such at x=k*x.
First, we examine the case where x=0, it obviously follows that 0=k*0 for k=0(or really any k) as
0=0*0 by the basic rules of algebra and reflexivity of equality.
Next, we examine the case where x is some non-zero nat. It obviously follows that x=k*x
for k=1 as x=1*x by the basic rules of algebra. QED
-/ 

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume h j,
  cases h with a hpf,
  cases j with b jpf,
  rw jpf,
  rw hpf,
  apply exists.intro (b*a),
  ring,
end
/-
English: To prove divides is transitive, we must show forall x,y,z, 
if x divides y and y divides z then x divides z.
Using substitution on the defintions of x divides y and y divides z, 
we can rewrite the goal(z=k*x) as b * (a * x) = k * x. It obviously follows that b * (a * x) = k * x 
for k= b * a as b * (a * x) = b * a * x by the basic rules of algebra. QED.
-/ 

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
/-
English: To prove divides is antisymmetric, it must be shown that forall x,y, x divides y and y divides x only if x=y.
Using substitution on the defintions of x divides y and y divides x, we can rewrite the goal as x =hn*x.
By basic algebra it's obvious that hn=1, and thus x=1*x by the ring axioms. QED. 
-/


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
example : (∃(b:β),true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume h,
  cases h with b t,
  assume i j k,
  have notrbb:=(k b),
end
/-
This proposition is completely false.
Even after adding an existence of β's to rule out the empty set, this proposition still remains false.
A clear counterexample is the relation less than (<). Less than is transitive (5<6, 6<7, → 5<7).
Less than is also not symmetric (5<6 → 6<5 → false). Thus, according to the proposition, less than should not be irreflexive.
However, less than clearly IS irreflexive as (5<5 → false). Thus, the proposition is definitively false and unproveable. QED
-/

end relation
