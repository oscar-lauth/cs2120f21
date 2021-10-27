import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start:
-- your completed English rendition here:
If there's a function that maps every α value to a corresponding β value and if all α have property p 
and every mapping of α by f has property q, and given there exists α that has property p, 
then there exists a correspondong β with property q.
-/


-- Give your formal proof here
begin
  assume h,
  assume j,
  cases h with hw hpf,
  cases j with jw jpf,
  --have b:= hw jw,
  apply exists.intro (hw jw),
  apply (hpf jw jpf),
end
  
--Informal proof:
/-
We can apply the given implication that if α has property p then (f a) has property q to 
β because we are given that β is a mapping of α by f (ie b = f a).
Thus, if there's an α with property p this suffices to prove that there's a β with property q. QED
-/

