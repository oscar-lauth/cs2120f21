/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

In English: Given propositions, P and Q, a proof of P → Q, and a proof of P, 
we can obtain a proof of Q by applying P → Q to P. 


(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- implies elim
            (q : Q)
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p2q,
  apply p2q,
end

-- Extra credit [2 points]. Who invented this principle?
--Aristotle?


-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Heres our answer]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- the proposition true is always invariably true thus we can always obtain a proof of true. 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true :=
  begin
    exact true.intro
  end


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Give an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Using a proof of P as well as a proof of Q, we can construct a proof of P ∧ Q.


ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/
/-
(P Q : Prop) (pq : P ∧ Q)
---------------------------- and.elim_left
        (p : P)

(P Q : Prop) (pq : P ∧ Q)
---------------------------- and.elim_right
        (q : Q)
-/

--and.elim_left : Given propositions, P and Q, a proof of P ∧ Q, we can obtain a proof of P
--and.elim_right : Given propositions, P and Q, a proof of P ∧ Q, we can obtain a proof of Q

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P :=
  begin
    assume P Q,
    assume qandp,
    exact and.elim_right qandp,
  end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- assume an arbitrary t, then show Q t i.e. that t has property Q

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- forall elim
                (Q t)

-- English language answer here
--Given T is any type, Q is any proposition, and we have a proof pf that 
all t of type T have property Q. We apply pf to t to obtain in particuliar that t has property Q. 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- using ∀ elimination, you apply pf to t to derive a proof of Q
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  (Lynn : Person)
  (knowsLogicLynn : KnowsLogic Lynn)


/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : (BetterComputerScientist Lynn):=
  begin
    apply LogicMakesYouBetterAtCS _,
    exact knowsLogicLynn,
  end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/- ¬P means that P → false so the strategy in proving ¬P is to 
assume P and show this leads to a contradiction and conclude P → false and thus ¬P is proved.
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that this assumption leads to a contradiction.
From this derivation you can conclude ¬P → false i.e. ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is classically valid, and that accepting the axiom
of the law of the excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q : Prop), (P ↔ Q)→(Q ↔ P) :=
begin
  assume P Q,
  assume h,
  have pq := h.elim_left,
  have qp := h.elim_right,
  apply iff.intro qp pq,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means.

English Rendition:
Everyone likes a nice, talented person. 
John Lennon is a person who is nice and talented, so everyone must like John Lennon.
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  unfold ELJL,
  intros,
  have johnNice:=and.elim_left JLNT,
  have johnTalent:=and.elim_right JLNT,
  apply elantp _ _,
  exact johnTalent,
  exact johnNice,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- car is heavy and red
    -- car is heavy and blue
    -- car is light and red
    -- car is light and blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), (x = y)→(y = x)

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), (x = y)→(y = z)→(x = z)


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (P:Prop), (¬¬P → P) ↔ (P → (P ∨ ¬P))

example: negelim_equiv_exmid:=
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume h,
  assume p,
  exact or.intro_left (¬P) p,
  --backward
  assume h,
  assume nnp,
  cases classical.em P with p np,
  exact p,
  exact false.elim (nnp np),
end

/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop
--axiom loves_refl : Loves : eq.symm,

example : (∃(s:Person), ∀(e:Person), Loves e s)→ 
(∃(s:Person), ∀(e:Person), Loves s e) :=
begin
  assume h,
  cases h with s pf,
  apply exists.intro s,
  assume e,
  have loves_e_s:= pf e,
  --given Loves is symmetric, loves_e_s → Loves s e. QED
  admit
end
-- example : ∀(P1 P2:Person),(Loves P1 P2 ↔ Loves P2 P1) ∧ (∃(s:Person), ∀(e:Person), Loves e s)→ 
-- (∃(s:Person), ∀(e:Person), Loves s e) :=
-- begin
--   assume p1 p2,
--   assume h1,
--   have loves_refl:= and.elim_left h1,
--   have h2:=and.elim_right h1,
--   cases h2 with s pf,
--   apply exists.intro s _,
--   assume e,
--   have j:= iff.elim_left loves_refl,
--   have g:= pf e,
--   have n:=j g,
--   -- (j (pf e))
--   --apply
-- end