/-
whd7zb; https://github.com/oscar-lauth/cs2120f21.git
-/


/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro --There always exists a proof of true

example : false := _     -- trick question? why? There exists no proof of false

/-
Show that P ∨ P ↔ P. 
For the forward direction, we assume to have a specific proposition P and a proof
of P ∨ P. Using a case analysis of P ∨ P, in case 1 we get a proof of P and in case 2 
we get a proof of P. Therefore, P ∨ P implies P. For the backward direction, we assume 
a proof of P and use the left introduction rule for or to show that P implies P ∨ P. 
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    cases porp with p1 p2,
    exact p1,
    exact p2,
  -- backward
    assume p,
    exact or.intro_left P p,
end

/-
Show that P ∧ P ↔ P.
For the forward direction, we assume to have a specific proposition P and a proof
of P ∧ P. Using the elimination rule for AND on P ∧ P, we get a proof of P. 
For the backward direction, we assume a proof of P and apply the AND introduction rule to form P ∧ P. 
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pandp,
  apply and.elim_left pandp,
  assume p,
  apply and.intro _ _,
  exact p,
  exact p,
end
/-
Show that P ∨ Q ↔ Q ∨ P.
For the forward direction, we assume to have specific propositions P, Q and a proof
of P ∨ Q. Using case analysis on P ∨ Q, we get a proof of P for case 1. Then we use the right OR introduction rule 
to prove Q ∨ P. For case 2, we get a proof of Q. Then we use the left OR introduction rule to prove Q ∨ P.
For the backward direction, we assume a proof of Q ∨ P and use case analysis on this proof. Case 1 gives 
a proof of Q which we use in right OR introduction rule to prove P ∨ Q. Case 2 gives a proof of P which we use in the left OR introduction rule to prove P ∨ Q.
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume porq,
  cases porq with p q,
  apply or.intro_right Q p,
  apply or.intro_left P q,
  --backward
  assume qorp,
  cases qorp with q p,
  apply or.intro_right P q,
  apply or.intro_left Q p,
end
/-
Show that P ∧ Q ↔ Q ∧ P.
For the forward direction, we assume to have specific propositions P, Q and a proof
of P ∧ Q. Using the AND elimination left rule we get a proof of P and using the AND 
elimination right rule we get a proof of Q. We use the proof of Q and then the proof 
of P in the introduction rule for AND to prove Q ∧ P. For the backward direction, we assume a 
proof of Q ∧ P. We apply to this the right and left AND elimination rules to get proofs of P and Q respectively.
Then, using the AND introduction rule we form a proof of P ∧ Q.
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --foward
  assume pandq,
  have p : P := and.elim_left pandq,
  have q : Q := and.elim_right pandq,
  exact and.intro q p,
  --backward
  assume qandp,
  have p : P := and.elim_right qandp,
  have q : Q := and.elim_left qandp,
  exact and.intro p q,
  
end
/-
Show that P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R).
For the forward direction, we assume to have specific propositions P, Q, R and a proof
of P ∧ (Q ∨ R). Using the AND elimination left rule we get a proof of P and using the AND 
elimination right rule we get a proof of Q ∨ R. We then do case analysis on Q ∨ R. Case 1 
gives a proof of Q. We then use the AND introduction rule on the proof of P and proof Q to get a proof of P ∧ Q.
Then, we use the OR left introduction rule with our proof of P ∧ Q to get (P ∧ Q) ∨ (P ∧ R)
Case 2 gives a proof of R. We then use the AND introduction rule on the proof of P and proof of R to get a proof of P ∧ R.
Then, we use the OR right introduction rule with our proof of P ∧ R to get (P ∧ Q) ∨ (P ∧ R)
For the backward direction, we assume a proof of (P ∧ Q) ∨ (P ∧ R). We do case analysis on (P ∧ Q) ∨ (P ∧ R).
Case 1 gives a proof of P ∧ Q. We then do case analysis on this. Subcase 1 gives a proof of P and subcase 2 gives a proof of Q.
We use the OR introduction left rule on proof of Q to get Q ∨ R. Using the AND introduction rule on the proof of P and on Q ∨ R we get P ∧ (Q ∨ R).
Case 2 gives a proof of P ∧ R. We then do case analysis on this. Subcase 1 gives a proof of P and subcase 2 gives a proof of R.
We use the OR introduction right rule on proof of R to get Q ∨ R. Using the AND introduction rule on the proof of P and on Q ∨ R we get P ∧ (Q ∨ R).
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume h, --Pand(QorR)
  have p : P := and.elim_left h,
  have qorr : Q ∨ R := and.elim_right h,
  cases qorr with q r,
  have pandq : P ∧ Q := and.intro p q,
  apply or.intro_left (P ∧ R) pandq,
  have pandr : P ∧ R := and.intro p r,
  apply or.intro_right (P ∧ Q) pandr,
  --backward
  assume h, --(PandQ)or(PandR)
  cases h with pandq pandr,
  cases pandq with p q,
  apply and.intro p (or.intro_left R q),
  cases pandr with p r,
  apply and.intro p (or.intro_right Q r)
end
/-
Show that P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
For the forward direction, we assume to have specific propositions P, Q, R and a proof
of P ∨ (Q ∧ R). We do case analysis on P ∨ (Q ∧ R). Case 1 gives a proof of P. Using the 
OR left introduction rule on the proof P we get proofs of P ∨ Q and P ∨ R. Then we apply the
AND introduction rule on these proofs to get (P ∨ Q) ∧ (P ∨ R). Case 2 gives a proof of Q ∧ R. 
We get a proof of Q using AND left elimination rule on Q ∧ R, a proof of R using AND right elimination rule on Q ∧ R.
Using the OR right introduction rule on the proof of Q we get a proof of P ∨ Q. 
Using the OR right introduction rule on the proof of R we get a proof of P ∨ R.
Applying the AND introduction rule on these proofs, we get a proof of (P ∨ Q) ∧ (P ∨ R).
For the backward direction, we assume a proof of (P ∨ Q) ∧ (P ∨ R). Applying AND left elimination rule to (P ∨ Q) ∧ (P ∨ R), we get a proof of P ∨ Q.
Applying AND right elimination rule to (P ∨ Q) ∧ (P ∨ R), we get a proof of P ∨ R. 
We then do case analysis on P ∨ Q and apply the OR introduction left rule to get a proof of P ∨ (Q ∧ R).
We then do case analysis on P ∨ R and apply the OR introduction left rule to get a proof of P ∨ (Q ∧ R).
Using proofs of Q and R from case analysis, we apply the AND introduction rule to get a proof of Q ∧ R.
We apply the OR introduction right rule to Q ∧ R to get a proof of P ∨ (Q ∧ R).
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume h, -- Por(QandR)
  cases h with p qandr,
  have porq : P ∨ Q := or.intro_left Q p,
  have porr : P ∨ R := or.intro_left R p,
  apply and.intro porq porr,
  have q: Q := and.elim_left qandr,
  have r: R := and.elim_right qandr,
  have porq : P ∨ Q := or.intro_right P q,
  have porr : P ∨ R := or.intro_right P r,
  apply and.intro porq porr,
  --backward
  assume h, -- (PorQ)and(PorR)
  have porq : P ∨ Q := and.elim_left h,
  have porr : P ∨ R := and.elim_right h,
  cases porq with p q,
  apply or.intro_left (Q ∧ R) p,

  cases porr with p r,
  apply or.intro_left (Q ∧ R) p,

  apply or.intro_right P (and.intro q r),

end
/-
Show that P ∧ (P ∨ Q) ↔ P.
For the forward direction, we assume to have specific propositions P, Q and a proof
of P ∧ (P ∨ Q). Using the AND left elimination rule on this proof, we get a proof of P.
For the backward direction, we assume to have a proof of P. Using the OR introduction left rule, we get a proof of P ∨ Q.
Then, we apply the AND introduction rule to the proof of P and proof of P ∨ Q to get a proof of P ∧ (P ∨ Q).
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume pandporq,
  have p : P := and.elim_left pandporq,
  exact p,
  --backward
  assume p,
  have porq : P ∨ Q := or.intro_left Q p,
  apply and.intro p porq,

end
/-
Show that P ∨ (P ∧ Q) ↔ P.
For the forward direction, we assume to have specific propositions P, Q and a proof
of P ∨ (P ∧ Q). We do case analysis on P ∨ (P ∧ Q). Case 1 gives a proof of P. Case 2 gives a 
proof of P ∧ Q which we can apply AND left elimination rule to get a proof of P.
In the backward direction, we assume to have a proof of P. We apply the OR introduction left rule to proof of P to get P ∨ (P ∧ Q).
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume h, -- Por(PandQ)
  cases h with p pandq,
  exact p,
  exact and.elim_left pandq,
  --backward
  assume p,
  apply or.intro_left (P ∧ Q) p,
end
/-
Show that P ∨ true ↔ true.
For the forward direction, we assume to have a specific proposition P and a proof
of P ∨ true. Applying the introduction rule for true, we get a proof of true.
In the backward direction, we assume to have a proof of true. We apply the OR introduction right rule to proof of true to get P ∨ true.
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume h, -- Portrue
  exact true.intro,
  --backward
  assume t,
  apply or.intro_right P t,
end
/-
Show that P ∨ false ↔ P.
For the forward direction, we assume to have a specific proposition P and a proof
of P ∨ false. We do case analysis on P ∨ false. Case 1 gives a proof of P. For case 2, applying the false elimination rule gives a proof of P.
In the backward direction, we assume to have a proof of P. We then apply the OR left introduction rule to the proof of P to get P ∨ false.  
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume h, -- Porfalse
  cases h with p f,
  exact p,
  exact false.elim f,
  --backward
  assume p,
  apply or.intro_left false p,
end
/-
Show that P ∧ true ↔ P.
For the forward direction, we assume to have a specific proposition P and a proof
of P ∧ true. We then apply the AND left elimination rule to P ∧ true to get a proof of P.
For the backward direction, we assume to have a proof of P. We apply the AND introduction rule to the proof of P and to a proof of true 
(from true's introduction rule) to get P ∧ true.
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume h, --Pandtrue
  apply and.elim_left h,
  --backward
  assume p,
  apply and.intro p true.intro,
end
/-
Show that P ∧ false ↔ false.
For the forward direction, we assume to have a specific proposition P and a proof
of P ∧ false. We apply AND right elimination rule to P ∧ false to get false. For the backward direction,
we assume to have false (the absence of a proof). We apply false's elimination rule to false to get a proof of P.
We then apply the AND introduction rule to the proof of P and false to get P ∧ false.
We combine the foward and backward proofs in the introduction rule for if and only if. QED
-/
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume h, --Pandfalse
  exact and.elim_right h,
  --backward
  assume f,
  have p:P := false.elim f,
  apply and.intro p f,
end


