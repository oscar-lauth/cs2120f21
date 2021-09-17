
namespace implies
axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q
--if we assume P is true, we can deduce Q is true


axiom p : P
--assume P is true
--assume we have a proof of P (p)
axiom pq : P → Q --or axiom pq : if_P_is_true_then_so_is_Q
--assume that we have a proof, pq, of P → Q

--intro rule for implies: assume premise, show conclusion
--elim rule for implies: apply a proof

--P is type Prop, pq is type P

#check p
#check P
--P is type Prop, p is type P
#check (pq p)

/-
Suppose P and Q are propositions and you
know that P → Q and that P are both true.
Show that Q is true.

Proof: Apply the truth of P → Q to the truth
of P to derive the truth of Q.

Proof: By the elimination rule for → with
pq applied to p.

Proof: By "modus ponens". QED
-/
--think of proof of P → Q as a function
--it takes in a proof of P and returns a proof of Q
end implies
namespace all
/-
FORALL
-/

axioms 
  (T : Type)
  (P : T → Prop)
  (t : T)
  (a : ∀ (x : T), P x) --forall x of type T, every x has property P

  --Does t have property P?
  --Yes by elim rule for forall
  
  example: P t := a t --apply a to t

  #check a t

  end all

  /-
  AND & →
  -/
  axioms (P Q : Prop)
  /-
  Want a proof of P ∧ Q.
  --AND is right defined to be right associative
  --exact: no placeholders, apply: can have placeholders for subgoals

  -/
  theorem and_associative : ∀ ( P Q R : Prop), (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  begin
    assume P Q R,
    assume h,
    have pq: P ∧ Q := and.elim_left h,
    have p : P := and.elim_left pq,
    have q : Q := and.elim_right pq,
    have r : R := and.elim_right h,
    exact and.intro p (and.intro q r)  
  end

