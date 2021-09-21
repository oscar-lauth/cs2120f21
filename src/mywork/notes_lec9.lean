/-
if ¬P (not P) is true then there should be a proof of it
then P has no proof
if P does have a proof, contradiction
P is false : P → false is true then we have a proof of false (impossible)
-/
example: false → false :=
begin
assume f,
exact f
end
example: false → true :=
begin
  assume f,
  exact true.intro,
end

example: true → false :=
begin
  assume t,
  --there are no proofs of false, not possible
end
--* if goal is ¬P, assume P is true and show thats a contradiction (P → false)
--case analysis: 'cases'
--given proof of P ∨ Q, can use case analysis for 2 subgoals. 

example: ¬ (0=1) :=
begin
  assume h,
  cases h, --elim rule for proof of false
end

example: false → false :=
begin
  assume f,
  --cases f,
  exact false.elim f,
end
theorem false_elim (P : Prop) (f : false) : P :=
begin
  cases f
end