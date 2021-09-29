--whd7zb; https://github.com/oscar-lauth/cs2120f21.git
-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume h,
  have pornp:=em P,
  have qornq:=em Q,
  cases pornp with p np,
  cases qornq with q nq,
  exact false.elim (h (and.intro p q)),
  exact or.intro_right (¬P) nq,
  exact or.intro_left (¬Q) np,
  --backward
  assume npornq,
  assume pandq,
  have p:=and.elim_left pandq,
  have q:=and.elim_right pandq,
  cases npornq with np nq,
  exact false.elim (np p),
  exact false.elim (nq q),
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume h,
  have pornp := em P,
  have qornq := em Q,
  cases pornp with p np,
  exact false.elim (h (or.intro_left Q p)),
  cases qornq with q nq,
  exact false.elim (h (or.intro_right P q)),
  exact and.intro np nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
  --forward
  assume h,
  cases h with p npandq,
  exact or.intro_left Q p,
  have q:=and.elim_right npandq,
  exact or.intro_right P q,
  --backward
  assume porq,
  cases porq with p q,
  exact or.intro_left (¬P ∧ Q) p,
  have pornp := em P,
  cases pornp with p np,
  exact or.intro_left (¬P ∧ Q) p,
  exact or.intro_right P (and.intro np q),
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
  --forward
  assume h,
  have porq:=and.elim_left h,
  have porr:=and.elim_right h,
 cases porq with p q,
 exact or.intro_left (Q∧R) p,
 cases porr with p r,
 exact or.intro_left (Q∧R) p,
 exact or.intro_right (P) (and.intro q r),
 --backward
 assume h,
 cases h with p qandr,
 exact and.intro (or.intro_left Q p) (or.intro_left R p),
 have q := and.elim_left qandr,
 have r:= and.elim_right qandr,
 exact and.intro (or.intro_right P q) (or.intro_right P r),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  --forward
  assume h,
  have porq:=and.elim_left h,
  have rors:=and.elim_right h,
  cases porq with p q,
  cases rors with r s,
  have pandr:=and.intro p r,
  exact or.intro_left ((P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)) (pandr),
  have pands := and.intro p s,
  exact or.intro_right (P ∧ R) (or.intro_left ((Q ∧ R) ∨ (Q ∧ S)) (pands)),
  cases rors with r s,
  have qandr:=and.intro q r,
  have a:=or.intro_left(Q ∧ S) qandr,
  have b:=or.intro_right(P ∧ S) a,
  exact or.intro_right (P ∧ R) b,
  have qands:=and.intro q s,
  have a:=or.intro_right (Q ∧ R) qands,
  have b:=or.intro_right (P ∧ S) a,
  exact or.intro_right (P ∧ R) b,
  --backward
  assume h,
  cases h with pandr x,
  have p:= and.elim_left pandr,
  have r:= and.elim_right pandr,
  exact and.intro (or.intro_left Q p) (or.intro_left S r),
  cases x with pands y,
  have p:= and.elim_left pands,
  have s:= and.elim_right pands,
  exact and.intro (or.intro_left Q p) (or.intro_right R s),
  cases y with qandr qands,
  have q:= and.elim_left qandr,
  have r:= and.elim_right qandr,
  exact and.intro (or.intro_right P q) (or.intro_left S r),
  have q:= and.elim_left qands,
  have s:= and.elim_right qands,
  exact and.intro (or.intro_right P q) (or.intro_right R s),
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∃ (n : ℕ), n≠0 :=
begin
  apply exists.intro _ _,
  exact 1,
  assume h,
  cases h,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
  assume h,
  have pornp := em P,
  cases pornp with p np,
  have q:= (h p),
  exact or.intro_right (¬P) q,
  exact or.intro_left Q np,
  assume nporq,
  assume p,
  cases nporq with np q,
  exact false.elim (np p),
  exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume h,
  assume nq,
  assume p,
  have q:= h p,
  exact nq q,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume h,
  assume q,
  have pornp := em P,
  cases pornp with p np,
  exact p,
  have nq := (h np),
  --contradiction,
  have f:= false.elim (nq q),
  exact false.elim f,
end

