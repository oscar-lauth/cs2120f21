
--axiom em : ∀ (p : Prop), p ∨ ¬p

-- 1
example : 0 ≠ 1 :=
begin
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  --exact false.elim (h (eq.refl 0)),
  have f := (h (eq.refl 0)),
  exact false.elim f,
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume p : P,
  -- ¬¬P
  -- ¬P→false
  -- (P→false)→ false
  assume np,
  apply false.elim (np p),
end

theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume nnp,
  --in classical logic this works, in constructive reasoning (like lean) this is not valid
  --can use em(law of excluded middle) axiom
  have pornp := classical.em P,
  cases pornp with p np,
  exact p,
  apply false.elim (nnp np),
end