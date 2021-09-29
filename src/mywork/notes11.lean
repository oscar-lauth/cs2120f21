def pt (a b c : ℕ):
Prop:= a*a + b*b = c*c
example: ∃ (a b c : ℕ),

∃(n:ℕ), red n ∧ blue n → ∃(n:ℕ), red n,
assume h, --red n ∧ blue n
exact and.elim_left h,
--intro rule for existence: witness and proof
--elim rule for existence: thing must exist, give it a name