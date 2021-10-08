axioms
(Person: Type)
(Likes : Person → Person → Prop) 
--Likes is 2 place predicate to represent binary relation between 2 Persons
example :
¬ (∀ p : Person, Likes p p) ↔ --not everyone likes themselves
∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,
  --forward
  assume h,
  have f:=classical.em (∃(p:Person), ¬Likes p p),
  cases f,
  exact f,
  have contra:∀ (p:Person), Likes p p := _,
  contradiction,
  assume p,
  have g := classical.em (Likes p p),
  cases g,
  exact g,
  have a : ∃ (p:Person), ¬Likes p p:=exists.intro p g,
  exact false.elim (f a),
  --backward
  assume h,
  cases h with w pf,
  assume j,
  

end