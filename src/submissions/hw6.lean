import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ {α : Type} (L : set α),L ∩ L = L := 
begin
  intros a L,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with l,
  exact l,
  --backward
  assume h,
  apply and.intro h h,
end

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example : ∀ {α : Type} (s1 s2 : set α),s1 ∪ s2 = s2 ∪ s1 := 
begin
  intros a s1 s2,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with mem1 mem2,
  exact or.inr mem1,
  exact or.inl mem2,
  --backward
  assume h,
  cases h with mem2 mem1,
  exact or.inr mem2,
  exact or.inl mem1,
end
/-
Informal English Proof:
In short, we can use case analysis to examine when any x is a member of either s1 or of s2. 
It obviously follows then, that any x will be a member of either s2 or of s1 which is the defintion of s2 ∪ s1.
The same tactic can be applied to prove the backwards direction for the equivalence connective(=). QED
-/

/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example : ∀ {α : Type} (L M R: set α),(L ⊆ L) ∧ (L ⊆ M → M ⊆ R → L ⊆ R):= 
begin
  intros a l m r,
  apply and.intro _ _,
  assume x h,
  assumption,
  assume lsubm msubr,
  assume i j,
  have linm:= (lsubm j),
  exact (msubr linm),
end
/-
Informal English Proof:
To prove ⊆ is reflexive (L ⊆ L) we must show that for any x, x is a member of L implies that x is a member of L.
Our goal is in our assumption. QED
To prove ⊆ is transitive, L ⊆ M means M contains L. M ⊆ R means R contains M.
Thus, we can use these two assumptions to rewrite this as R contains L, ie L ⊆ R. QED.
-/
/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example: ∀ {α : Type} (L M R : set α), ((L ∪ M) ∪ R) = (L ∪ (M ∪ R)) ∧ ((L ∩ M) ∩ R) = (L ∩ (M ∩ R)):=
begin
  intros a l m r,
  apply and.intro _ _,
  --∪ assoc.
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with hl hr,
  cases hl with ll lr,
  apply or.intro_left (_) ll,
  apply or.intro_right (_) (or.intro_left (_) lr),
  apply or.intro_right (_) (or.intro_right (_) hr),
  --backward
  assume h,
  cases h with hl hr,
  apply or.intro_left (_) (or.intro_left (_) hl),
  cases hr with rl rr,
  apply or.intro_left (_) (or.intro_right (_) rl),
  apply or.intro_right (x∈l∪m) rr,
  --∩ assoc.
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  have hlm:=and.elim_left h,
  have hr:=and.elim_right h,
  have hl:= and.elim_left hlm,
  have hm:= and.elim_right hlm,
  apply and.intro hl (and.intro hm hr),
  --backward
  assume h,
  have hl:=and.elim_left h,
  have hmr:=and.elim_right h,
  have hm:= and.elim_left hmr,
  have hr:= and.elim_right hmr,
  apply and.intro (and.intro hl hm) hr,
end
/-
Informal English Proof:
To prove ∪ is associative ((L ∪ M) ∪ R) = (L ∪ (M ∪ R)), we can use case analysis to examine individual proofs of L, M, R.
Then, for each of these cases we can use these proofs and OR introduction to construct the required disjunctions for 
the forward and backward directions for the equivalnce connective(=). QED.

To prove ∩ is associative ((L ∩ M) ∩ R) = (L ∩ (M ∩ R)), we can use AND elimination to obtain individual proofs of L, M, R
and recombine them with AND introduction to construct the requried conjunctions for the forward and 
backward directions for the equivalence connective(=). QED. 
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/
example: ∀ {α : Type} (L M R : set α),(L ∩ (M ∩ R)) = ((L ∩ M) ∩ (L ∩ R)):=
begin
  intros a l m r,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  have hl:=and.elim_left h,
  have hmr:=and.elim_right h,
  have hm:=and.elim_left hmr,
  have hr:=and.elim_right hmr,
  apply and.intro,
  exact and.intro hl hm,
  exact and.intro hl hr,
  --backward
  assume h,
  have hlm:=and.elim_left h,
  have hlr:=and.elim_right h,
  have hl:= and.elim_left hlm,
  have hm:= and.elim_right hlm,
  have hr:=and.elim_right hlr,
  apply and.intro hl (and.intro hm hr),
end
/-
Informal English Proof:
To prove ∩ is left-distributive over ∩, (L ∩ (M ∩ R)) = ((L ∩ M) ∩ (L ∩ R)), we can use AND elimination on the
assumed proposition to obtain individual proofs of L,M,R. Then, applying AND introduction with the proofs of L,M,R, 
it obvsiously follows we can construct the required conjuction statements to prove the 
forward and backward directions for the equivalence connective (=). QED.  
-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
example: ∀ {α : Type} (L M R : set α),(L ∪ (M ∩ R)) = ((L ∪ M) ∩ (L ∪ R)):=
begin
  intros a l m r,
  apply set.ext _,
  assume x,
  split,
  --forward
  assume h,
  cases h with hl hmr,
  apply and.intro (or.intro_left (_) hl) (or.intro_left (_) hl),
  have hm:=and.elim_left hmr,
  have hr:=and.elim_right hmr,
  apply and.intro (or.intro_right (_) hm) (or.intro_right (_) hr),
  --backward
  assume h,
  have hlm:=and.elim_left h,
  have hlr:=and.elim_right h,
  cases hlm with hl hm,
  apply or.intro_left (_) hl,
  cases hlr with hl hr,
  apply or.intro_left (_) hl,
  apply or.intro_right (_) (and.intro hm hr),
end
/-
Informal English Proof:
To prove ∪ is left-distributive over ∩ is to show (L ∪ (M ∩ R)) = ((L ∪ M) ∩ (L ∪ R)).
For the forward direction of the equivalence connective (=), cases analysis as well as AND elimination
can be applied to the assumed proposition to examine individual proofs of L,M,R. By applying OR introduction to these proofs,
it obviously follows we can obtain proofs of the disjunctions (L ∪ M), (L ∪ R). 
The requried conjuction,((L ∪ M) ∩ (L ∪ R)), can then be constructed using the proofs of these two disjunctions by AND introduction.

For the backward direction of the equivalence connective (=), AND elimination followed by case analysis on
the assumed proposition can be applied to examine individual proofs of L,M,R. The required disjunction, (L ∪ (M ∩ R)),
can then be constructed using the proof of L in one case and the conjuction of proofs of M, R in the other case. QED
-/


