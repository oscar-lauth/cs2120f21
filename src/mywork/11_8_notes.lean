/-
total relation: for every x y, x is related to y OR y is related to x
less than equal is a total order

partial_order: subset inclusion on the powerset of a given set.
-/
import ..instructor.lectures.lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def strict_ordering :=  asymmetric r ∧ transitive r
--asymmetric: if a related b then b cannot be related to a
--less than or greater than are strict ordering
-- --> --> --> -->


def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r


def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬strongly_connected r


def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

def well_ordering := total_order r ∧ 
(
  ∀(s : set β), ∃(b:β),(∀(b':β), b' ∈ s → b ≺ b')
)
/-
well order:
total order and if you pick any subset has to have a least element,
gurantees set of objects youre recursing over will terminate
-/

end relation
end relations
