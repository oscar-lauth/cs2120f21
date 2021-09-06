-- single-line comment
/-
multi-line comment
-/

theorem eq_symm : 
  ∀ (T : Type) (x y : T), x = y → y = x :=
    begin
      assume (T : Type),
      assume (x y : T),
      assume (e : x = y), --assume to have proof of x=y
      rw e, --sub x=y in y=x then by axiom of reflex. y=y is true QED
    end

/-
Theorem: Equality is symmetric
show that if x=y, y=x.
Assume T is any type and x and y are objects of type T. It must be shown that if x=y then y=x. 
Assuming x=y, it remains to be proved that y=x. By applying the axiom of substitutability of equals,
we can rewrite x in the goal of y such that x=y becomes y=y. 
By applying the axiom of reflexitivity of equals, y=y is true. QED.
-/

theorem eq_trans :
  ∀ (T : Type) (x y z: T), x = y → y = z → x = z :=
    begin
      assume (T : Type), --assume T,
      assume (x y z : T), --assume x y z,
      assume (e : x = y),
      rw e,
      assume (c : y = z), 
      exact c,
    end

--z=x
theorem eq_trans_reverse :
  ∀ (T : Type) (x y z: T), x = y → y = z → z = x :=
    begin
      assume (T : Type), --assume T,
      assume (x y z : T), --assume x y z,
      assume (e : x = y),
      rw e,
      assume (e2 : y = z),
      rw e2,
      

    end

