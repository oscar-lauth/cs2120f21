import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type
| zero : nat
| succ (n' : nat) : nat

def z := nat.zero
#check z
#reduce z

def o := nat.succ z

def t := nat.succ o
#check t
#reduce t

def f : nat := 
begin
  exact nat.succ (nat.succ t)
end

def inc' : nat → nat :=
begin
  assume n,
  exact nat.succ n,
end
#reduce inc' f --5

def inc : nat → nat 
| n := nat.succ n

#reduce inc f --5

def dec : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := n'

#reduce dec f --3

def add : nat → nat → nat 
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ(add n' m) --answer for n'

#reduce add f t --6

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add m (mul n' m)

#reduce mul f f --16

def exp : nat → nat → nat 
| (nat.zero) (m) := nat.zero
| (n) (nat.zero) := nat.zero.succ
| (n) (nat.succ m') := mul n (exp n m')

#reduce exp f t --16

def sum_to : nat → nat
|(nat.zero) := nat.zero
|(nat.succ n') := add (nat.succ(n')) (sum_to n')

#reduce sum_to f --10

def P : nat → Prop
|n:= mul t (sum_to n) = mul n (inc n)


end hidden

def P : nat → Prop
|n:= hidden.sum_to n = mul n (inc n)

theorem foo : ∀(n : ℕ), P n :=