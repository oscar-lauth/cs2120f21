import algebra.algebra.basic tactic.ring

/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
(P : Prop) := ∀(n m:ℕ), m < n → P m → P n. ∀P ∀n

#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs.

Informal proof of #2:
We will define a function sum_to_sq n that returns the sum of the squares of natural numbers from 0 to any natural number n.
Then the property, P(n) that we want to
show holds for every natural number, n, is
that sum_to_sq n = (1/6)n(1+n)(1+2n)
By induction applied to proofs of the 
two lemmas, P(0), and ∀ n', P(n') → P(n'+1). 

Lemma 1: P(0). Both sum_to_sq 0 and (1/6) * 0 * (1) * (1) are both equal
to 0, and so are equal. Thus P(0) holds true.

Lemma 2: Assume n' is arbitrary and that we
know P(n') holds true, such that sum_to_sq n' = (1/6)n'(1+n')(1+2n').
Our goal is now to show sum_to_sq (n'+1) = (1/6)(n'+1)(2+n')(3+2n').

Observe that sum_to_sq (n'+1) = sum_to_sq n' + (n'+1)*(n'+1).
Rewriting using our induction hypothesis we have
sum_to_sq (n'+1) = (1/6)n'(1+n')(1+2n') + (n'+1)*(n'+1). 
Distributing, we have sum_to_sq (n'+1) = (1/6)(n'+3n'^2+2n'^3)+(n'^2+2n'+1)
Adding like terms, we have sum_to_sq (n'+1) = 1+(13/6)n'+(3/2)n'^2+(1/3)n'^3
Factoring a (1/6)(n'+1), we have sum_to_sq (n'+1) = (1/6)(n'+1)(2n'^2+7n'+6).
Factoring the quadratic, we have sum_to_sq (n'+1) = (1/6)(n'+1)(2n'+3)(n'+2).
This matches our goal of sum_to_sq (n'+1). Thus, P(n'+1) holds true.

We've thus shown that if P holds for n' then it
holds for (n'+1). With this case and the base 
case proved, we apply induction to get our final
result, a proof of P(n) for arbitrary n, which
is to say, ∀ n, P n. QED. 
-/




/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
-/
--Formal Proof of #2
def sum_to_sq : ℕ → ℕ --function that sums the squares of nats from 0 to n
| (nat.zero)    := nat.zero                  
| (nat.succ n')  := (sum_to_sq n') + (n'.succ)*(n'.succ) 

#reduce sum_to_sq 6 --checking function is working

def P : ℕ → Prop :=  --Prop to be proven for #2
  λ n, 6 * sum_to_sq n = n*(1 + n)*(1 + 2*n)

theorem sum_to_squares: ∀ n, P n :=
begin
  assume n,
  unfold P,
  induction n with n' ih_n',
  apply rfl,
  simp [sum_to_sq],   
  rw mul_add, 
  rw ih_n',   
  rw nat.succ_eq_add_one,
  ring,    
end
/-
#2: Formal or detailed informal proofs 10-13
In order to write inductive proofs about the properties of addition and multiplication, we must recursively define these operations.
-/
def add : ℕ → ℕ → ℕ  
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)

def mul : ℕ → ℕ → ℕ
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)

-- Formal Proof of #10
--Due to recursively defining add and mul, we write a proof for a lemma that add n 0 = n. This will assist us in proving #10.

lemma add_right_zero: ∀(m:ℕ), add m 0 = m:=
  begin
    assume m,
    induction m with m' ih_m',
    refl,
    simp[add],
    exact ih_m',
  end
--Formal Proof of #10
example: ∀ (n:ℕ), mul 1 n = n:= --proof of 1 * n = n
begin
  assume n,
  induction n with n' ih_n',
  refl,
  rw nat.succ_eq_add_one,
  simp[mul],
  apply add_right_zero,
end

--#11 Informal Proof
/-
Let P be a property defined by m * (n + k) = (m * n) + (m * k). To show P holds for all natural numbers m,n,k
we can apply induction to proofs of two lemmas, one with P(0) (base case),
and another case such that ∀ k', P(k') → P(k'+1).

Lemma 1: P(0). m * (n + 0) = m * n + m * 0.
By the defintions of addition and multiplication, we have  m * n = m * n. Both sides are equal and thus P(0) holds true.

Lemma 2: Assume k' is arbitrary and that we know P(k') holds true, such that m * (n + k') = m * n + m * k'.
Our goal is now to show P(k'+1): m * (n + (k' + 1)) = m * n + m * (k' + 1).
By the defintions of addition and multiplication, we have m * (n + k') + m = (m * n) + m * (k' + 1).
Rewriting our goal with the inductive hypothesis P(k'), we have (m * n) + (m * k') + m = (m * n) + (m * (k' + 1)).
Using basic principles of addition and multiplication, we have (m * n) + m * (k' + 1) = (m * n) + (m * (k' + 1)).
Both sides are equal and thus P(k'+1) holds true.

With our base case and inductive case proven, we can apply induction to prove ∀(m n k:ℕ), m * (n + k) = (m * n) + (m * k) is true. QED.
-/


--#12 Informal Proof
/-
Let P be a property defined by m * (n * k) = (m * n) * k. To show P holds for all natural numbers m,n,k
we can apply induction to proofs of two lemmas, one with P(0) (base case),
and another case such that ∀ k', P(k') → P(k'+1).

Lemma 1: P(0). m * (n * 0) = (m * n) * 0. Both sides are equal to 0, and thus P(0) holds true.

Lemma 2: Assume k' is arbitrary and that we know P(k') holds true, such that m * (n * k') = (m * n) * k'.
Our goal is now to show P(k'+1): m * (n * (k'+1)) = (m * n) * (k'+1).
Using the properties of multiplicative identity and distribution over addition proven above, we have m * ((n * k) + n) = (m * n) * (k'+1).
Using left distributivity again, we have (m * (n * k')) + m * n = (m * n) * (k'+1).
Rewriting our goal with the inductive hypothesis P(k'), we have ((m * n) * k') + m * n = (m * n) * (k'+1).
Using basic principles of addition and multiplication, we have (m * n) * (k' + 1) = (m * n) * (k'+1).
Both sides are equal and thus P(k'+1) holds true.

With our base case and inductive case proven, we can apply induction to prove ∀(m n k:ℕ), m * (n * k) = (m * n) * k is true. QED.
-/


--#13 Informal Proof

/-
Let P be a property defined by m * n = n * m. To show P holds for all natural numbers m,n
we can apply induction to proofs of two lemmas, one with P(0) (base case),
and another case such that ∀ n', P(n') → P(n'+1).

Lemma 1: P(0). m * 0 = 0 * m. Both sides are equal to 0, and thus P(0) holds true.

Lemma 2: Assume n' is arbitrary and that we know P(n') holds true, such that m * n' = n' * m.
Our goal is now to show P(n'+1): m * (n'+1) = (n'+1) * m.
Using the properties of multiplicative identity and distribution over addition proven above, we have m * n' + m = (n'+1) * m.
Rewriting our goal with the inductive hypothesis, we have n' * m + m = (n'+1) * m. Using basic principles of addition and multiplication,
we have (n' + 1) * m = (n'+1) * m.
Both sides are equal and thus P(n'+1) holds true.

With our base case and inductive case proven, we can apply induction to prove ∀(m n:ℕ), m * n = n * m is true. QED.
-/
/-
#3 (Extra Credit): #5 or #9
-/
--#5
def fib: ℕ → ℕ 
| (nat.zero):= nat.zero
| (nat.succ nat.zero) := nat.succ nat.zero                 
| (nat.succ(nat.succ n'))  := fib n' + fib (nat.succ n')

#reduce fib 14

def F : ℕ → Prop := 
  λ n, (fib (n+1))^2 - (fib (n+2) * fib(n)) = (0-1)^(n)

theorem cassini : ∀n, F n :=
begin
  assume n,
  unfold F,
  induction n with n' ih_n',
  apply refl,
  simp[fib],
  rw nat.succ_eq_add_one,
  ring_nf,
  sorry,
end


/-
NOT FINALIZED. ADVISORY. 
-/