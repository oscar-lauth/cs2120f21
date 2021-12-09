example: (∀ n: ℕ 

--2^(n'+1) = 2^n' * 2

| nat.zero := 1
| nat.succ := 2*p(n')

/-
By induction,
P 0 = 1
∀ n', P n' → P(n'+1)
assume n'
assume ind_hypothesis for P(n'): 1+2+...+2^n' = 2^n'+1  -1
show P(n'+1) = 1+2+..+2^n' + 2^(n'+1)=2^(n'+1+1) -1
rw with ind_hypothesis, 2^n'+1 -1 + 2^(n'+1)=2^(n'+2) -1
ring, 2*(2^(n'+1))=2^(n'+1+1)=2^(n'+1)*2^1
2^(n'+2)=2^(n'+2), QED


for all sets, if cardinality of set is n, then cardinality of power set is 2^n

P n: ∀ sets with n elements, power set has 2^n elements
prove P 0 : a set with 0 elements contains 1 subset, the empty set 1=2^n, n=0
assume set of size n' has power set size of 2^n' <--induction hypothesis
show set of size n'+1 has power set size of 2^(n'+1), <--goal
2 cases: 
-subsets without new element, 2^n'
-subsets with new element, 2^n'
size of power set = 2^n' + 2^n' = 2*2^n' = 2^(n'+1), QED
-/