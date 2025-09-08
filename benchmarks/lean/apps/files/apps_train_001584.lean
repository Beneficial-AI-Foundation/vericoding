/-
## Task

Given a positive integer, `n`, return the number of possible ways such that `k` positive integers multiply to `n`. Order matters.

**Examples**
```
n = 24
k = 2
(1, 24), (2, 12), (3, 8), (4, 6), (6, 4), (8, 3), (12, 2), (24, 1) -> 8

n = 100
k = 1
100 -> 1

n = 20
k = 3
(1, 1, 20), (1, 2, 10), (1, 4, 5), (1, 5, 4), (1, 10, 2), (1, 20, 1),
(2, 1, 10), (2, 2, 5), (2, 5, 2), (2, 10, 1), (4, 1, 5), (4, 5, 1),
(5, 1, 4), (5, 2, 2), (5, 4, 1), (10, 1, 2), (10, 2, 1), (20, 1, 1) -> 18
```
**Constraints**
`1 <= n <= 500_000_000`
and `1 <= k <= 1000`
-/

def multiply (n k: Nat) : Nat := sorry

theorem multiply_positive (n k: Nat) 
  (h1: n > 0) (h2: k > 0) : multiply n k > 0 :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def isPrime (n: Nat) : Bool := sorry

theorem multiply_one (k: Nat)
  (h: k > 0) : multiply 1 k = 1 :=
sorry

theorem multiply_k1_is_one (n: Nat)
  (h: n > 0) : multiply n 1 = 1 :=
sorry

theorem multiply_monotone_k (n k: Nat)
  (h1: n > 0) (h2: k > 1) : 
  multiply n k ≥ multiply n (k-1) :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval multiply 24 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval multiply 100 1

/-
info: 18
-/
-- #guard_msgs in
-- #eval multiply 20 3

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible