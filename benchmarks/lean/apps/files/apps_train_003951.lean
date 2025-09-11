-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divisors (n : Nat) : List Nat := sorry

theorem divisors_all_divide (n : Nat) (h : n ≥ 2) :
  ∀ d ∈ divisors n, n % d = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divisors_increasing (n : Nat) (h : n ≥ 2) :
  ∀ i j, i < j → i < (divisors n).length → j < (divisors n).length → 
    (divisors n).get! i < (divisors n).get! j := sorry

theorem divisors_contains_one_and_self (n : Nat) (h : n ≥ 2) :
  divisors n ≠ [] ∧ 
  List.head! (divisors n) = 1 ∧ 
  List.getLast! (divisors n) = n := sorry

theorem divisors_unique (n : Nat) (h : n ≥ 2) :
  List.Nodup (divisors n) := sorry

theorem divisors_complementary_pairs (n : Nat) (h : n ≥ 2) (k : Nat) :
  k ∈ divisors n → k * k ≤ n → k * (n / k) = n := sorry

/-
info: '1-sum'
-/
-- #guard_msgs in
-- #eval solve 3

/-
info: '3-altsum'
-/
-- #guard_msgs in
-- #eval solve 7

/-
info: '1-altsum'
-/
-- #guard_msgs in
-- #eval solve 11

/-
info: '3-sum'
-/
-- #guard_msgs in
-- #eval solve 37
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded