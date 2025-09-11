-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prime (n : Nat) : Bool := sorry

def prime_bef_aft (n : Nat) : Nat × Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem prime_bef_aft_bound {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  p1 < n ∧ n < p2 := sorry

theorem prime_bef_aft_primes {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  prime p1 = true ∧ prime p2 = true := sorry

theorem prime_bef_aft_nat {n : Nat} (h : n ≥ 4) (h2 : n ≤ 1000) :
  let (p1, p2) := prime_bef_aft n
  p1 ≥ 0 ∧ p2 ≥ 0 := sorry

theorem prime_divisibility {n : Nat} (h : n ≥ 2) (h2 : n ≤ 100) :
  prime n = true ↔ ∀ i : Nat, 2 ≤ i → i < n → n % i ≠ 0 := sorry

theorem composite_divisibility {n : Nat} (h : n ≥ 2) (h2 : n ≤ 100) :
  prime n = false → ∃ i : Nat, 2 ≤ i ∧ i < n ∧ n % i = 0 := sorry

/-
info: [97, 101]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 100

/-
info: [89, 101]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 97

/-
info: [97, 103]
-/
-- #guard_msgs in
-- #eval prime_bef_aft 101
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded