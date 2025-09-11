-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lcm (a b : Nat) : Nat := sorry
def mn_lcm (m n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcm_properties {a b : Nat} (h1 : a > 0) (h2 : b > 0) :
  let result := lcm a b
  (result % a = 0) ∧ (result % b = 0) ∧ (result ≥ max a b) ∧ (result ≥ 0) := sorry

theorem mn_lcm_properties {m n : Nat} (h1 : m > 0) (h2 : n > 0) :
  let result := mn_lcm m n
  let lower := min m n
  let upper := max m n
  (∀ i, lower ≤ i → i ≤ upper → result % i = 0) ∧ (result ≥ upper) := sorry

theorem lcm_known_values :
  lcm 2 3 = 6 ∧ lcm 6 8 = 24 := sorry

theorem mn_lcm_order_invariant {m n : Nat} :
  mn_lcm m n = mn_lcm n m := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval mn_lcm 1 2

/-
info: 6
-/
-- #guard_msgs in
-- #eval mn_lcm 2 3

/-
info: 2520
-/
-- #guard_msgs in
-- #eval mn_lcm 1 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible