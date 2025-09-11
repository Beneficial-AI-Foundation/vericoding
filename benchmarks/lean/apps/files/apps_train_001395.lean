-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_xor_m (n : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_xor_m_no_solution (n : Nat) :
  find_smallest_xor_m n = -1 →
  ∀ m : Nat, m ≤ n + 2 → m ^^^ (m + 1) ≠ n :=
sorry

theorem find_smallest_xor_m_invalid_inputs (n : Int) :
  n ≤ 0 → find_smallest_xor_m n.toNat = -1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_smallest_xor_m 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_smallest_xor_m 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_smallest_xor_m 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible