-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def count_signs_with_two_digits (k: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_signs_always_positive (k: Nat) (hk: k ≥ 1) (hk': k ≤ 1000):
  count_signs_with_two_digits k > 0 :=
  sorry

theorem count_signs_mod_property (k: Nat) (hk: k ≥ 1) (hk': k ≤ 1000):
  count_signs_with_two_digits k ≥ 0 ∧ count_signs_with_two_digits k < MOD :=
  sorry

theorem count_signs_doubles_each_k (k: Nat) (hk: k ≥ 1) (hk': k ≤ 10):
  count_signs_with_two_digits (k + 1) = ((count_signs_with_two_digits k) * 2) % MOD :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_signs_with_two_digits 1

/-
info: 20
-/
-- #guard_msgs in
-- #eval count_signs_with_two_digits 2

/-
info: 40
-/
-- #guard_msgs in
-- #eval count_signs_with_two_digits 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible