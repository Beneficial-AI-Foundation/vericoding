-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_rocket_stability (coeff : List Int) : Nat := sorry

theorem check_rocket_binary (coeff : List Int) : 
  check_rocket_stability coeff = 0 ∨ check_rocket_stability coeff = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_stable (zeros : List Int) :
  zeros.all (λ x => x = 0) → check_rocket_stability zeros = 1 := sorry

theorem single_coeff_stable (coeff : List Int) :
  coeff.length = 1 → check_rocket_stability coeff = 1 := sorry

theorem copy_safety (coeff : List Int) :
  check_rocket_stability coeff = 0 ∨ check_rocket_stability coeff = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval check_rocket_stability [10, 12, 4, 5, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval check_rocket_stability [0, 0, 0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval check_rocket_stability [5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded