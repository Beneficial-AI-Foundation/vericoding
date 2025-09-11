-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_drone_step (n : Nat) (R : Int) (H : List Int) : Nat :=
  sorry

variable (n : Nat) (R : Int) (H : List Int)
-- </vc-definitions>

-- <vc-theorems>
theorem max_drone_step_positive :
  n > 0 → H.length = n → max_drone_step n R H > 0 :=
  sorry

theorem max_drone_step_divides_distances : 
  n > 0 → H.length = n →
  ∀ h, h ∈ H → (h - R).natAbs % (max_drone_step n R H) = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_drone_step 3 1 [3, 5, 11]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_drone_step 2 4 [2, 8]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_drone_step 4 5 [1, 3, 7, 9]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible