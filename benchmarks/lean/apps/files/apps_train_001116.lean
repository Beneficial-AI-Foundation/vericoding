-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_imposter (n : Nat) (base : List Int) (game : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_imposter_correct (base : List Int) (imposter : Int) :
  imposter ∉ base →  -- assume imposter not in base list
  find_imposter (base.length) base (base ++ [imposter]) = imposter := by  
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_imposter 3 [4, 2, 5] [4, 2, 3, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_imposter 2 [1, 1] [1, 1, 2]

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_imposter 1 [5] [5, 5]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded