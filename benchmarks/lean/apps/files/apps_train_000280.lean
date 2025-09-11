-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_beautiful_arrangements (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_beautiful_arrangements_positive (n : Nat)
    (h : n > 0 ∧ n ≤ 15) :
    count_beautiful_arrangements n > 0 := sorry

theorem count_beautiful_arrangements_increasing
    {n₁ n₂ : Nat} (h₁ : n₁ > 0 ∧ n₁ ≤ 15) (h₂ : n₂ > 0 ∧ n₂ ≤ 15)
    (h₃ : n₁ < n₂) :
    count_beautiful_arrangements n₁ < count_beautiful_arrangements n₂ := sorry 

theorem count_beautiful_arrangements_undefined (n : Nat)
    (h : n = 0 ∨ n > 15) :
    count_beautiful_arrangements n = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_beautiful_arrangements 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_beautiful_arrangements 3

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_beautiful_arrangements 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible