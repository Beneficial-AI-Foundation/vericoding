-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def even_numbers_before_fixed (sequence : List Int) (fixed : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem not_found_returns_neg_one (sequence : List Int) (fixed : Int) : 
  ¬(fixed ∈ sequence) → even_numbers_before_fixed sequence fixed = -1 :=
  sorry

theorem count_evens_before_first_occurrence (sequence : List Int) (fixed : Int) :
  fixed ∈ sequence →
  even_numbers_before_fixed sequence fixed = 
    ((sequence.take (sequence.findIdx (· = fixed))).filter (·.mod 2 = 0)).length :=
  sorry

theorem result_is_nonneg_when_found (sequence : List Int) (fixed : Int) :
  fixed ∈ sequence →
  even_numbers_before_fixed sequence fixed ≥ 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval even_numbers_before_fixed [1, 4, 2, 6, 3, 1] 6

/-
info: -1
-/
-- #guard_msgs in
-- #eval even_numbers_before_fixed [2, 2, 2, 1] 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval even_numbers_before_fixed [1, 3, 4, 3] 3
-- </vc-theorems>