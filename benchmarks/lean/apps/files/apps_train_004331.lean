-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def decompose : Int → List Nat × Int := sorry

/- Decompose function's list result contains only numbers greater than 1 -/
-- </vc-definitions>

-- <vc-theorems>
theorem decompose_result_gt_one (n : Int) :
  let (result, _) := decompose n
  ∀ k ∈ result, k > 1 := sorry

/- Decompose function's remainder is non-negative -/

theorem decompose_remainder_nonneg (n : Int) :
  let (_, remainder) := decompose n
  remainder ≥ 0 := sorry

/- The decomposition recomposes back to the original number -/

theorem decompose_recompose (n : Int) :
  let (result, remainder) := decompose n
  let recomposed := remainder + (List.foldl (fun acc (i, k) => acc + (i + 2)^k) 0 
    (List.zip (List.range result.length) result))
  recomposed = n := sorry

/- Negative inputs return empty list and same number as remainder -/

theorem decompose_negative (n : Int) :
  n < 0 →
  decompose n = ([], n) := sorry

/- Small inputs (0,1) return empty list and same number -/

theorem decompose_small_inputs (n : Int) :
  n = 0 ∨ n = 1 →
  decompose n = ([], n) := sorry

/-
info: [[], 3]
-/
-- #guard_msgs in
-- #eval decompose 3

/-
info: [[4, 2], 1]
-/
-- #guard_msgs in
-- #eval decompose 26

/-
info: [[], 0]
-/
-- #guard_msgs in
-- #eval decompose 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded