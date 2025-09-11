-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_positives_sum_negatives (arr : List Int) : List Int := sorry

theorem count_positives (arr : List Int) :
  arr ≠ [] → 
  (count_positives_sum_negatives arr).get! 0 = 
    (arr.filter (fun x => x > 0)).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_negatives (arr : List Int) :
  arr ≠ [] →
  (count_positives_sum_negatives arr).get! 1 = 
    (arr.filter (fun x => x < 0)).foldl (· + ·) 0 := sorry

/-
info: [10, -65]
-/
-- #guard_msgs in
-- #eval count_positives_sum_negatives [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, -11, -12, -13, -14, -15]

/-
info: [8, -50]
-/
-- #guard_msgs in
-- #eval count_positives_sum_negatives [0, 2, 3, 0, 5, 6, 7, 8, 9, 10, -11, -12, -13, -14]

/-
info: []
-/
-- #guard_msgs in
-- #eval count_positives_sum_negatives []
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible