-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def smaller (arr : List Int) : List Int := sorry

theorem smaller_length_matches_input (arr : List Int) (h : arr ≠ []) :
  List.length (smaller arr) = List.length arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem smaller_returns_non_negative (arr : List Int) (h : arr ≠ []) :
  ∀ x ∈ smaller arr, x ≥ 0 := sorry

theorem smaller_last_always_zero (arr : List Int) (h : arr ≠ []) :
  List.get! (smaller arr) (List.length arr - 1) = 0 := sorry

theorem smaller_count_correct (arr : List Int) (h : arr ≠ []) :
  ∀ i, i < List.length arr →
    List.get! (smaller arr) i = 
      (List.drop (i+1) arr).countP (· < List.get! arr i) := sorry

theorem smaller_maximum_constraint (arr : List Int) (h : arr ≠ []) :
  ∀ i, i < List.length arr →
    List.get! (smaller arr) i ≤ List.length arr - i - 1 := sorry

/-
info: [4, 3, 2, 1, 0]
-/
-- #guard_msgs in
-- #eval smaller [5, 4, 3, 2, 1]

/-
info: [1, 1, 0]
-/
-- #guard_msgs in
-- #eval smaller [1, 2, 0]

/-
info: [0, 0, 0]
-/
-- #guard_msgs in
-- #eval smaller [1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible