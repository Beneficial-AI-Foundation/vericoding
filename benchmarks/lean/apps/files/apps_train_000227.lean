-- <vc-helpers>
-- </vc-helpers>

def find_first_missing_positive (xs : List Int) : Nat :=
  sorry

theorem find_first_missing_positive_is_positive
    {xs : List Int} :
    find_first_missing_positive xs > 0 :=
  sorry

theorem find_first_missing_positive_handles_duplicates
    {xs : List Int} :
    find_first_missing_positive xs = find_first_missing_positive (List.eraseDups xs) :=
  sorry

theorem find_first_missing_positive_continuity
    {xs : List Int} :
    let result := find_first_missing_positive xs
    ∀ i : Int, 1 ≤ i ∧ i < result → i ∈ xs :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_first_missing_positive [1, 2, 0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_first_missing_positive [3, 4, -1, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_first_missing_positive [7, 8, 9, 11, 12]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible