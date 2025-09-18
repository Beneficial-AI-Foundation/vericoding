-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_first_missing_positive (xs : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>