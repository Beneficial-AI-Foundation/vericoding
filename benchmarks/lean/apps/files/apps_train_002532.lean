-- <vc-preamble>
def addsup (a1 a2 a3 : List Int) : List (Int × Int × Int) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compare_arrays (arr1 arr2 : List (List Int)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem addsup_empty_input
  (a1 a2 a3 : List Int)
  : (a1 = [] ∨ a2 = []) → addsup a1 a2 a3 = [] :=
  sorry
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible