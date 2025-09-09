def addsup (a1 a2 a3 : List Int) : List (Int × Int × Int) :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def compare_arrays (arr1 arr2 : List (List Int)) : Bool :=
  sorry

theorem addsup_empty_input
  (a1 a2 a3 : List Int)
  : (a1 = [] ∨ a2 = []) → addsup a1 a2 a3 = [] :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible