-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumOfDivisors (n : Int) : Int :=
  sorry

def abundant (n : Int) : Option (List (List Int)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem abundant_output_structure
  (h : Int)
  (h_ge : h ≥ 12)
  (h_le : h ≤ 1000)
  (result : List (List Int))
  (h_result : abundant h = some result) :
  result.length = 2 ∧
  ∀ sublist ∈ result, sublist.length = 1 ∧
  ∀ sublist ∈ result, ∀ x ∈ sublist, x ≥ 0 :=
sorry

theorem abundant_properties
  (h : Int)
  (h_ge : h ≥ 12)
  (h_le : h ≤ 1000)
  (result : List (List Int))
  (h_result : abundant h = some result)
  (n : Int := (result.get! 0).get! 0)
  (diff : Int := (result.get! 1).get! 0) :
  n ≤ h ∧
  n > 0 ∧
  sumOfDivisors n > n ∧
  sumOfDivisors n - n = diff :=
sorry
-- </vc-theorems>