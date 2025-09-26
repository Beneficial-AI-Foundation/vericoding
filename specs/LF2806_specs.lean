-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitByValue (k : Int) (elements : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem preserves_elements (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  result.length = elements.length ∧
  ∀ x, (result.count x) = (elements.count x) :=
  sorry

theorem correct_partitioning (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  let splitPoint := (List.filter (· < k) result).length
  (List.take splitPoint result).all (· < k) ∧
  (List.drop splitPoint result).all (· ≥ k) :=
  sorry

theorem maintains_relative_order (k : Int) (elements : List Int) :
  let result := splitByValue k elements
  List.filter (· < k) result = List.filter (· < k) elements ∧ 
  List.filter (· ≥ k) result = List.filter (· ≥ k) elements :=
  sorry
-- </vc-theorems>