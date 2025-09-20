-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_cleaner (seq : List Int) : List Int × List Nat := sorry

theorem binary_cleaner_properties (seq : List Int) :
  let result := binary_cleaner seq
  (∀ x ∈ result.1, x < 2) ∧
  (∀ i ∈ result.2, i < seq.length) ∧
  (List.all result.2 fun i => seq.get! i ≥ 2) ∧
  result.1.length + result.2.length = seq.length := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>