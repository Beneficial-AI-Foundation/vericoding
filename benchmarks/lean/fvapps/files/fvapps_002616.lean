-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (lst : List Int) : String := sorry

theorem output_format (lst : List Int) (h : lst.length ≥ 3) :
  let result := solve lst
  result = "A" ∨ result = "D" ∨ result = "RA" ∨ result = "RD" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rotation_property (lst : List Int) (h : lst.length ≥ 3) :
  let original_result := solve lst
  let rotated := lst.tail ++ [lst.head!]
  let rotated_result := solve rotated
  (original_result = "A" ∨ original_result = "D") →
  (rotated_result = "RA" ∨ rotated_result = "RD") := sorry
-- </vc-theorems>