-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_one_out (s : String) : List Char := sorry

theorem odd_one_out_output_valid (s : String) :
  let result := odd_one_out s
  -- All elements are characters from input string
  (∀ c ∈ result, c ∈ s.data) ∧
  -- Each character appears odd times in original
  (∀ c ∈ result, (s.data.count c) % 2 = 1) ∧
  -- No duplicates
  result.Nodup := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_one_out_nonempty (s : String) (h : s ≠ "") :
  let result := odd_one_out s
  (∃ c ∈ s.data, (s.data.count c) % 2 = 1) →
  result ≠ [] := by sorry

theorem odd_one_out_complete (s : String) :
  let result := odd_one_out s
  result.length = (s.data.filter (fun c => (s.data.count c) % 2 = 1)).length := by sorry
-- </vc-theorems>