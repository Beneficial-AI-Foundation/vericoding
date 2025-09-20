-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Int) : String := sorry

theorem pattern_nonpos {n : Int} (h : n ≤ 0) : 
  pattern n = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_line_structure {n : Int} (h : n > 0) (i : Nat) (h2 : i < n) :
  let lines := (pattern n).splitOn "\n"
  let expected_num := 2 * i + 1
  lines[i]! = String.mk (List.replicate expected_num (toString expected_num).data[0]!) := sorry

theorem pattern_examples : 
  pattern 0 = "" ∧ 
  pattern (-1) = "" ∧
  pattern 4 = "1\n333" ∧
  pattern 5 = "1\n333\n55555" := sorry
-- </vc-theorems>