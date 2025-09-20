-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pattern (n : Nat) : String := sorry

theorem pattern_lines_count {n : Nat} (h : n > 0) :
  ((pattern n).splitOn "\n").length == n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pattern_first_line_is_one {n : Nat} (h : n > 0) :
  ((pattern n).splitOn "\n").get! 0 == "1" := sorry

theorem pattern_line_structure {n : Nat} {i : Nat} (h₁ : n > 0) (h₂ : i > 1) (h₃ : i ≤ n) :
  let lines := (pattern n).splitOn "\n"
  let line := lines.get! (i - 1)
  line.startsWith "1" ∧ 
  line.endsWith (toString i) ∧
  line.length = i + (if i > 2 then i-2 else 0) := sorry
-- </vc-theorems>