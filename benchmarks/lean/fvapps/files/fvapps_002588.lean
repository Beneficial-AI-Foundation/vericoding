-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pyramid (n : Nat) : String := sorry

def String.stripRight (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pyramid_empty_newline : pyramid 0 = "\n" := sorry

theorem pyramid_single_level : pyramid 1 = "/\\\n" := sorry

theorem pyramid_ends_with_newline {n : Nat} : 
  (pyramid n).endsWith "\n" := sorry 

theorem pyramid_line_structure {n : Nat} (h : n > 0) :
  let lines := (pyramid n).splitOn "\n"
  ∀ i < n,
  let line := (lines.get! i)
  let content := line.trim
  content.front = '/' ∧ 
  content.back = '\\' := sorry

theorem pyramid_last_line_underscores {n : Nat} (h : n > 1) :
  let lines := (pyramid n).splitOn "\n"
  let lastLine := lines.get! (n-1)
  lastLine.contains '_' := sorry
-- </vc-theorems>