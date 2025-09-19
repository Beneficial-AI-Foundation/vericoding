-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def modify_operators (lines : List String) : String := sorry

theorem preserves_string_without_operators {lines : List String} 
  (h : lines ≠ []) 
  (h2 : ∀ l ∈ lines, ¬ l.data.contains '&' ∧ ¬ l.data.contains '|') :
  modify_operators lines = String.join lines := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem converts_all_operators {lines : List String}
  (h : lines ≠ [])
  (h2 : ∀ l ∈ lines, ∃ s1 s2 : String, l = s1 ++ " && " ++ s2 ∨ l = s1 ++ " || " ++ s2) :
  ¬ (modify_operators lines).data.contains '&' ∧
  ¬ (modify_operators lines).data.contains '|' := sorry

theorem idempotent (lines : List String) (h : lines ≠ []) :
  let first := modify_operators lines
  let second := modify_operators (first.splitOn "\n")
  first = second := sorry
-- </vc-theorems>