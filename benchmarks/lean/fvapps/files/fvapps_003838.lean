-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number (lines : List String) : List String := sorry 

theorem number_same_length (lines : List String) :
  (number lines).length = lines.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem number_format_get {lines : List String} {i : Nat} (h : i < lines.length) :
  (number lines).get ⟨i, by {
    rw [number_same_length]
    exact h
  }⟩ = s!"{i+1}: {lines.get ⟨i, h⟩}" := sorry

theorem number_handles_all_strings {lines : List String} :
  number lines = List.map (fun i => s!"{i+1}: {lines.get ⟨i, by sorry⟩}") 
    (List.range lines.length) := sorry

theorem number_empty_input :
  number [] = [] := sorry
-- </vc-theorems>