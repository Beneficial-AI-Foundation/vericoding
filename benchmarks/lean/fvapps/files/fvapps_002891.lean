-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (α : Type) := List (List α)

def trace (m : Matrix Int) : Option Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem trace_square_matrix {m : List (List Int)} 
  (h : ∀ (l : List Int), List.elem l m → l.length = m.length) 
  (h' : m.length > 0) :
  ∃ result, trace m = some result ∧ 
    result = (List.range m.length).foldr (λ i acc => acc + ((m.get! i).get! i)) 0 :=
  sorry

theorem trace_non_square_matrix {m : List (List Int)}
  (h : ∃ (l : List Int), List.elem l m ∧ l.length ≠ m.length) :
  trace m = none :=
  sorry

theorem trace_empty_matrix :
  trace ([] : Matrix Int) = none :=
  sorry

theorem trace_empty_row :
  trace [[]] = none :=
  sorry
-- </vc-theorems>