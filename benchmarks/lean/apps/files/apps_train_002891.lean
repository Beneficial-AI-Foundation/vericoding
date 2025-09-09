-- <vc-helpers>
-- </vc-helpers>

def Matrix (α : Type) := List (List α)

def trace (m : Matrix Int) : Option Int :=
  sorry

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

/-
info: 15
-/
-- #guard_msgs in
-- #eval trace [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

/-
info: None
-/
-- #guard_msgs in
-- #eval trace []

/-
info: None
-/
-- #guard_msgs in
-- #eval trace [[1, 2], [1, 2], [1, 2]]

-- Apps difficulty: introductory
-- Assurance level: unguarded