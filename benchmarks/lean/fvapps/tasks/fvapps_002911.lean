-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.transpose {α : Type} : List (List α) → List (List α)
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_matrix_transpose {α : Type} :
  @List.transpose α [[]] = [[]] := by sorry

theorem transpose_dimensions_correct {α : Type} (m : List (List α)) 
  (h1 : m.length > 0) (h2 : (m[0]!).length > 0) 
  (h3 : ∀ i < m.length, (m[i]!).length = (m[0]!).length) :
  let t := List.transpose m
  (t.length = (m[0]!).length) ∧ 
  (t[0]!.length = m.length) := by sorry

theorem double_transpose_identity {α : Type} (m : List (List α))
  (h1 : m.length > 0) (h2 : (m[0]!).length > 0)
  (h3 : ∀ i < m.length, (m[i]!).length = (m[0]!).length) :
  List.transpose (List.transpose m) = m := by sorry
-- </vc-theorems>