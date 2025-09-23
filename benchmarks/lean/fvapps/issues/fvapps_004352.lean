-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transpose {α : Type u} [Inhabited α] : Matrix α → Matrix α
  | Matrix.mk m => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem transpose_dimensions {α : Type u} [Inhabited α] {m : List (List α)} 
    (h1 : m.length > 0) 
    (h2 : m.head!.length > 0)
    (h3 : ∀ row ∈ m, row.length = m.head!.length) :
  let t := transpose (Matrix.mk m)
  match t with
  | Matrix.mk t' =>
    t'.length = m.head!.length ∧
    t'.head!.length = m.length := by sorry

theorem transpose_involution {α : Type u} [Inhabited α] {m : List (List α)}
    (h1 : m.length > 0)
    (h2 : m.head!.length > 0)
    (h3 : ∀ row ∈ m, row.length = m.head!.length) :
  transpose (transpose (Matrix.mk m)) = Matrix.mk m := by sorry

theorem transpose_element_relationship {α : Type u} [Inhabited α] {m : List (List α)}
    (h1 : m.length > 0)
    (h2 : m.head!.length > 0)
    (h3 : ∀ row ∈ m, row.length = m.head!.length)
    (i : Nat) (j : Nat)
    (hi : i < m.length)
    (hj : j < m.head!.length) :
  (m.get! i).get! j = ((match transpose (Matrix.mk m) with | Matrix.mk t => t).get! j).get! i := by sorry

theorem single_row_transpose {α : Type u} [Inhabited α] (row : List α)
    (h : row.length > 0) :
  let m := Matrix.mk [row]
  let t := transpose m
  match t with
  | Matrix.mk t' =>
    t'.length = row.length ∧
    (∀ col ∈ t', col.length = 1) ∧
    (List.map (λ col => col.head!) t' = row) := by sorry

theorem single_element_transpose {α : Type u} [Inhabited α] (x : α) :
  transpose (Matrix.mk [[x]]) = Matrix.mk [[x]] := by sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval transpose [[1]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval transpose [[1, 2, 3]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval transpose [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- </vc-theorems>