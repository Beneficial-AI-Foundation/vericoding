-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interleave {α : Type} : List α → List α → List α 
  | l, [] => l
  | [], l => l
  | (x::xs), (y::ys) => x :: y :: interleave xs ys
-- </vc-definitions>

-- <vc-theorems>
theorem interleave_single_list {α : Type} (lst : List α) : 
  interleave lst [] = lst := by sorry

theorem interleave_length {α : Type} (l₁ l₂ : List α) :
  List.length (interleave l₁ l₂) = 2 * max (List.length l₁) (List.length l₂) := by sorry

theorem interleave_elements {α : Type} [Inhabited α] (l₁ l₂ : List α) (i : Nat) :
  i < List.length l₁ → List.get! (interleave l₁ l₂) (2*i) = List.get! l₁ i := by sorry

theorem interleave_elements_second {α : Type} [Inhabited α] (l₁ l₂ : List α) (i : Nat) :
  i < List.length l₂ → List.get! (interleave l₁ l₂) (2*i + 1) = List.get! l₂ i := by sorry

theorem interleave_empty_left {α : Type} : 
  interleave ([] : List α) [] = [] := by sorry

theorem interleave_empty_right {α : Type} :
  interleave [] ([] : List α) = [] := by sorry

/-
info: [1, 'c', 2, 'd', 3, 'e']
-/
-- #guard_msgs in
-- #eval interleave [1, 2, 3] ["c", "d", "e"]

/-
info: [1, 4, 2, 5, 3, None]
-/
-- #guard_msgs in
-- #eval interleave [1, 2, 3] [4, 5]

/-
info: [1, 4, 7, 2, 5, 8, 3, 6, 9]
-/
-- #guard_msgs in
-- #eval interleave [1, 2, 3] [4, 5, 6] [7, 8, 9]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded