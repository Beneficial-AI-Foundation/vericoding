-- <vc-helpers>
-- </vc-helpers>

def countBits (n : Nat) : Nat := sorry
def sort_by_bit (arr : List Nat) : List Nat := sorry

theorem sort_by_bit_preserves_length (arr : List Nat) :
  arr.length > 0 → (sort_by_bit arr).length = arr.length := sorry

theorem sort_by_bit_maintains_order (arr : List Nat) (i : Nat) (h1 : arr.length > 0) 
  (h2 : i < (sort_by_bit arr).length - 1) : 
  let result := sort_by_bit arr
  let elem₁ := result.getD i 0
  let elem₂ := result.getD (i+1) 0
  countBits elem₁ < countBits elem₂ ∨
  (countBits elem₁ = countBits elem₂ ∧ elem₁ ≤ elem₂) := sorry

theorem sort_by_bit_idempotent (arr : List Nat) :
  sort_by_bit (sort_by_bit arr) = sort_by_bit arr := sorry

theorem sort_by_bit_edge_cases :
  sort_by_bit [0] = [0] ∧
  sort_by_bit [1, 1] = [1, 1] ∧ 
  sort_by_bit [2^32 - 1] = [2^32 - 1] := sorry

/-
info: [8, 6, 7, 15]
-/
-- #guard_msgs in
-- #eval sort_by_bit [7, 6, 15, 8]

/-
info: [1, 8, 3, 3, 5, 6, 9, 7]
-/
-- #guard_msgs in
-- #eval sort_by_bit [3, 8, 3, 6, 5, 7, 9, 1]

/-
info: [0, 2, 2, 4, 8, 8, 3, 5, 5, 6, 9, 7, 56]
-/
-- #guard_msgs in
-- #eval sort_by_bit [9, 4, 5, 3, 5, 7, 2, 56, 8, 2, 6, 8, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded