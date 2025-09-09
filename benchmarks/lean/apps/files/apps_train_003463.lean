-- <vc-helpers>
-- </vc-helpers>

def solve (arr : List Nat) : Option (List Nat) := sorry

theorem solve_preserves_length {arr : List Nat} {result : List Nat} :
  solve arr = some result → result.length = arr.length := sorry

theorem solve_preserves_elements {arr : List Nat} {result : List Nat} :
  solve arr = some result → 
  ∀ x, x ∈ arr ↔ x ∈ result := sorry

theorem solve_adjacent_pairs_rule {arr : List Nat} {result : List Nat} :
  solve arr = some result →
  ∀ i, i < result.length - 1 → 
    (result[i]! * 2 = result[i+1]! ∨ result[i]! = result[i+1]! * 3) := sorry

theorem solve_duplicates {arr : List Nat} :
  ¬arr.Nodup → solve arr = none := sorry 

theorem solve_empty :
  solve [] = none := sorry

theorem solve_single (n : Nat) :
  solve [n] = some [n] := sorry

/-
info: [9, 3, 6, 12, 4, 8]
-/
-- #guard_msgs in
-- #eval solve [12, 3, 9, 4, 6, 8]

/-
info: [2, 4]
-/
-- #guard_msgs in
-- #eval solve test2

/-
info: [279, 558, 1116, 2232, 744, 1488]
-/
-- #guard_msgs in
-- #eval solve test3

-- Apps difficulty: introductory
-- Assurance level: unguarded