-- <vc-preamble>
def solve_polygon (grid : List (List Nat)) : List (Nat × Nat) := sorry 

def isConvex (polygon : List (Nat × Nat)) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replaceNth {α : Type} (xs : List α) (n : Nat) (v : α) : List α :=
  match n, xs with
  | _, [] => []
  | 0, x::xs => v::xs 
  | n+1, x::xs => x :: replaceNth xs n v
-- </vc-definitions>

-- <vc-theorems>
theorem square_shape_valid (size : Nat) (h1 : size ≥ 7) (h2 : size ≤ 20) :
  let grid := List.replicate size (List.replicate size 0)
  let mid := size / 2
  let centerRow := replaceNth (List.replicate size 0) mid 2
  let modifiedGrid := replaceNth grid mid centerRow
  let polygon := solve_polygon modifiedGrid
  polygon.length = 4 ∧ isConvex polygon := sorry

/-
info: [(2, 3), (2, 4), (6, 6), (5, 2)]
-/
-- #guard_msgs in
-- #eval solve_polygon [[0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0], [0, 0, 0, 1, 2, 2, 1, 0], [0, 1, 2, 3, 4, 2, 0, 0], [0, 2, 4, 4, 4, 2, 0, 0], [0, 1, 2, 2, 3, 2, 0, 0], [0, 0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0]]

/-
info: [(2, 2), (2, 3), (3, 3), (3, 2)]
-/
-- #guard_msgs in
-- #eval solve_polygon [[0, 0, 0, 0, 0], [0, 1, 2, 1, 0], [0, 2, 4, 2, 0], [0, 1, 2, 1, 0], [0, 0, 0, 0, 0]]

/-
info: [(2, 5), (4, 5), (4, 2)]
-/
-- #guard_msgs in
-- #eval solve_polygon [[0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 2, 1, 0, 0], [0, 1, 3, 4, 2, 0, 0], [0, 0, 1, 3, 2, 0, 0], [0, 0, 0, 2, 2, 0, 0], [0, 0, 0, 1, 1, 0, 0], [0, 0, 0, 0, 0, 0, 0]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded