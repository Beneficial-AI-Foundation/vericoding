-- <vc-preamble>
def replaceNth {α : Type} (xs : List α) (n : Nat) (v : α) : List α :=
  match n, xs with
  | _, [] => []
  | 0, x::xs => v::xs
  | n+1, x::xs => x :: replaceNth xs n v
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isConvex (polygon : List (Nat × Nat)) : Bool := sorry

def solve_polygon (grid : List (List Nat)) : List (Nat × Nat) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_shape_valid (size : Nat) (h1 : size ≥ 7) (h2 : size ≤ 20) :
  let grid := List.replicate size (List.replicate size 0)
  let mid := size / 2
  let centerRow := replaceNth (List.replicate size 0) mid 2
  let modifiedGrid := replaceNth grid mid centerRow
  let polygon := solve_polygon modifiedGrid
  polygon.length = 4 ∧ isConvex polygon :=
sorry
-- </vc-theorems>