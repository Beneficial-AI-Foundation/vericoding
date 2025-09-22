-- <vc-preamble>
def toString (c : Char) : String := String.mk [c]

def mkString (n : Nat) (c : Char) : String := 
  String.mk (List.replicate n c)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_rectangle (h w : Nat) (grid : List String) : Nat := sorry

theorem solve_max_rectangle_dimensions {h w : Nat} (hge2 : h ≥ 2) (wge2 : w ≥ 2) 
    (grid : List String) (grid_all_dots : ∀ i < h, grid.get? i = some (mkString w '.')) :
  let result := solve_max_rectangle h w grid
  result ≥ max h w ∧ result ≤ h * w := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_max_rectangle_positive {h w : Nat} (hge2 : h ≥ 2) (wge2 : w ≥ 2)
    (grid : List String) (grid_valid : grid.length ≥ h ∧ ∀ row ∈ grid, row.length ≥ w) :
  let grid' := (grid.take h).map (λ row => row.take w)
  let result := solve_max_rectangle h w grid'
  result > 0 ∧ (∃ n : Nat, result = n) := sorry

theorem solve_max_rectangle_identical_rows {n : Nat} (nge2 : n ≥ 2) :
  let grid := List.replicate n (mkString n '.')
  solve_max_rectangle n n grid = n * n := sorry

theorem solve_max_rectangle_alternating_pattern {n : Nat} (nge2 : n ≥ 2) :
  let grid := List.range n |>.map (λ i =>
    List.range n |>.map (λ j => if (i + j) % 2 = 0 then '#' else '.') |>.asString)
  solve_max_rectangle n n grid ≥ n := sorry
-- </vc-theorems>