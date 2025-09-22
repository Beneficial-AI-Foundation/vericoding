-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_virus_spread_days (row col x y : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem virus_spread_bounds 
    (row col : Nat) (x y : Nat)
    (h_row : row > 0) (h_col : col > 0)
    (h_x : x < row) (h_y : y < col) :
  let result := calc_virus_spread_days row col x y
  result ≥ max x (row - x - 1) + max y (col - y - 1) ∧ result ≥ 0 :=
  sorry

theorem virus_spread_square_symmetric
    (size : Nat) (h_size : size > 0) :
  let mid := size / 2
  calc_virus_spread_days size size mid mid = calc_virus_spread_days size size mid mid :=
  sorry

theorem virus_spread_corner_symmetry
    (row col : Nat) (h_row : row > 0) (h_col : col > 0) 
    (h_eq : row = col) :
  let corners := [(0, 0), (0, col-1), (row-1, 0), (row-1, col-1)]
  let results := corners.map (fun p => calc_virus_spread_days row col p.1 p.2)
  ∀ (x y : Nat), x ∈ results → y ∈ results → x = y :=
  sorry
-- </vc-theorems>