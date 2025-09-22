-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int := if x < 0 then -x else x

def min_moves_to_cheese (n : Int) (sx sy ex ey blockx blocky : Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_manhattan_lower_bound 
  (n : Int) (sx sy ex ey blockx blocky : Int)
  (h1 : n ≥ 2) (h2 : sx ≥ 1) (h3 : sy ≥ 1) (h4 : ex ≥ 1) (h5 : ey ≥ 1) 
  (h6 : blockx ≥ 1) (h7 : blocky ≥ 1)
  (h8 : sx ≤ 100) (h9 : sy ≤ 100) (h10 : ex ≤ 100) (h11 : ey ≤ 100)
  (h12 : blockx ≤ 100) (h13 : blocky ≤ 100) :
  min_moves_to_cheese n sx sy ex ey blockx blocky ≥ (abs (sx - ex) + abs (sy - ey)) := sorry

theorem min_moves_manhattan_upper_bound
  (n : Int) (sx sy ex ey blockx blocky : Int)
  (h1 : n ≥ 2) (h2 : sx ≥ 1) (h3 : sy ≥ 1) (h4 : ex ≥ 1) (h5 : ey ≥ 1)
  (h6 : blockx ≥ 1) (h7 : blocky ≥ 1)
  (h8 : sx ≤ 100) (h9 : sy ≤ 100) (h10 : ex ≤ 100) (h11 : ey ≤ 100)
  (h12 : blockx ≤ 100) (h13 : blocky ≤ 100) :
  min_moves_to_cheese n sx sy ex ey blockx blocky ≤ (abs (sx - ex) + abs (sy - ey) + 2) := sorry

theorem max_detour_implies_blocked_path
  (n : Int) (sx sy ex ey blockx blocky : Int)
  (h1 : n ≥ 2) (h2 : sx ≥ 1) (h3 : sy ≥ 1) (h4 : ex ≥ 1) (h5 : ey ≥ 1)
  (h6 : blockx ≥ 1) (h7 : blocky ≥ 1)
  (h8 : sx ≤ 100) (h9 : sy ≤ 100) (h10 : ex ≤ 100) (h11 : ey ≤ 100)
  (h12 : blockx ≤ 100) (h13 : blocky ≤ 100)
  (h14 : min_moves_to_cheese n sx sy ex ey blockx blocky = abs (sx - ex) + abs (sy - ey) + 2) :
  ((sx = ex ∧ ex = blockx ∧ min sy ey < blocky ∧ blocky < max sy ey) ∨
   (sy = ey ∧ ey = blocky ∧ min sx ex < blockx ∧ blockx < max sx ex)) := sorry

theorem diagonal_manhattan_distance
  (n : Int) (sx sy ex ey : Int)
  (h1 : n ≥ 2) (h2 : sx ≥ 1) (h3 : sy ≥ 1) (h4 : ex ≥ 1) (h5 : ey ≥ 1)
  (h6 : sx ≤ 100) (h7 : sy ≤ 100) (h8 : ex ≤ 100) (h9 : ey ≤ 100)
  (h10 : sx ≠ ex) (h11 : sy ≠ ey) :
  min_moves_to_cheese n sx sy ex ey 1 1 = abs (sx - ex) + abs (sy - ey) := sorry
-- </vc-theorems>