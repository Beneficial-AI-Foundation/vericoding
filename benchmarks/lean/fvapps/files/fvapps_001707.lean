-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def edge_detection (s : String) : String := sorry

def pixel_at (s : String) (x y : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_value_image_no_edges (val : Nat) (h : val > 0) (h2 : val ≤ 5) :
  edge_detection s!"1 {val} 1" = "1 0 1" := sorry

theorem uniform_square_no_edges (size : Nat) (h : size > 0) (h2 : size ≤ 10) :
  edge_detection s!"{size} 5 {size * size}" = s!"{size} 0 {size * size}" := sorry

theorem alternating_pixels_edge_value 
  (size val1 val2 : Nat)
  (h1 : size > 0) (h2 : size ≤ 4)
  (h3 : val1 ≤ 255) (h4 : val2 ≤ 255)
  (h5 : val1 ≠ val2) :
  let input := s!"{size} {val1} {size} {val2} {size}"
  let diff := if val1 ≥ val2 then val1 - val2 else val2 - val1
  let output := edge_detection input
  ∀ i j, i < size → j < size →
    pixel_at output i j = diff := sorry
-- </vc-theorems>