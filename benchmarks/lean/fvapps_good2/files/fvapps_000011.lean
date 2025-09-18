-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_grid_area (s : String) : Nat :=
  sorry

def min_width_height_from_path (s : String) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_grid_area_positive (s : String) :
  min_grid_area s > 0 := by
  sorry

theorem min_grid_area_nonempty (s : String) (h : s.length > 0) :
  min_grid_area s ≥ 2 := by
  sorry

theorem min_grid_area_empty :
  min_grid_area "" = 1 := by
  sorry

theorem min_grid_area_single_char (c : Char) (h : c = 'W' ∨ c = 'A' ∨ c = 'S' ∨ c = 'D') :
  min_grid_area (String.mk [c]) = 2 := by
  sorry

theorem min_grid_area_bounds (s : String) :
  let (w, h) := min_width_height_from_path s
  min_grid_area s ≥ min (w * h) 2 := by
  sorry
-- </vc-theorems>