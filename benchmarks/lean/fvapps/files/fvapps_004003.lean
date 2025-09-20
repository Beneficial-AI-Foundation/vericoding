-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_size (w h d : Nat) : Nat × Nat := sorry

theorem get_size_volume (w h d : Nat) :
  (get_size w h d).2 = w * h * d := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_size_surface_area (w h d : Nat) :
  (get_size w h d).1 = 2 * (w*h + h*d + w*d) := sorry

theorem get_size_surface_area_positive (w h d : Nat) (h1: w > 0) (h2: h > 0) (h3: d > 0) :
  (get_size w h d).1 > 0 := sorry

theorem get_size_volume_positive (w h d : Nat) (h1: w > 0) (h2: h > 0) (h3: d > 0) :
  (get_size w h d).2 > 0 := sorry

theorem get_size_surface_area_greater_than_faces (w h d : Nat) (h1: w > 0) (h2: h > 0) (h3: d > 0) :
  (get_size w h d).1 > w*h ∧ 
  (get_size w h d).1 > h*d ∧
  (get_size w h d).1 > w*d := sorry
-- </vc-theorems>