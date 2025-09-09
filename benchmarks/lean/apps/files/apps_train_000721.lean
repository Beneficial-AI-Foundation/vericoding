-- <vc-helpers>
-- </vc-helpers>

def calculate_min_fences (n m : Nat) (plants : List (Nat × Nat)) : Nat := sorry

theorem fence_positive {n m : Nat} {plants : List (Nat × Nat)}
  (h1 : n > 0) (h2 : m > 0) (h3 : plants ≠ []) :
  (calculate_min_fences n m plants) > 0 := sorry

theorem single_plant_perimeter {n m : Nat} {p : Nat × Nat}
  (h1 : n > 0) (h2 : m > 0) :
  (calculate_min_fences n m [p]) = 4 := sorry

theorem max_perimeter_bound {n m : Nat} {plants : List (Nat × Nat)}
  (h1 : n > 0) (h2 : m > 0) :
  (calculate_min_fences n m plants) ≤ 4 * plants.length := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible