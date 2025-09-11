-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kClosest (points : List (List Int)) (k : Nat) : List (List Int) := sorry

def euclDistance (point : List Int) : Int :=
  match point with
  | [x, y] => x*x + y*y
  | _ => 0

/- For valid inputs, kClosest returns k points -/
-- </vc-definitions>

-- <vc-theorems>
theorem kClosest_correct_length {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  (kClosest points k).length = k := sorry

/- All points in the result were in the original list -/

theorem kClosest_subset {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ kClosest points k, p ∈ points := sorry

/- The distances in the result are non-decreasing -/

theorem kClosest_distances_ordered {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ i j, i < j → j < (kClosest points k).length →
  euclDistance ((kClosest points k)[i]!) ≤ euclDistance ((kClosest points k)[j]!) := sorry

/- The result contains the k closest points -/

theorem kClosest_optimal {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ kClosest points k, ∀ q ∈ points, q ∉ kClosest points k →
  euclDistance p ≤ euclDistance q := sorry

/- When k equals length, returns all points -/

theorem kClosest_full_list {points : List (List Int)}
  (h : ∀ p ∈ points, p.length = 2) :
  kClosest points points.length = points := sorry

/- When k = 1, returns point with minimum distance -/

theorem kClosest_k_one {points : List (List Int)}
  (h1 : points.length > 0)
  (h2 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ points, 
  euclDistance (List.head! (kClosest points 1)) ≤ euclDistance p := sorry

/-
info: [[-2, 2]]
-/
-- #guard_msgs in
-- #eval kClosest [[1, 3], [-2, 2]] 1

/-
info: [[1, 1], [2, 2]]
-/
-- #guard_msgs in
-- #eval kClosest [[1, 1], [2, 2], [3, 3]] 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded