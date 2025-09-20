-- <vc-preamble>
def euclDistance (point : List Int) : Int :=
  match point with
  | [x, y] => x*x + y*y
  | _ => 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kClosest (points : List (List Int)) (k : Nat) : List (List Int) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem kClosest_correct_length {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  (kClosest points k).length = k :=
sorry

theorem kClosest_subset {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ kClosest points k, p ∈ points :=
sorry

theorem kClosest_distances_ordered {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ i j, i < j → j < (kClosest points k).length →
  euclDistance ((kClosest points k)[i]!) ≤ euclDistance ((kClosest points k)[j]!) :=
sorry

theorem kClosest_optimal {points : List (List Int)} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ points.length)
  (h3 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ kClosest points k, ∀ q ∈ points, q ∉ kClosest points k →
  euclDistance p ≤ euclDistance q :=
sorry

theorem kClosest_full_list {points : List (List Int)}
  (h : ∀ p ∈ points, p.length = 2) :
  kClosest points points.length = points :=
sorry

theorem kClosest_k_one {points : List (List Int)}
  (h1 : points.length > 0)
  (h2 : ∀ p ∈ points, p.length = 2) :
  ∀ p ∈ points,
  euclDistance (List.head! (kClosest points 1)) ≤ euclDistance p :=
sorry
-- </vc-theorems>