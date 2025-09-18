-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>