-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mod : Nat := 1000000007

def find_car_numbers (x1 y1 x2 y2 k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coordinates_ordering {x1 y1 x2 y2 k : Nat}
  (h1 : 1 ≤ x1 ∧ x1 ≤ 100000)
  (h2 : 1 ≤ y1 ∧ y1 ≤ 100000)
  (h3 : 1 ≤ x2 ∧ x2 ≤ 100000) 
  (h4 : 1 ≤ y2 ∧ y2 ≤ 100000)
  (h5 : 1 ≤ k ∧ k ≤ 1000000000) :
  0 ≤ find_car_numbers (min x1 x2) (min y1 y2) (max x1 x2) (max y1 y2) k ∧
  find_car_numbers (min x1 x2) (min y1 y2) (max x1 x2) (max y1 y2) k < mod :=
  sorry

theorem symmetry {x1 y1 x2 y2 k : Nat}
  (h1 : 1 ≤ x1 ∧ x1 ≤ 100000)
  (h2 : 1 ≤ y1 ∧ y1 ≤ 100000)
  (h3 : 1 ≤ x2 ∧ x2 ≤ 100000)
  (h4 : 1 ≤ y2 ∧ y2 ≤ 100000)
  (h5 : 1 ≤ k ∧ k ≤ 1000000000) :
  find_car_numbers (min x1 x2) (min y1 y2) (max x1 x2) (max y1 y2) k =
  find_car_numbers (min y1 y2) (min x1 x2) (max y1 y2) (max x1 x2) k :=
  sorry
-- </vc-theorems>