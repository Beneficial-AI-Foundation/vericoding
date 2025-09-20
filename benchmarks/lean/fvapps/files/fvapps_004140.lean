-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def area_or_perimeter (l w : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_is_area {l : Nat} (h : l > 0) (h2 : l ≤ 1000) :
  area_or_perimeter l l = l * l :=
sorry

theorem rectangle_is_perimeter {l w : Nat} (h1 : l > 0) (h2 : w > 0) 
    (h3 : l ≤ 1000) (h4 : w ≤ 1000) (h5 : l ≠ w) :
  area_or_perimeter l w = 2 * (l + w) :=
sorry

theorem output_is_positive {l w : Nat} (h1 : l > 0) (h2 : w > 0)
    (h3 : l ≤ 1000) (h4 : w ≤ 1000) :
  area_or_perimeter l w > 0 :=
sorry

theorem commutative {l w : Nat} (h1 : l > 0) (h2 : w > 0)
    (h3 : l ≤ 1000) (h4 : w ≤ 1000) :
  area_or_perimeter l w = area_or_perimeter w l :=
sorry
-- </vc-theorems>