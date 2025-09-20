-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_hours_equal_plants (n : Nat) (plants : List Nat) : Nat := sorry

def isDecreasing (l : List Nat) : Prop :=
  ∀ i, i + 1 < l.length → l[i]! > l[i+1]!
-- </vc-definitions>

-- <vc-theorems>
theorem min_gap_strictly_decreasing
  {n : Nat} {plants : List Nat}
  (h_sorted : isDecreasing plants)
  (h_len : plants.length = n)
  (h_size : n ≥ 2)
  (h_bounded : ∀ x ∈ plants, x ≥ 1 ∧ x ≤ 1000) :
  ∃ i, i + 1 < plants.length ∧ 
    min_hours_equal_plants n plants = plants[i]! - plants[i+1]! :=
sorry

theorem min_gap_constant
  {n : Nat} {gap : Nat}
  (h_n : n ≥ 2 ∧ n ≤ 10)
  (h_gap : gap ≥ 1 ∧ gap ≤ 100)
  (plants := List.range n |>.map (fun i => 100 - i * gap)) :
  min_hours_equal_plants n plants = gap :=
sorry
-- </vc-theorems>