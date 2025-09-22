-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxPizzaSlices (m: Nat) (n: Nat) (cuts: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_pizza_slices_positive (m n: Nat) (cuts: List Nat) (h1: m > 0) (h2: n > 0) (h3: cuts.length > 0) :
  maxPizzaSlices m n cuts > 0 :=
  sorry

theorem max_pizza_slices_min_bound (m n: Nat) (cuts: List Nat) (h1: m > 0) (h2: n > 0) (h3: cuts.length > 0) :
  maxPizzaSlices m n cuts ≥ m :=
  sorry

theorem max_pizza_slices_max_bound (m n: Nat) (cuts: List Nat) (h1: m > 0) (h2: n > 0) (h3: cuts.length > 0) :
  maxPizzaSlices m n cuts ≤ m + (n * (n + 1)) / 2 :=
  sorry

theorem single_pizza_formula (n cuts: Nat) (h1: cuts ≤ n) :
  maxPizzaSlices 1 n [cuts] = 1 + (cuts * (cuts + 1)) / 2 :=
  sorry
-- </vc-theorems>