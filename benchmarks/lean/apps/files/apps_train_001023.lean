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

/-
info: 31
-/
-- #guard_msgs in
-- #eval max_pizza_slices 5 10 [1, 2, 3, 4, 5]

/-
info: 6
-/
-- #guard_msgs in
-- #eval max_pizza_slices 2 3 [1, 2]

/-
info: 8
-/
-- #guard_msgs in
-- #eval max_pizza_slices 3 4 [2, 1, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded