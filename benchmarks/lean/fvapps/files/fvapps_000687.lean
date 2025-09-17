-- <vc-preamble>
def min_trips (n : Nat) (k : Nat) (weights : List Nat) : Int := sorry

def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_maximum : List Nat → Nat 
  | [] => 0
  | [x] => x
  | (x::xs) => max x (list_maximum xs)
-- </vc-definitions>

-- <vc-theorems>
theorem min_trips_basic_properties 
  (weights : List Nat) (k : Nat) (n : Nat) (h1 : n = weights.length) :
  let result := min_trips n k weights
  ((∃ w ∈ weights, w > k) → result = -1) ∧ 
  ((∀ w ∈ weights, w ≤ k) → 
    result > 0 ∧ 
    result ≤ n ∧
    result * k ≥ list_sum weights) := sorry

theorem min_trips_monotonic
  (weights : List Nat) (n : Nat) (h1 : n = weights.length) :
  let k₁ := list_maximum weights
  let k₂ := k₁ + 1
  min_trips n k₁ weights ≥ min_trips n k₂ weights := sorry

theorem min_trips_zero_weights
  (k : Nat) (weights : List Nat) (n : Nat) (h1 : n = weights.length)
  (h2 : ∀ w ∈ weights, w = 0) :
  let result := min_trips n k weights
  result = 0 ∨ result = 1 := sorry

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_trips 1 1 [2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_trips 2 4 [1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_trips 3 6 [3, 4, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded