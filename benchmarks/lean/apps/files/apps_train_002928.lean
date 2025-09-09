def squares : Nat → List Nat
| n => sorry

def num_range : Nat → Int → Int → List Int
| n, start, step => sorry

def rand_range : Nat → Int → Int → List Int
| n, mn, mx => sorry

-- <vc-helpers>
-- </vc-helpers>

def primes : Nat → List Nat
| n => sorry

theorem squares_length (n : Nat) : (squares n).length = n := by
  sorry

theorem squares_values (n : Nat) (i : Nat) : 
  i < n → (squares n).get ⟨i, sorry⟩ = (i + 1) * (i + 1) := by
  sorry

theorem num_range_length (n : Nat) (start step : Int) :
  (num_range n start step).length = n := by
  sorry

theorem num_range_start (n : Nat) (start step : Int) :
  n > 0 → (num_range n start step).get ⟨0, sorry⟩ = start := by
  sorry

theorem num_range_step (n : Nat) (start step : Int) :
  n > 1 → (num_range n start step).get ⟨1, sorry⟩ - (num_range n start step).get ⟨0, sorry⟩ = step := by
  sorry

theorem rand_range_length (n : Nat) (mn mx : Int) : 
  mn ≤ mx → (rand_range n mn mx).length = n := by
  sorry

theorem rand_range_bounds (n : Nat) (mn mx : Int) (i : Nat) :
  mn ≤ mx → i < n → 
  mn ≤ (rand_range n mn mx).get ⟨i, sorry⟩ ∧ (rand_range n mn mx).get ⟨i, sorry⟩ ≤ mx := by
  sorry

theorem primes_length (n : Nat) :
  (primes n).length = n := by
  sorry

theorem primes_ordered (n : Nat) (i : Nat) :
  n > 0 → i < n - 1 → 
  (primes n).get ⟨i, sorry⟩ < (primes n).get ⟨i + 1, sorry⟩ := by
  sorry

/-
info: [1, 4, 9, 16, 25]
-/
-- #guard_msgs in
-- #eval squares 5

/-
info: [1, 4, 9]
-/
-- #guard_msgs in
-- #eval squares 3

/-
info: [0, 1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval num_range 5 0 1

/-
info: [2, 4, 6]
-/
-- #guard_msgs in
-- #eval num_range 3 2 2

/-
info: [2, 3, 5, 7, 11]
-/
-- #guard_msgs in
-- #eval primes 5

-- Apps difficulty: introductory
-- Assurance level: guarded