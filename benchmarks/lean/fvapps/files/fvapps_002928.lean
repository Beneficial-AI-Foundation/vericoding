-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def squares : Nat → List Nat
| n =>
sorry

def num_range : Nat → Int → Int → List Int
| n, start, step =>
sorry

def rand_range : Nat → Int → Int → List Int
| n, mn, mx =>
sorry

def primes : Nat → List Nat
| n =>
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>