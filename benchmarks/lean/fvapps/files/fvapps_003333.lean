-- <vc-preamble>
def fibNaive (n : Nat) : Nat := 
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let rec fib_iter (i : Nat) (a b : Nat) : Nat :=
      match i with
      | 0 => b
      | i + 1 => fib_iter i b (a + b)
    fib_iter (n) 0 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lastFibDigit (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matches_naive_for_small_n (n : Nat) (h : n ≤ 100) :
  lastFibDigit n = fibNaive n % 10 :=
sorry

theorem returns_single_digit (n : Nat) :
  0 ≤ lastFibDigit n ∧ lastFibDigit n ≤ 9 :=
sorry

theorem periodic_behavior_sixty (n : Nat) :
  lastFibDigit n = lastFibDigit (n + 60) :=
sorry

theorem periodic_behavior_mod (n : Nat) :
  lastFibDigit n = lastFibDigit (n % 60) :=
sorry
-- </vc-theorems>