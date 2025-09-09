-- <vc-helpers>
-- </vc-helpers>

def fib_digits (n : Nat) : List (Nat × Nat) := sorry

theorem fib_digits_bounds {n : Nat} (h : n ≥ 10) :
  let result := fib_digits n
  (∀ (count digit : Nat), (count, digit) ∈ result → 
    count > 0 ∧ digit ≤ 9) := sorry

theorem fib_digits_total_count {n : Nat} (h : n ≥ 10) :
  let result := fib_digits n
  let pairs := result.toArray
  let counts := Array.map Prod.fst pairs
  (Array.size counts > 0) := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible