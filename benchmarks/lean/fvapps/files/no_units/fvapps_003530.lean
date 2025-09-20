-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry 

def divisors (n : Nat) : Nat := sorry

-- Every positive number has at least 1 divisor and no more than itself
-- </vc-definitions>

-- <vc-theorems>
theorem divisors_bounds (n : Nat) (h : n > 0) : 
  1 ≤ divisors n ∧ divisors n ≤ n := sorry

-- Prime numbers have exactly 2 divisors

theorem divisors_prime (n : Nat) (h1 : n > 1) (h2 : ∀ m : Nat, 2 ≤ m → m ≤ sqrt n → ¬(m ∣ n)) : 
  divisors n = 2 := sorry

-- Perfect squares have an odd number of divisors

theorem divisors_perfect_square (n : Nat) (h : ∃ m : Nat, n = m * m) :
  divisors n % 2 = 1 := sorry

-- One has exactly one divisor

theorem divisors_one :
  divisors 1 = 1 := sorry
-- </vc-theorems>