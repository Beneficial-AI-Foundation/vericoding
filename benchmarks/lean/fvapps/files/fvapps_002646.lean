-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fib_rabbits (n : Nat) (b : Nat) : Nat := sorry

theorem fib_rabbits_nonnegative (n : Nat) (b : Nat) (h : b > 0) :
  fib_rabbits n b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fib_rabbits_monotone (n : Nat) (b : Nat) (h1 : b > 0) (h2 : n > 2) :
  fib_rabbits n b ≥ fib_rabbits (n-1) b := sorry

theorem fib_rabbits_bound (n : Nat) (b : Nat) (h1 : b > 0) (h2 : n > 1) :
  fib_rabbits n b ≤ fib_rabbits (n-1) b * b + fib_rabbits (n-2) b := sorry 

theorem fib_rabbits_zero (b : Nat) (h : b > 0) :
  fib_rabbits 0 b = 0 := sorry
-- </vc-theorems>