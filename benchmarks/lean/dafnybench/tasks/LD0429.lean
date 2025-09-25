-- <vc-preamble>
def fib (n : Nat) : Nat :=
if n < 2 then n else fib (n-2) + fib (n-1)

partial def fact (n : Nat) : Nat :=
if n == 0 then 1 else n * fact (n-1)

partial def gcd (m n : Nat) : Nat :=
if m == n then m
else if m > n then gcd (m - n) n
else gcd m (n - m)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdI (m n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_spec (m n : Nat) :
m > 0 ∧ n > 0 → gcd m n > 0 :=
sorry

theorem gcdI_spec (m n : Nat) :
m > 0 ∧ n > 0 → gcdI m n = gcd m n :=
sorry
-- </vc-theorems>