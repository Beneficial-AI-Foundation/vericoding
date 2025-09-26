-- <vc-preamble>
partial def gcd (m n : Nat) : Nat :=
if m = n then n
else if m > n then gcd (m - n) n
else gcd m (n - m)

def exp (x : Float) (n : Nat) : Float :=
if n = 0 then 1.0
else if x == 0.0 then 0.0
else if n = 0 ∧ x == 0.0 then 1.0
else x * exp x (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdCalc (m n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_spec (m n : Nat) :
m > 0 ∧ n > 0 → gcd m n > 0 :=
sorry

theorem exp_spec (x : Float) (n : Nat) :
exp x n ≥ 0.0 :=
sorry

theorem gcdCalc_spec (m n : Nat) :
m > 0 ∧ n > 0 → gcdCalc m n = gcd m n :=
sorry
-- </vc-theorems>