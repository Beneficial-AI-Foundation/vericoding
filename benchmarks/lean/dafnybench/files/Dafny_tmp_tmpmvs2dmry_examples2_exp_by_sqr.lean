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
def exp_by_sqr (x0 : Float) (n0 : Nat) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_spec (m n : Nat) :
m > 0 ∧ n > 0 → gcd m n > 0 :=
sorry

theorem exp_by_sqr_spec (x0 : Float) (n0 : Nat) :
x0 ≥ 0.0 → exp_by_sqr x0 n0 = exp x0 n0 :=
sorry
-- </vc-theorems>