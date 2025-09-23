-- <vc-preamble>
partial def gcd (x y : Int) : Int :=
if x = y then x
else if x > y then gcd (x - y) y
else gcd x (y - x)

partial def gcd' (x y : Int) : Int :=
if x = y then x
else if x > y then gcd' (x - y) y
else gcd y x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcdI (m n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_spec (x y : Int) :
x > 0 ∧ y > 0 → gcd x y > 0 :=
sorry

theorem gcd'_spec (x y : Int) :
x > 0 ∧ y > 0 → gcd' x y > 0 :=
sorry

theorem gcdI_spec (m n : Int) :
m > 0 ∧ n > 0 → gcdI m n = gcd m n :=
sorry
-- </vc-theorems>