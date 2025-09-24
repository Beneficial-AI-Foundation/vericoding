-- <vc-preamble>
def f2 (n : Nat) : Nat :=
if n = 0 then 0
else 5 * f2 (n / 3) + n % 4
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mod2 (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mod2_spec (n : Nat) : mod2 n = f2 n :=
sorry
-- </vc-theorems>