-- <vc-preamble>
partial def sumcheck (s : Array Int) (i : Int) : Int :=
if i == 0 then 0
else s[(i - 1).toNat]! + sumcheck s (i - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum (s : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_spec (s : Array Int) :
s.size > 0 →
sum s = sumcheck s s.size :=
sorry
-- </vc-theorems>