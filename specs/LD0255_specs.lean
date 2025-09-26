-- <vc-preamble>
partial def sumInts (n : Int) : Int :=
if n == 0 then 0
else sumInts (n-1) + n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumIntsLoop (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumInts_spec (n : Int) :
n ≥ 0 → sumInts n = n * (n + 1) / 2 :=
sorry

theorem SumIntsLoop_spec (n : Int) :
n ≥ 0 →
let s := SumIntsLoop n
s = sumInts n ∧ s = n * (n + 1) / 2 :=
sorry
-- </vc-theorems>