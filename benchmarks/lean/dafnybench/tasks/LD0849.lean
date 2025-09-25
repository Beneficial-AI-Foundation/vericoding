-- <vc-preamble>
partial def SqrSumRec (n : Int) : Int :=
if n == 0 then 0
else n * n + SqrSumRec (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SqrSum1 (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SqrSumRec_spec (n : Int) :
n ≥ 0 → SqrSumRec n = n * (n + 1) * (2 * n + 1) / 6 :=
sorry

theorem SqrSum1_spec (n : Int) (s : Int) :
n ≥ 0 → s = SqrSum1 n → s = SqrSumRec n :=
sorry
-- </vc-theorems>