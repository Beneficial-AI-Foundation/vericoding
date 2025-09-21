-- <vc-preamble>
partial def SqrSumRec (n : Int) : Int :=
if n == 0 then 0
else n * n + SqrSumRec (n - 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def HoareTripleReqEns (i : Int) (k : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SqrSumRec_spec (n : Int) :
n ≥ 0 → SqrSumRec n = n * (n + 1) * (2 * n + 1) / 6 :=
sorry

theorem HoareTripleReqEns_spec (i k : Int) :
k = i * i →
∃ k', HoareTripleReqEns i k = k' ∧ k' = (i + 1) * (i + 1) :=
sorry
-- </vc-theorems>