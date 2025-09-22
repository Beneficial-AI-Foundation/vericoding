-- <vc-preamble>
partial def SqrSumRec (n : Int) : Int :=
if n == 0 then 0 else n*n + SqrSumRec (n-1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def DivMod1 (a : Int) (b : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem L1_spec (n : Int) :
n ≥ 0 → SqrSumRec n = n * (n + 1) * (2 * n + 1) / 6 :=
sorry

theorem DivMod1_spec (a b : Int) :
b > 0 ∧ a ≥ 0 →
let (q, r) := DivMod1 a b
a = b*q + r ∧ 0 ≤ r ∧ r < b :=
sorry
-- </vc-theorems>