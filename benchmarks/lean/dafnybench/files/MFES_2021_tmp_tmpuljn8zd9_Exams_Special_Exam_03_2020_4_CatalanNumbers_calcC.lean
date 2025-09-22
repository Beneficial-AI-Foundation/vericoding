-- <vc-preamble>
def C (n : Nat) : Nat :=
if n = 0 then
1
else
(4 * n - 2) * C (n-1) / (n + 1)
decreasing_by all_goals simp_wf; omega
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calcC (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calcC_spec (n : Nat) : calcC n = C n :=
sorry
-- </vc-theorems>