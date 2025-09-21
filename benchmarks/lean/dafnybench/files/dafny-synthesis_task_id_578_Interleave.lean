-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Interleave (s1 s2 s3 : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Interleave_spec (s1 s2 s3 : Array Int) :
s1.size = s2.size ∧ s2.size = s3.size →
let r := Interleave s1 s2 s3
r.size = 3 * s1.size ∧
(∀ i, 0 ≤ i ∧ i < s1.size →
r[3*i]! = s1[i]! ∧
r[3*i + 1]! = s2[i]! ∧
r[3*i + 2]! = s3[i]!) :=
sorry
-- </vc-theorems>