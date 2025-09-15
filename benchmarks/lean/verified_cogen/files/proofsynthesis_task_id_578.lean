-- <vc-preamble>
@[reducible, simp]
def interleave_precond (s1 : Array Int) (s2 : Array Int) (s3 : Array Int) : Prop :=
  s1.size = s2.size ∧ s2.size = s3.size ∧ 0 ≤ (s1.size * 3) ∧ (s1.size * 3) ≤ Int.natAbs (Int.ofNat 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>
