-- <vc-preamble>
@[reducible, simp]
def interleave_precond (s1 : Array Int) (s2 : Array Int) (s3 : Array Int) : Prop :=
  s1.size = s2.size ∧ s2.size = s3.size ∧ 0 ≤ (s1.size * 3) ∧ (s1.size * 3) ≤ Int.natAbs (Int.ofNat 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interleave (s1 : Array Int) (s2 : Array Int) (s3 : Array Int) (h_precond : interleave_precond s1 s2 s3) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def interleave_postcond (s1 : Array Int) (s2 : Array Int) (s3 : Array Int) (result : Array Int) (h_precond : interleave_precond s1 s2 s3) : Prop :=
  result.size = s1.size * 3 ∧ 
  (∀ i : Nat, i < s1.size → result[3 * i]! = s1[i]! ∧ result[3 * i + 1]! = s2[i]! ∧ result[3 * i + 2]! = s3[i]!)

theorem interleave_spec_satisfied (s1 : Array Int) (s2 : Array Int) (s3 : Array Int) (h_precond : interleave_precond s1 s2 s3) :
    interleave_postcond s1 s2 s3 (interleave s1 s2 s3 h_precond) h_precond := by
  sorry
-- </vc-theorems>