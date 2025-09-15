-- <vc-preamble>
/- Recursive sum function for array segments -/
def sum (a : Array Int) (s : Int) (t : Int) : Int :=
  if s < 0 ∨ s ≥ t ∨ t > a.size then
    0
  else
    a[t.toNat - 1]! + sum a s (t - 1)
termination_by (t - s).toNat

@[reducible, simp]
def maxSegmentSum_precond (a : Array Int) (s : Nat) (t : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

/- Main function for testing -/
def main : IO Unit :=
  IO.println "Max segment sum implementation"