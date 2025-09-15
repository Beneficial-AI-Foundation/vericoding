-- <vc-preamble>
@[reducible, simp]
def squareNums_precond (nums : Array Int) : Prop :=
  ∀ k, 0 ≤ k ∧ k < nums.size → 0 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! < 2147483647
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()