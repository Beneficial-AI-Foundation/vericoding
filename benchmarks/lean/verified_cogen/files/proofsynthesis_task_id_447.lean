-- <vc-preamble>
@[reducible, simp]
def cubeElement_precond (nums : Array Int) :=
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! ≤ 2147483647) ∧
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! * nums[k]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()