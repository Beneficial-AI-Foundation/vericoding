import Mathlib
-- <vc-preamble>
@[reducible, simp]
def cubeElement_precond (nums : Array Int) :=
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! ≤ 2147483647) ∧
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! * nums[k]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- Using `Int` which has arbitrary precision, the preconditions on integer ranges
-- are not strictly necessary for the correctness of the implementation,
-- as overflow is not an issue mathematically. Thus, no special helper functions are required.
-- </vc-helpers>

-- <vc-definitions>
def cubeElement (nums : Array Int) (h_precond : cubeElement_precond (nums)) : Array Int :=
    nums.map (fun x => x * x * x)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeElement_postcond (nums : Array Int) (cubed: Array Int) (h_precond : cubeElement_precond (nums)) :=
  ∀ i, i < nums.size → cubed[i]! = nums[i]! * nums[i]! * nums[i]!

theorem cubeElement_spec_satisfied (nums: Array Int) (h_precond : cubeElement_precond (nums)) :
    cubeElement_postcond (nums) (cubeElement (nums) h_precond) h_precond := by
    -- Unfold definitions to expose the goal.
  unfold cubeElement_postcond cubeElement
  -- Introduce index `i` and its bound `hi`.
  intro i hi
  -- The goal is `(nums.map (fun x => x * x * x))[i]! = nums[i]! * nums[i]! * nums[i]!`.
  -- The `![i]` notation (`getElem!`) expands to an `if-then-else` based on `i < arr.size`.
  -- The hypothesis `hi` allows `simp` to resolve these checks.
  -- `simp` automatically uses `@[simp]` lemmas like `Array.size_map` and `Array.getElem_map`
  -- to handle the mapped array's size and element access.
  simp [hi]
-- </vc-theorems>
