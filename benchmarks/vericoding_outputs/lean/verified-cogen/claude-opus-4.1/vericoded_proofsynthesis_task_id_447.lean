import Mathlib
-- <vc-preamble>
@[reducible, simp]
def cubeElement_precond (nums : Array Int) :=
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! ≤ 2147483647) ∧
  (∀ k, k < nums.size → -2147483648 ≤ nums[k]! * nums[k]! * nums[k]! ∧ nums[k]! * nums[k]! * nums[k]! ≤ 2147483647)
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma array_size_map (f : α → β) (a : Array α) : (a.map f).size = a.size := by
  simp [Array.size_map]

-- LLM HELPER
lemma array_get_map (f : α → β) (a : Array α) (i : Nat) (h : i < (a.map f).size) :
    (a.map f)[i]'h = f (a[i]'(by rw [Array.size_map] at h; exact h)) := by
  simp [Array.getElem_map]
-- </vc-helpers>

-- <vc-definitions>
def cubeElement (nums : Array Int) (h_precond : cubeElement_precond (nums)) : Array Int :=
  Array.map (fun x => x * x * x) nums
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def cubeElement_postcond (nums : Array Int) (cubed: Array Int) (h_precond : cubeElement_precond (nums)) :=
  ∀ i, i < nums.size → cubed[i]! = nums[i]! * nums[i]! * nums[i]!

theorem cubeElement_spec_satisfied (nums: Array Int) (h_precond : cubeElement_precond (nums)) :
    cubeElement_postcond (nums) (cubeElement (nums) h_precond) h_precond := by
  unfold cubeElement_postcond cubeElement
  intro i h_i
  simp [array_get_map, h_i]
-- </vc-theorems>

def main : IO Unit := pure ()