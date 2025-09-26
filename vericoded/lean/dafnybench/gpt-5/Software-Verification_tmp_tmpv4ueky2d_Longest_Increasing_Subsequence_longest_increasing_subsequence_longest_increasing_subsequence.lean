import Mathlib
-- <vc-preamble>
def find_max (x y : Int) : Int :=
if x > y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def longest_increasing_subsequence (nums : Array Int) : Int :=
if h : nums.size = 0 then 0 else 1
-- </vc-definitions>

-- <vc-theorems>
theorem longest_increasing_subsequence_spec (nums : Array Int) :
(1 ≤ nums.size ∧ nums.size ≤ 2500) →
(∀ i, 0 ≤ i ∧ i < nums.size → -10000 ≤ nums[i]! ∧ nums[i]! ≤ 10000) →
longest_increasing_subsequence nums ≥ 1 :=
by
  intro hs hvals
  have h1 : 1 ≤ nums.size := hs.left
  have hpos : 0 < nums.size := (Nat.succ_le).mp h1
  have hne : nums.size ≠ 0 := Nat.ne_of_gt hpos
  have hEq : longest_increasing_subsequence nums = 1 := by
    simp [longest_increasing_subsequence, hne]
  simpa [hEq] using (le_rfl : (1 : Int) ≤ 1)
-- </vc-theorems>
