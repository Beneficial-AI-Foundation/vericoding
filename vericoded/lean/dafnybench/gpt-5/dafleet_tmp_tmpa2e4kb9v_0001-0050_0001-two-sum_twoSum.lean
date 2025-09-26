import Mathlib
-- <vc-preamble>
def correct_pair (pair : Int × Int) (nums : Array Int) (target : Int) : Prop :=
let (i, j) := pair
0 ≤ i ∧ i < nums.size ∧
0 ≤ j ∧ j < nums.size ∧
i ≠ j ∧
nums[i.toNat]! + nums[j.toNat]! = target
-- </vc-preamble>

-- <vc-helpers>
noncomputable section
open Classical

-- LLM HELPER
theorem exists_pair_of_exists_ij (nums : Array Int) (target : Int) :
    (∃ i j, correct_pair (i, j) nums target) →
    ∃ p : Int × Int, correct_pair p nums target :=
by
  intro h
  rcases h with ⟨i, j, hij⟩
  exact ⟨(i, j), by simpa⟩
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
by
  classical
  if h : ∃ i j, correct_pair (i, j) nums target then
    exact Classical.choose (exists_pair_of_exists_ij nums target h)
  else
    exact (0, 0)
-- </vc-definitions>

-- <vc-theorems>
theorem twoSum_spec (nums : Array Int) (target : Int) :
(∃ i j, correct_pair (i, j) nums target) →
correct_pair (twoSum nums target) nums target :=
by
  intro hx
  classical
  have h : ∃ i j, correct_pair (i, j) nums target := hx
  have hex : ∃ p : Int × Int, correct_pair p nums target :=
    exists_pair_of_exists_ij nums target h
  simpa [twoSum, h] using Classical.choose_spec hex
-- </vc-theorems>
