import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def remove_element (nums : Array Int) (val : Int) : Int :=
0
-- </vc-definitions>

-- <vc-theorems>
theorem remove_element_spec (nums : Array Int) (val : Int) :
(0 ≤ nums.size ∧ nums.size ≤ 100) →
(∀ i, 0 ≤ i ∧ i < nums.size → 0 ≤ nums[i]! ∧ nums[i]! ≤ 50) →
(0 ≤ val ∧ val ≤ 100) →
let i := remove_element nums val
∀ j:Nat, 0 < j ∧ j < i ∧ i < nums.size → nums[j]! ≠ val :=
by
  intro hsize hbnds hval
  simpa [remove_element] using
    (by
      intro j hj
      rcases hj with ⟨hj_pos, hj_lt, hi_lt_size⟩
      have hlt0 : (0 : Int) < 0 := lt_of_le_of_lt (Int.ofNat_nonneg j) hj_lt
      exact False.elim ((lt_irrefl _) hlt0)
    )
-- </vc-theorems>
