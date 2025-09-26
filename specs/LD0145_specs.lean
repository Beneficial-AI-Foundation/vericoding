-- <vc-preamble>
def summingPair (i j : Nat) (nums : Array Int) (target : Int) : Prop :=
i < nums.size ∧ j < nums.size ∧ i ≠ j ∧ nums[i]! + nums[j]! = target
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoSum (nums : Array Int) (target : Int) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem twoSum_spec (nums : Array Int) (target : Int) :
(∃ i j : Nat, i < j ∧ j < nums.size ∧
summingPair i j nums target ∧
∀ l m : Nat, l < m ∧ m < nums.size ∧ l ≠ i ∧ m ≠ j →
¬summingPair l m nums target) →
let pair := twoSum nums target
pair.1 < nums.size ∧ pair.2 < nums.size ∧
summingPair pair.1 pair.2 nums target :=
sorry
-- </vc-theorems>