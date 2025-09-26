-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveDie (n : Nat) (nums : List Nat) : List Nat :=
  sorry

def isValidConfig (config : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem die_configuration_theorem (n : Nat) (nums : List Nat) :
  let result := solveDie n nums
  result = [0] ∨ isValidConfig result ∧
    ∀ i : Nat, i + 1 < n →
      nums[i]! ≠ nums[i+1]! ∧
      nums[i+1]! ≠ result[nums[i]! - 1]! :=
sorry

theorem adjacent_same_numbers_theorem (n : Nat) (nums : List Nat) :
  (∃ i : Nat, i + 1 < n ∧ nums[i]! = nums[i+1]!) →
  solveDie n nums = [0] :=
sorry
-- </vc-theorems>