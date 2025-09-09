def solveDie (n : Nat) (nums : List Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isValidConfig (config : List Nat) : Bool :=
  sorry

/- If solveDie returns [0], it indicates no valid configuration exists.
    Otherwise, returns a valid die configuration that works with the input sequence. -/

theorem die_configuration_theorem (n : Nat) (nums : List Nat) :
  let result := solveDie n nums
  result = [0] ∨ isValidConfig result ∧
    ∀ i : Nat, i + 1 < n →
      nums[i]! ≠ nums[i+1]! ∧
      nums[i+1]! ≠ result[nums[i]! - 1]! :=
  sorry

/- If there are adjacent equal numbers in the input sequence,
    no valid die configuration exists -/

theorem adjacent_same_numbers_theorem (n : Nat) (nums : List Nat) :
  (∃ i : Nat, i + 1 < n ∧ nums[i]! = nums[i+1]!) →
  solveDie n nums = [0] :=
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded