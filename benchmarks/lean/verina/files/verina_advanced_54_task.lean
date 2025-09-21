-- <vc-preamble>
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def missingNumber_postcond (nums : List Nat) (result: Nat) (h_precond : missingNumber_precond (nums)) : Prop :=
  let n := nums.length
  (result ∈ List.range (n + 1)) ∧
  ¬(result ∈ nums) ∧
  ∀ x, (x ∈ List.range (n + 1)) → x ≠ result → x ∈ nums

theorem missingNumber_spec_satisfied (nums: List Nat) (h_precond : missingNumber_precond (nums)) :
    missingNumber_postcond (nums) (missingNumber (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>