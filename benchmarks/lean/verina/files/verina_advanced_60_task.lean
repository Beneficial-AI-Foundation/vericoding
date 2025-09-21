-- <vc-preamble>
@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  let evens := result.fst
  let odds := result.snd
  -- All elements from nums are in evens ++ odds, no extras
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)

theorem partitionEvensOdds_spec_satisfied (nums: List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    partitionEvensOdds_postcond (nums) (partitionEvensOdds (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>