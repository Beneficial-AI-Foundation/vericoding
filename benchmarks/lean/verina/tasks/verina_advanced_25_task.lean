-- <vc-preamble>
import Mathlib.Data.List.Basic

@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0
-- </vc-helpers>

-- <vc-definitions>
def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem lengthOfLIS_spec_satisfied (nums: List Int) (h_precond : lengthOfLIS_precond (nums)) :
    lengthOfLIS_postcond (nums) (lengthOfLIS (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>