-- <vc-preamble>
import Mathlib.Data.List.Basic

@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>