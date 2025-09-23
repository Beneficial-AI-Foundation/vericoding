-- <vc-preamble>
import Mathlib

@[reducible, simp]
def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestIncreasingSubsequence (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Prop :=
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem longestIncreasingSubsequence_spec_satisfied (numbers: List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    longestIncreasingSubsequence_postcond (numbers) (longestIncreasingSubsequence (numbers) h_precond) h_precond := by
  sorry
-- </vc-theorems>