-- <vc-preamble>
import Mathlib

@[reducible, simp]
def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def intMax (x y : Int) : Int :=
  if x < y then y else x
-- </vc-helpers>

-- <vc-definitions>
def LongestIncreasingSubsequence (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def LongestIncreasingSubsequence_postcond (a : Array Int) (result: Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Prop :=
  let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem LongestIncreasingSubsequence_spec_satisfied (a: Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    LongestIncreasingSubsequence_postcond (a) (LongestIncreasingSubsequence (a) h_precond) h_precond := by
  sorry
-- </vc-theorems>