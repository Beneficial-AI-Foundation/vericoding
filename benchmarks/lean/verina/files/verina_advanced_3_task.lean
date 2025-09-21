-- <vc-preamble>
@[reducible]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def intMax (x y : Int) : Int :=
  if x < y then y else x
-- </vc-helpers>

-- <vc-definitions>
def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>