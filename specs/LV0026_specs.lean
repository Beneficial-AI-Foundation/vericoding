-- <vc-preamble>
@[reducible]
def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
partial def toCharList (s : String) : List Char :=
  s.data

partial def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""

partial def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right
-- </vc-helpers>

-- <vc-definitions>
def longestCommonSubsequence (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : Prop :=
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)

theorem longestCommonSubsequence_spec_satisfied (s1: String) (s2: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    longestCommonSubsequence_postcond (s1) (s2) (longestCommonSubsequence (s1) (s2) h_precond) h_precond := by
  sorry
-- </vc-theorems>