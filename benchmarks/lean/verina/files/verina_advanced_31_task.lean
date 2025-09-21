-- <vc-preamble>
import Mathlib.Data.List.Basic

@[reducible]
def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- Generate all subsequences
def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

-- Check if a list is strictly increasing
def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false
-- </vc-helpers>

-- <vc-definitions>
def longestIncreasingSubseqLength (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def longestIncreasingSubseqLength_postcond (xs : List Int) (result: Nat) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Prop :=
  let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)

theorem longestIncreasingSubseqLength_spec_satisfied (xs: List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    longestIncreasingSubseqLength_postcond (xs) (longestIncreasingSubseqLength (xs) h_precond) h_precond := by
  sorry
-- </vc-theorems>