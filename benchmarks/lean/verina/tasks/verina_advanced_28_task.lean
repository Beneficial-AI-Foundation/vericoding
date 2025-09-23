-- <vc-preamble>
import Std.Data.HashSet
import Mathlib
open Std

@[reducible, simp]
def longestConsecutive_precond (nums : List Int) : Prop :=
  List.Nodup nums
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longestConsecutive (nums : List Int) (h_precond : longestConsecutive_precond (nums)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)
@[reducible, simp]
def longestConsecutive_postcond (nums : List Int) (result: Nat) (h_precond : longestConsecutive_precond (nums)) : Prop :=
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)

  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))

theorem longestConsecutive_spec_satisfied (nums: List Int) (h_precond : longestConsecutive_precond (nums)) :
    longestConsecutive_postcond (nums) (longestConsecutive (nums) h_precond) h_precond := by
  sorry
-- </vc-theorems>