-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fix_progression (arr : List Int) : Nat := sorry

theorem fix_progression_bounds {arr : List Int} (h : arr ≠ []) : 
  fix_progression arr ≤ arr.length - 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_sequence_no_changes {arr : List Int} (h : arr.length ≥ 2) :
  let d := arr[1]! - arr[0]!
  let arith_seq := List.map (fun i => arr[0]! + (Int.ofNat i) * d) (List.range arr.length)
  fix_progression arith_seq = 0 := sorry

theorem constant_sequence_no_changes {arr : List Int} (h : arr.length ≥ 2) :
  let const_seq := List.replicate arr.length arr[0]!
  fix_progression const_seq = 0 := sorry

theorem result_changes_with_perturbation {arr : List Int} (h : arr.length ≥ 3) :
  let mid := arr.length / 2
  let arr_perturbed := arr.set mid (arr[mid]! + 1000)
  fix_progression arr ≤ fix_progression arr_perturbed := sorry
-- </vc-theorems>