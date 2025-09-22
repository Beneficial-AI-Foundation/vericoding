-- <vc-preamble>
def abs (n : Int) : Int := 
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diff (arr : List String) : Option String := sorry

theorem diff_empty_list :
  diff [] = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diff_equal_pairs (n : Nat) :
  diff [s!"{n}-{n}"] = none := sorry

theorem diff_result_in_input (arr : List String) :
  match diff arr with
  | none => True  
  | some result => result ∈ arr
  := sorry

theorem diff_has_largest_diff (arr : List String) (result : String) :
  diff arr = some result →
  let result_nums := (result.splitOn "-").map String.toNat!
  let result_diff := abs (result_nums[0]! - result_nums[1]!)
  ∀ pair ∈ arr,
    let nums := (pair.splitOn "-").map String.toNat!
    let diff_val := abs (nums[0]! - nums[1]!)
    diff_val ≤ result_diff
  := sorry
-- </vc-theorems>