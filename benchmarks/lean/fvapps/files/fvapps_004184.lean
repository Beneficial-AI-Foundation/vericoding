-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def proc_arr (arr : List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem proc_arr_length (arr : List String) : 
  List.length (proc_arr arr) = 3 :=
  sorry

theorem proc_arr_permutation_count (arr : List String) :
  let result := proc_arr arr
  let n := List.length arr
  List.head! result > 0 :=
  sorry

theorem proc_arr_min_leq_max (arr : List String) :
  let result := proc_arr arr
  List.get! result 1 ≤ List.get! result 2 :=
  sorry

theorem proc_arr_all_zeros (n : Nat) :
  let zeros := List.replicate n "0"
  let result := proc_arr zeros
  List.get! result 1 = 0 ∧ List.get! result 2 = 0 ∧ List.head! result = 1 :=
  sorry

theorem proc_arr_all_same (n : Nat) :
  let ones := List.replicate n "1" 
  let result := proc_arr ones
  List.head! result = 1 ∧ 
  List.get! result 1 = List.get! result 2 :=
  sorry
-- </vc-theorems>