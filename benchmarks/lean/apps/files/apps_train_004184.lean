-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: [60, 122233, 332221]
-/
-- #guard_msgs in
-- #eval proc_arr ["1", "2", "2", "3", "2", "3"]

/-
info: [3360, 1112335, 53321110]
-/
-- #guard_msgs in
-- #eval proc_arr ["1", "2", "3", "0", "5", "1", "1", "3"]

/-
info: [60, 111223, 322111]
-/
-- #guard_msgs in
-- #eval proc_arr ["1", "1", "1", "2", "2", "3"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible