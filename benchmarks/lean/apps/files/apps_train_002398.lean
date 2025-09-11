-- <vc-preamble>
def find_distance_value (arr1 arr2 : List Int) (d : Nat) : Nat := sorry

theorem find_distance_value_non_negative 
  (arr1 arr2 : List Int) (d : Nat) 
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  find_distance_value arr1 arr2 d ≥ 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x
-- </vc-definitions>

-- <vc-theorems>
theorem find_distance_value_bounded 
  (arr1 arr2 : List Int) (d : Nat)
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  find_distance_value arr1 arr2 d ≤ arr1.length := sorry

theorem find_distance_value_empty_arr2
  (arr1 : List Int) (d : Nat)  
  (h : arr1 ≠ []) :
  find_distance_value arr1 [] d = arr1.length := sorry

theorem find_distance_value_zero_distance
  (arr1 arr2 : List Int)
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :  
  find_distance_value arr1 arr2 0 = 
    (arr1.filter (fun x => x ∉ arr2)).length := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_distance_value [4, 5, 8] [10, 9, 1, 8] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_distance_value [1, 4, 2, 3] [-4, -3, 6, 10, 20, 30] 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_distance_value [2, 1, 100, 3] [-5, -2, 10, -3, 7] 6
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible