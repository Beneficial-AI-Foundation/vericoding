-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_amazing_numbers (n : Nat) (arr : List Nat) : List Int := sorry

theorem example_case_1 (n : Nat) (arr : List Nat)
  (hn : n = 5)
  (harr : arr = [1,2,3,4,5]) :
  find_amazing_numbers n arr = [-1,-1,3,2,1] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem example_case_2 (n : Nat) (arr : List Nat)  
  (hn : n = 5)
  (harr : arr = [4,4,4,4,2]) :
  find_amazing_numbers n arr = [-1,4,4,4,2] := sorry

theorem example_case_3 (n : Nat) (arr : List Nat)
  (hn : n = 6) 
  (harr : arr = [1,3,1,5,3,1]) :
  find_amazing_numbers n arr = [-1,-1,1,1,1,1] := sorry

/-
info: [-1, -1, 3, 2, 1]
-/
-- #guard_msgs in
-- #eval find_amazing_numbers 5 [1, 2, 3, 4, 5]

/-
info: [-1, 4, 4, 4, 2]
-/
-- #guard_msgs in
-- #eval find_amazing_numbers 5 [4, 4, 4, 4, 2]

/-
info: [-1, -1, 1, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval find_amazing_numbers 6 [1, 3, 1, 5, 3, 1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded