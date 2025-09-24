-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_new_notes (salary: Nat) (bills: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_new_notes_edge_zero_salary : 
  get_new_notes 0 [] = 0 := sorry

theorem get_new_notes_edge_min_note : 
  get_new_notes 5 [] = 1 := sorry

theorem get_new_notes_edge_no_remainder :
  get_new_notes 100 [100] = 0 := sorry

theorem get_new_notes_edge_insufficient :
  get_new_notes 100 [200] = 0 := sorry

/-
info: 188
-/
-- #guard_msgs in
-- #eval get_new_notes 2000 [500, 160, 400]

/-
info: 122
-/
-- #guard_msgs in
-- #eval get_new_notes 1260 [500, 50, 100]

/-
info: 1
-/
-- #guard_msgs in
-- #eval get_new_notes 2000 [500, 495, 100, 900]
-- </vc-theorems>