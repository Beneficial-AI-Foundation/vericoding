-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_cross (stones : List Nat) : Bool := sorry

theorem empty_stones :
  can_cross [] = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_stone :
  can_cross [0] = true := sorry

theorem stones_start_with_zero {stones : List Nat} (h : stones ≠ []) :
  stones.head! = 0 := sorry 

theorem stones_strictly_increasing {stones : List Nat} (i : Nat) 
  (h1 : i + 1 < stones.length) :
  stones[i]! < stones[i+1]! := sorry

theorem return_type_bool (stones : List Nat) :
  can_cross stones = true ∨ can_cross stones = false := sorry

theorem invalid_sequences_head {stones : List Nat} (h1 : stones.length ≥ 2) 
  (h2 : stones.head! ≠ 0) :
  can_cross stones = false := sorry

theorem invalid_sequences_monotone {stones : List Nat} (i : Nat) 
  (h1 : i + 1 < stones.length)
  (h2 : stones[i]! ≥ stones[i+1]!) :
  can_cross stones = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_cross [0, 1, 3, 5, 6, 8, 12, 17]

/-
info: False
-/
-- #guard_msgs in
-- #eval can_cross [0, 1, 2, 3, 4, 8, 9, 11]

/-
info: True
-/
-- #guard_msgs in
-- #eval can_cross [0, 1, 3, 4, 5, 7, 9, 10, 12]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded