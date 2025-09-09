def countInversion (s : List Int) : Nat := sorry

def isSorted (s : List Int) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isAntiSorted (s : List Int) : Bool := sorry

theorem countInversion_nonnegative (s : List Int) :
  countInversion s ≥ 0 := sorry

theorem countInversion_sorted_zero (s : List Int) :
  isSorted s = true → countInversion s = 0 := sorry

theorem countInversion_reverse_sorted_max (s : List Int) :
  let maxInv := s.length * (s.length - 1) / 2
  isAntiSorted s = true → countInversion s ≤ maxInv := sorry

theorem countInversion_small_seq (s : List Int) : 
  s.length ≤ 1 → countInversion s = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_inversion (1, 2, 5, 3, 4, 7, 6)

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_inversion (0, 1, 2, 3)

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_inversion (3, 2, 1, 0)

-- Apps difficulty: introductory
-- Assurance level: unguarded