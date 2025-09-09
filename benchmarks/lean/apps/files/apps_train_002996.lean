-- <vc-helpers>
-- </vc-helpers>

def totalAmountVisible (topNum : Nat) (numSides : Nat) : Nat := sorry

theorem total_visible_non_negative (topNum : Nat) (numSides : Nat) 
    (h : 0 < topNum ∧ topNum ≤ numSides) : 
  totalAmountVisible topNum numSides ≥ 0 := sorry

theorem total_visible_less_than_sum (topNum : Nat) (numSides : Nat)
    (h : 0 < topNum ∧ topNum ≤ numSides) :
  totalAmountVisible topNum numSides ≤ (numSides * (numSides + 1)) / 2 := sorry

theorem total_visible_increases_from_one (topNum : Nat) (numSides : Nat)
    (h : 1 < topNum ∧ topNum ≤ numSides) :
  totalAmountVisible topNum numSides > totalAmountVisible 1 numSides := sorry

theorem total_visible_strictly_increasing (topNum : Nat) (numSides : Nat)
    (h : 0 < topNum ∧ topNum < numSides) :
  totalAmountVisible (topNum + 1) numSides > totalAmountVisible topNum numSides := sorry

theorem total_visible_equal_sides_special_case (n : Nat)
    (h : 0 < n) :
  totalAmountVisible n n = (n * (n + 1)) / 2 - 1 := sorry

/-
info: 19
-/
-- #guard_msgs in
-- #eval totalAmountVisible 5 6

/-
info: 208
-/
-- #guard_msgs in
-- #eval totalAmountVisible 19 20

/-
info: 48
-/
-- #guard_msgs in
-- #eval totalAmountVisible 4 10

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible