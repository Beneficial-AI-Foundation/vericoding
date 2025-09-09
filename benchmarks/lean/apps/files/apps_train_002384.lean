def max_power (s : List Char) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def max_run (s : List Char) : Nat :=
  sorry

theorem max_power_lower_bound (s : List Char) (h : s.length > 0) : 
  max_power s ≥ 1 :=
sorry

theorem max_power_upper_bound (s : List Char) :
  max_power s ≤ s.length :=
sorry

theorem max_power_equals_longest_run (s : List Char) (h : s.length > 0) :
  max_power s = max_run s :=
sorry

theorem max_power_single_char (s : List Char) (h : s.length > 0) 
  (h' : ∀ (i j : Fin s.length), s.get i = s.get j) :
  max_power s = s.length :=
sorry

theorem max_power_alternating (s : List Char) (h : s.length ≥ 2)
  (h' : ∀ (i : Fin s.length), 
    if i.val % 2 = 0 
    then s.get i = 'a'
    else s.get i = 'b') :
  max_power s = 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_power "leetcode"

/-
info: 5
-/
-- #guard_msgs in
-- #eval max_power "abbcccddddeeeeedcba"

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_power "tourist"

-- Apps difficulty: introductory
-- Assurance level: guarded