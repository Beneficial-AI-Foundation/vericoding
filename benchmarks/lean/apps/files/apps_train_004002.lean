-- <vc-helpers>
-- </vc-helpers>

def count_targets (n : Nat) (lst : List Int) : Nat := sorry

theorem count_targets_non_negative (n : Nat) (lst : List Int) : 
  count_targets n lst ≥ 0 := sorry

theorem count_targets_upper_bound (n : Nat) (lst : List Int) :
  count_targets n lst ≤ max 0 (lst.length - n) := sorry

theorem count_targets_empty_list (n : Nat) :
  count_targets n [] = 0 := sorry

theorem count_targets_n_geq_length (n : Nat) (lst : List Int) :
  n ≥ lst.length → count_targets n lst = 0 := sorry 

theorem count_targets_shift_zero (lst : List Int) :
  count_targets 0 lst = lst.length := sorry

theorem count_targets_shift_one (lst : List Int) :
  lst ≠ [] →
  count_targets 1 lst = 
    ((lst.zip (lst.drop 1)).filter (fun p => p.1 = p.2)).length := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_targets 1 [1, 1, 1, 1, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_targets 2 [1, 2, 1, 2, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_targets 1 []

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible