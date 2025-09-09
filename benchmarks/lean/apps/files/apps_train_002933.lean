-- <vc-helpers>
-- </vc-helpers>

def unflatten (arr : List Nat) : List (Sum (List Nat) Nat) := sorry

def flatten {α} (l : List (Sum (List α) α)) : List α := sorry

theorem unflatten_type (arr : List Nat) :
  unflatten arr ≠ [] → unflatten arr ≠ [] := sorry

theorem unflatten_preserves_flatten (arr : List Nat) (h : arr ≠ []) :
  flatten (unflatten arr) = arr := sorry

theorem unflatten_sublist_len (arr : List Nat) (sublist : List Nat) :
  (Sum.inl sublist) ∈ unflatten arr → 
  sublist ≠ [] → sublist[0]! ≥ sublist.length := sorry

theorem unflatten_small_nums (arr : List Nat) (item : Nat) :
  (Sum.inr item) ∈ unflatten arr →
  item ≤ 2 := sorry

theorem unflatten_all_small (arr : List Nat) :
  (∀ x ∈ arr, x ≤ 2) → unflatten arr = arr.map Sum.inr := sorry

theorem unflatten_single_large (n : Nat) :
  n ≥ 3 → unflatten [n] = [Sum.inl [n]] := sorry

/-
info: [[3, 5, 2], 1]
-/
-- #guard_msgs in
-- #eval unflatten [3, 5, 2, 1]

/-
info: [1, [4, 5, 2, 1], 2, [4, 5, 2, 6], 2, [3, 3]]
-/
-- #guard_msgs in
-- #eval unflatten [1, 4, 5, 2, 1, 2, 4, 5, 2, 6, 2, 3, 3]

/-
info: [[99, 1, 1, 1]]
-/
-- #guard_msgs in
-- #eval unflatten [99, 1, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded