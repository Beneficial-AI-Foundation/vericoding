-- <vc-helpers>
-- </vc-helpers>

def find_min_moves (n: Nat) (arr: List Int) : Nat := sorry

theorem find_min_moves_result_range {n: Nat} {arr: List Int} (h: n > 0) :
  find_min_moves n arr ≤ n := sorry

theorem find_min_moves_result_nonneg {n: Nat} {arr: List Int} :
  find_min_moves n arr ≥ 0 := sorry

theorem find_min_moves_all_same {n: Nat} {v: Int} (h: n > 0) :
  find_min_moves n (List.replicate n v) = 0 := sorry

theorem find_min_moves_single_different {n: Nat} {v w: Int} (h1: n ≥ 2) (h2: v ≠ w) :
  find_min_moves n ([v] ++ List.replicate (n-1) w) = 1 := sorry

theorem find_min_moves_reverse {n: Nat} {arr: List Int} (h: n > 0) :
  find_min_moves n arr = find_min_moves n arr.reverse := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min_moves 5 [1, 1, 1, 1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_moves 4 [9, 8, 1, 8]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_moves 2 [1, 9]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible