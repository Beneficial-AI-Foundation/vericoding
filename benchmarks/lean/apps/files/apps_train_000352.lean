-- <vc-helpers>
-- </vc-helpers>

def tileRectangle (n m : Nat) : Nat := sorry

theorem square_input {n : Nat} (h : n > 0) : 
  tileRectangle n n = 1 := sorry

theorem multiples {n : Nat} (h : n > 0) :
  tileRectangle n (2 * n) = 2 ∧ tileRectangle (2 * n) n = 2 := sorry

theorem lower_bound {n m : Nat} (hn : n > 0) (hm : m > 0) :
  tileRectangle n m ≥ 1 := sorry

theorem upper_bound {n m : Nat} (hn : n > 0) (hm : m > 0) :
  tileRectangle n m ≤ n * m := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval tile_rectangle 2 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval tile_rectangle 5 8

/-
info: 6
-/
-- #guard_msgs in
-- #eval tile_rectangle 11 13

-- Apps difficulty: interview
-- Assurance level: guarded