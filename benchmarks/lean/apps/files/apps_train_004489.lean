-- <vc-preamble>
def sum (l : List Int) : Int := sorry
def maximum? (l : List Int) : Option Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def filterWithIndex (l : List Int) (f : Nat → Int → Bool) : List Int := sorry
def target_game (vals : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_game_nonneg (vals : List Int) 
  (h : vals ≠ []) : 
  target_game vals ≥ 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval target_game [1, 2, 3, 4]

/-
info: 15
-/
-- #guard_msgs in
-- #eval target_game [5, 5, 5, 5, 5]

/-
info: 5
-/
-- #guard_msgs in
-- #eval target_game [5, -2, -9, -4]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible