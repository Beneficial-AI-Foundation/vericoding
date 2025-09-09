-- <vc-helpers>
-- </vc-helpers>

def canIPlay (now start finish : Nat) : Bool := sorry

theorem canIPlay_symmetry_24 (now start finish : Nat) :
  canIPlay now start finish = canIPlay (now + 24) start finish := sorry

theorem canIPlay_symmetry_start_finish (now start finish : Nat) :
  canIPlay now start finish = canIPlay now (start + 24) (finish + 24) := sorry

theorem canIPlay_relative_times (now start finish : Nat) :
  canIPlay now start finish = 
  canIPlay (now - start) 0 ((finish - start) % 24) := sorry

theorem canIPlay_same_start_finish (now start : Nat) :
  ¬(canIPlay now start start) := sorry

theorem canIPlay_window_contains_start 
  (start window : Nat) (h : 0 < window) (h2 : window < 24) :
  canIPlay start start ((start + window) % 24) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_i_play 13 10 15

/-
info: False
-/
-- #guard_msgs in
-- #eval can_i_play 15 8 12

/-
info: True
-/
-- #guard_msgs in
-- #eval can_i_play 0 22 1

-- Apps difficulty: introductory
-- Assurance level: unguarded