-- <vc-preamble>
def langtons_ant (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (n : Nat) : Nat :=
  n
-- </vc-definitions>

-- <vc-theorems>
theorem langtons_ant_non_negative (n : Nat) :
  langtons_ant n ≥ 0 :=
sorry

theorem langtons_ant_first_moves (n : Nat) :
  (n = 0 → langtons_ant n = 0) ∧ 
  (n = 1 → langtons_ant n = 1) ∧
  (n ≥ 2 → langtons_ant n ≤ n) :=
sorry

theorem langtons_ant_periodic (n1 n2 : Nat) :
  n1 ≥ 9977 → n2 ≥ 9977 →
  (n1 - n2) % 104 = 0 →
  (if langtons_ant n1 ≥ langtons_ant n2 
   then langtons_ant n1 - langtons_ant n2
   else langtons_ant n2 - langtons_ant n1) = 
    12 * (if (n1 - 9977) / 104 ≥ (n2 - 9977) / 104
          then (n1 - 9977) / 104 - (n2 - 9977) / 104
          else (n2 - 9977) / 104 - (n1 - 9977) / 104) :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval langtons_ant 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval langtons_ant 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval langtons_ant 2

/-
info: 6
-/
-- #guard_msgs in
-- #eval langtons_ant 10

/-
info: 20
-/
-- #guard_msgs in
-- #eval langtons_ant 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded