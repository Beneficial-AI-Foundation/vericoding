/-
*This kata is based on [Project Euler Problem #349](https://projecteuler.net/problem=349). You may want to start with solving [this kata](https://www.codewars.com/kata/langtons-ant) first.*

---

[Langton's ant](https://en.wikipedia.org/wiki/Langton%27s_ant) moves on a regular grid of squares that are coloured either black or white.
The ant is always oriented in one of the cardinal directions (left, right, up or down) and moves  according to the following rules:
- if it is on a black square, it flips the colour of the square to white, rotates 90 degrees counterclockwise and moves forward one square.
- if it is on a white square, it flips the colour of the square to black, rotates 90 degrees clockwise and moves forward one square.

Starting with a grid that is **entirely white**, how many squares are black after `n` moves of the ant?

**Note:** `n` will go as high as 10^(20)

---

## My other katas

If you enjoyed this kata then please try [my other katas](https://www.codewars.com/collections/katas-created-by-anter69)! :-)

#### *Translations are welcome!*
-/

def langtons_ant (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def abs (n : Nat) : Nat :=
  n

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

-- Apps difficulty: introductory
-- Assurance level: guarded