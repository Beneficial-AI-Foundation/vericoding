-- <vc-helpers>
-- </vc-helpers>

def monty_hall (door : Nat) (guesses : List Nat) : Nat :=
  sorry

theorem monty_hall_single_guess (door : Nat) (guess : Nat)
  (h1 : 1 ≤ door) (h2 : door ≤ 3) (h3 : 1 ≤ guess) (h4 : guess ≤ 3) :
  monty_hall door [guess] = 0 ∨ monty_hall door [guess] = 100 :=
  sorry

/-
info: 70
-/
-- #guard_msgs in
-- #eval monty_hall 1 [1, 2, 2, 2, 3, 2, 1, 3, 1, 3]

/-
info: 55
-/
-- #guard_msgs in
-- #eval monty_hall 2 [2, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3]

/-
info: 75
-/
-- #guard_msgs in
-- #eval monty_hall 3 [1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2, 3, 1, 1, 2]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible