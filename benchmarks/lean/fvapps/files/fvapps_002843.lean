-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def monty_hall (door : Nat) (guesses : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem monty_hall_single_guess (door : Nat) (guess : Nat)
  (h1 : 1 ≤ door) (h2 : door ≤ 3) (h3 : 1 ≤ guess) (h4 : guess ≤ 3) :
  monty_hall door [guess] = 0 ∨ monty_hall door [guess] = 100 :=
  sorry
-- </vc-theorems>