-- <vc-preamble>
def is_valid_shot (n : Nat) (shot : Nat × Nat) : Bool :=
  1 ≤ shot.1 ∧ shot.1 ≤ n ∧ shot.2 ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_parrot_hunt (n : Nat) (init_parrots : List Nat) (num_shots : Nat) (shots : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_parrot_hunt_no_shots_preserves_input
  (n : Nat) (init_parrots : List Nat) (h : init_parrots.length = n) :
  solve_parrot_hunt n init_parrots 0 [] = init_parrots :=
sorry
-- </vc-theorems>