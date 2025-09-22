-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roll_dice (rolls: Nat) (sides: Nat) (threshold: Nat) : Float := sorry

theorem roll_dice_probability_bounds
    (rolls: Nat) (sides: Nat) (threshold: Nat)
    (h1: 1 ≤ rolls) (h2: rolls ≤ 10)
    (h3: 1 ≤ sides) (h4: sides ≤ 20)
    (h5: 1 ≤ threshold) (h6: threshold ≤ 200) :
    0 ≤ roll_dice rolls sides threshold ∧ roll_dice rolls sides threshold ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roll_dice_impossible_threshold
    (rolls: Nat) (sides: Nat)
    (h1: 1 ≤ rolls) (h2: rolls ≤ 10)
    (h3: 1 ≤ sides) (h4: sides ≤ 20) :
    roll_dice rolls sides (rolls * sides + 1) = 0 := sorry

theorem roll_dice_guaranteed_threshold
    (rolls: Nat) (sides: Nat)
    (h1: 1 ≤ rolls) (h2: rolls ≤ 10)
    (h3: 1 ≤ sides) (h4: sides ≤ 20) :
    roll_dice rolls sides rolls = 1 := sorry

theorem roll_dice_monotonicity
    (rolls: Nat) (sides: Nat) (threshold: Nat)
    (h1: 1 ≤ rolls) (h2: rolls ≤ 10)
    (h3: 1 ≤ sides) (h4: sides ≤ 20)
    (h5: 1 ≤ threshold) (h6: threshold ≤ 200)
    (h7: threshold < rolls * sides) :
    roll_dice rolls sides threshold ≥ roll_dice rolls sides (threshold + 1) := sorry
-- </vc-theorems>