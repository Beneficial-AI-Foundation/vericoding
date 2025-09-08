/-
Stacey is a big [AD&D](https://en.wikipedia.org/wiki/Dungeons_%26_Dragons) games nerd. Moreover, she's a munchkin. Not a [cat breed](https://en.wikipedia.org/wiki/Munchkin_cat), but a person who likes to get maximum efficiency of their character.

As you might know, many aspects of such games are modelled by rolling dice and checking it against a threshold value determined by various aspects.
Stacey wants to always control the situation and know whether she can beat the foe with certain special ability or not. Unfortunately she doesn't know probabilty theory well enough. Help Stacey by providing a calculating utility for her.

P.S.: Stacey says that she has tried to implement a calculator by Monte-Carlo modelling: calling rand() in a loop, but she hasn't been satisfied with precision of this method.

### Examples

`P(1d6 >= 4)` means the chance of getting 4 points or higher on a regular cubic die. Obviously the chance is `3/6` cause there're 6 possibilities in total (1, 2, 3, 4, 5, 6) and only three of them are >= 4: (4, 5, 6)

`P(2d6 >= 3)` gives us `35/36`, cause the only possibility to get < 3 is rolling exactly 1+1.
Exactly 2 as sum of two dice appears only if both have 1. While total amount of different outcomes is 6\*6 = 36. Hence resulting probability is 1-1/36, which is 35/36

### Your task

is to write a function, which will calculate the probability of that a die with `N` sides rolled `M` times (`MdN` in AD&D notation) will get at least `T` points. We don't add modifiers cause they are already incorporated into the threshold.

Input arguments will be valid integers with the following limits:

- `rolls` 1..20
- `sides` 2..100
- `threshold` 1..2000
-/

-- <vc-helpers>
-- </vc-helpers>

def roll_dice (rolls: Nat) (sides: Nat) (threshold: Nat) : Float := sorry

theorem roll_dice_probability_bounds
    (rolls: Nat) (sides: Nat) (threshold: Nat)
    (h1: 1 ≤ rolls) (h2: rolls ≤ 10)
    (h3: 1 ≤ sides) (h4: sides ≤ 20)
    (h5: 1 ≤ threshold) (h6: threshold ≤ 200) :
    0 ≤ roll_dice rolls sides threshold ∧ roll_dice rolls sides threshold ≤ 1 := sorry

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

-- Apps difficulty: interview
-- Assurance level: guarded