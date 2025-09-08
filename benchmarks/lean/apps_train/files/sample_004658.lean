/-
You're in the casino, playing Roulette, going for the "1-18" bets only and desperate to beat the house and so you want to test how effective the [Martingale strategy](https://en.wikipedia.org/wiki/Martingale_(betting_system)) is. 

You will be given a starting cash balance and an array of binary digits to represent a win (`1`) or a loss (`0`). Return your balance after playing all rounds.

*The Martingale strategy*

You start with a stake of `100` dollars. If you lose a round, you lose the stake placed on that round and you double the stake for your next bet. When you win, you win 100% of the stake and revert back to staking 100 dollars on your next bet.

## Example
```
martingale(1000, [1, 1, 0, 0, 1]) === 1300
```
Explanation:
* you win your 1st round: gain $100, balance = 1100
* you win the 2nd round: gain $100, balance = 1200
* you lose the 3rd round: lose $100 dollars, balance = 1100
* double stake for 4th round and lose: staked $200, lose $200, balance = 900
* double stake for 5th round and win: staked $400, won $400, balance = 1300

**Note: Your balance is allowed to go below 0.**
-/

-- <vc-helpers>
-- </vc-helpers>

def martingale (bank : Float) (outcomes : List Int) : Float :=
  sorry

theorem martingale_monotonic_bank {bank : Float} {outcomes : List Int} :
  ∀ inc : Float, inc ≥ 0 → martingale (bank + inc) outcomes ≥ martingale bank outcomes := by
  sorry

theorem martingale_all_wins {bank : Float} {outcomes : List Int} :
  (∀ x ∈ outcomes, x = 1) → 
  martingale bank outcomes = bank + (outcomes.length.toFloat * 100) := by
  sorry

theorem martingale_empty_outcomes {bank : Float} :
  martingale bank [] = bank := by
  sorry

theorem martingale_returns_float {bank : Float} {outcomes : List Int} :
  ∃ x : Float, martingale bank outcomes = x := by
  sorry

theorem martingale_consecutive_losses {n : Nat} :
  let losses := List.replicate n 0
  martingale 0 losses = -(List.range n).foldl (fun acc i => acc + 100 * (Float.pow 2 i.toFloat)) 0 := by
  sorry

/-
info: 1300
-/
-- #guard_msgs in
-- #eval martingale 1000 [1, 1, 0, 0, 1]

/-
info: 800
-/
-- #guard_msgs in
-- #eval martingale 500 [1, 1, 1]

/-
info: -600
-/
-- #guard_msgs in
-- #eval martingale 100 [0, 0, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded