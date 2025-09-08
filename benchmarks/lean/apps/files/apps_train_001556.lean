/-
# Connect Four

Take a look at wiki description of Connect Four game:

[Wiki Connect Four](https://en.wikipedia.org/wiki/Connect_Four)

The grid is 6 row by 7 columns, those being named from A to G.

You will receive a list of strings showing the order of the pieces which dropped in columns:

```python
  pieces_position_list = ["A_Red",
                          "B_Yellow",
                          "A_Red",
                          "B_Yellow",
                          "A_Red",
                          "B_Yellow",
                          "G_Red",
                          "B_Yellow"]
```

The list may contain up to 42 moves and shows the order the players are playing.

The first player who connects four items of the same color is the winner.

You should return "Yellow", "Red" or "Draw" accordingly.
-/

def who_is_winner (moves : List String) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def columnHeight (moves : List String) (col : String) : Nat :=
  sorry

theorem valid_result_states (moves : List String) :
  let result := who_is_winner moves
  result = "Red" ∨ result = "Yellow" ∨ result = "Draw" := by
  sorry

theorem column_height_bound (moves : List String) (col : String) :
  columnHeight moves col ≤ 6 := by
  sorry

/-
info: 'Yellow'
-/
-- #guard_msgs in
-- #eval who_is_winner ["A_Red", "B_Yellow", "A_Red", "B_Yellow", "A_Red", "B_Yellow", "G_Red", "B_Yellow"]

/-
info: 'Red'
-/
-- #guard_msgs in
-- #eval who_is_winner ["A_Yellow", "B_Red", "B_Yellow", "C_Red", "G_Yellow", "C_Red", "C_Yellow", "D_Red", "G_Yellow", "D_Red", "G_Yellow", "D_Red", "F_Yellow", "E_Red", "D_Yellow"]

/-
info: 'Yellow'
-/
-- #guard_msgs in
-- #eval who_is_winner ["C_Yellow", "E_Red", "G_Yellow", "B_Red", "D_Yellow", "B_Red", "B_Yellow", "G_Red", "C_Yellow", "C_Red", "D_Yellow", "F_Red", "E_Yellow", "A_Red", "A_Yellow", "G_Red", "A_Yellow", "F_Red", "F_Yellow", "D_Red", "B_Yellow", "E_Red", "D_Yellow", "A_Red", "G_Yellow", "D_Red", "D_Yellow", "C_Red"]

-- Apps difficulty: interview
-- Assurance level: unguarded