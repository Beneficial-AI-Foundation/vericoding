/-
# Task
 Four men, `a, b, c and d` are standing in a line, one behind another. 

 There's a wall between the first three people (a, b and c) and the last one (d).

 a, b and c are lined up in order of height, so that person a can see the backs of b and c, person b can see the back of c, and c can see just the wall.

 There are 4 hats, 2 black and 2 white. Each person is given a hat. None of them can see their own hat, but person a can see the hats of b and c, while person b can see the hat of person c. Neither c nor d can see any hats.

 Once a person figures out their hat's color, they shouts it. 

 ![](http://stuffbox.in/wp-content/uploads/2016/08/Guess-hat-colour-604x270.png)

 Your task is to return the person who will guess their hat first. You can assume that they will speak only when they reach a correct conclusion.

# Input/Output

 - `[input]` string `a`

  a's hat color ("white" or "black").

 - `[input]` string `b`

  b's hat color ("white" or "black").

 - `[input]` string `c`

  c's hat color ("white" or "black").

 - `[input]` string `d`

  d's hat color ("white" or "black").

 - `[output]` an integer

 The person to guess his hat's color first, `1 for a, 2 for b, 3 for c and 4 for d`.
-/

-- <vc-helpers>
-- </vc-helpers>

def guess_hat_color : Color → Color → Color → Color → Nat :=
  fun _ _ _ _ => sorry

theorem guess_hat_result_valid {a b c d : Color} :
  (guess_hat_color a b c d = 1) ∨ (guess_hat_color a b c d = 2) := 
  sorry

theorem guess_hat_equal_gives_one {a b c d : Color} :
  (guess_hat_color a b c d = 1) = (b = c) :=
  sorry 

theorem guess_hat_unequal_gives_two {a b c d : Color} :
  (guess_hat_color a b c d = 2) = (b ≠ c) :=
  sorry

theorem guess_hat_preserves_colors (a b c d : Color) :
  (a = Color.black ∨ a = Color.white) ∧
  (b = Color.black ∨ b = Color.white) ∧
  (c = Color.black ∨ c = Color.white) ∧
  (d = Color.black ∨ d = Color.white) :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval guess_hat_color "white" "black" "white" "black"

/-
info: 1
-/
-- #guard_msgs in
-- #eval guess_hat_color "white" "black" "black" "white"

-- Apps difficulty: introductory
-- Assurance level: guarded