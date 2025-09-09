/-
Let's imagine we have a popular online RPG. A player begins with a score of 0 in class E5. A1 is the highest level a player can achieve.

Now let's say the players wants to rank up to class E4. To do so the player needs to achieve at least 100 points to enter the qualifying stage.

Write a script that will check to see if the player has achieved at least 100 points in his class. If so, he enters the qualifying stage. 

In that case, we return, ```"Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up."```.

Otherwise return, ```False/false``` (according to the language n use).

NOTE:  Remember, in C# you have to cast your output value to Object type!
-/

-- <vc-helpers>
-- </vc-helpers>

def playerRankUp (points : Int) : Bool ⊕ String := sorry 

theorem playerRankUp_return_type (points : Int) : 
  (∃ b : Bool, playerRankUp points = Sum.inl b) ∨ 
  (∃ s : String, playerRankUp points = Sum.inr s) := sorry

theorem below_threshold (points : Int) :
  points < 100 → playerRankUp points = Sum.inl false := sorry 

theorem above_threshold (points : Int) :
  points ≥ 100 → 
  playerRankUp points = Sum.inr "Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up." := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval playerRankUp 45

/-
info: 'Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up.'
-/
-- #guard_msgs in
-- #eval playerRankUp 100

/-
info: 'Well done! You have advanced to the qualifying stage. Win 2 out of your next 3 games to rank up.'
-/
-- #guard_msgs in
-- #eval playerRankUp 105

-- Apps difficulty: introductory
-- Assurance level: unguarded