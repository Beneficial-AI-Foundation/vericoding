/-
Remember the movie with David Bowie: 'The Labyrinth'?

You can remember your childhood here: https://www.youtube.com/watch?v=2dgmgub8mHw

In this scene the girl is faced with two 'Knights" and two doors. One door leads the castle where the Goblin King and her kid brother is, the other leads to certain death. She can ask the 'Knights'  a question to find out which door is the right one to go in. But...

One of them always tells the truth, and the other one always lies.

In this Kata one of the 'Knights' is on a coffee break, leaving the other one to watch the doors. You have to determine if the one there is the Knight(Truth teller) or Knave(Liar) based off of what he ```says```

Create a function:
```
def knight_or_knave(says):
  # returns if knight or knave 
```
Your function should determine if the input '''says''' is True or False and then return:
```'Knight!'``` if True or ```'Knave! Do not trust.'``` if False

Input will be either boolean values, or strings.
The strings will be simple statements that will be either true or false, or evaluate to True or False. 

See example test cases for, well... examples

You will porbably need to ```eval(says)```

But note: Eval is evil, and is only here for this Kata as a game.

And remember the number one rule of The Labyrinth, even if it is easy, Don't ever say 'that was easy.'
-/

-- <vc-helpers>
-- </vc-helpers>

def knight_or_knave (s : String) : String := sorry

theorem knight_or_knave_numeric_comparison (a b : Int) :
  let expr := toString a ++ "==" ++ toString b
  let result := knight_or_knave expr
  (result = "Knight!" ∨ result = "Knave! Do not trust.") ∧
  (result = "Knight!" ↔ a = b) := sorry

theorem knight_or_knave_boolean (b : Bool) :
  let expr := toString b
  knight_or_knave expr = (if b then "Knight!" else "Knave! Do not trust.") := sorry

theorem knight_or_knave_arithmetic (a b : Int) :
  let expr := toString a ++ "+" ++ toString b ++ "==" ++ toString (a + b)
  knight_or_knave expr = "Knight!" := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded