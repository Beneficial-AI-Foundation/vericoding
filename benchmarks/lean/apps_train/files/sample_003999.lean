It's the most hotly anticipated game of the school year - Gryffindor vs Slytherin! Write a function which returns the winning team. 

You will be given two arrays with two values. 

The first given value is the number of points scored by the team's Chasers and the second a string with a 'yes' or 'no' value if the team caught the golden snitch!

The team who catches the snitch wins their team an extra 150 points - but doesn't always win them the game.

If the score is a tie return "It's a draw!""

** The game only ends when someone catches the golden snitch, so one array will always include 'yes' or 'no.' Points scored by Chasers can be any positive integer.

def calculateScore (initialScore: Nat) (snitch: SnitchResult) : Nat :=
  match snitch with
  | SnitchResult.Yes => initialScore + 150
  | SnitchResult.No => initialScore

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded