You've just recently been hired to calculate scores for a  Dart Board game!

Scoring specifications:

* 0 points - radius above 10
* 5 points - radius between 5 and 10 inclusive
* 10 points - radius less than 5

**If all radii are less than 5, award 100 BONUS POINTS!**

Write a function that accepts an array of radii (can be integers and/or floats), and returns a total score using the above specification.

An empty array should return 0.

## Examples:

def score_throws (radiuses : List Float) : Nat := sorry

theorem score_throws_empty : 
  score_throws [] = 0 := sorry

def throw_points (r : Float) : Nat :=
  if r < 5 then 10
  else if r ≤ 10 then 5
  else 0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
