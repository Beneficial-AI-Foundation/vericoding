You are given a list of directions in the form of a list:

goal = ["N", "S", "E", "W"]

Pretend that each direction counts for 1 step in that particular direction.

Your task is to create a function called directions, that will return a reduced list that will get you to the same point.The order of directions must be returned as N then S then E then W.

If you get back to beginning, return an empty array.

def Direction.toString : Direction → String
  | Direction.N => "N"
  | Direction.S => "S"
  | Direction.E => "E"
  | Direction.W => "W"

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
