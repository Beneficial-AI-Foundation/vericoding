# Task
 You are the manager of the famous rescue team: The Knights. Your task is to assign your knights to a rescue missions on an infinite 2D-plane.

 Your knights can move only by `n-knight` jumps. 

 For example, if a knight has n = 2, they can only move exactly as a knight on a chess board. 

 If n = 3, they can move from (0, 0) to one of the following 8 points:

 `(3, 1) (3, -1), ( -3, 1), (-3, -1), (1, 3), (1, -3), (-1, 3) or (-1, -3).`

 You are given an array containing the `n`s of all of your knights `n-knight` jumps, and the coordinates (`x`, `y`) of a civilian who need your squad's help.

 Your head quarter is located at (0, 0). Your must determine if `at least one` of your knight can reach that point `(x, y)`.

# Input/Output

 - `[input]` integer array `N`

  The ways your knights move. 

  `1 <= N.length <=20`

 - `[input]` integer `x`

  The x-coordinate of the civilian

 - `[input]` integer `y`

  The y-coordinate of the civilian

 - `[output]` a boolean value

 `true` if one of your knights can reach point (x, y), `false` otherwise.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded