# Task
 Pac-Man got lucky today! Due to minor performance issue all his enemies have frozen. Too bad Pac-Man is not brave enough to face them right now, so he doesn't want any enemy to see him. 

 Given a gamefield of size `N` x `N`, Pac-Man's position(`PM`) and his enemies' positions(`enemies`), your task is to count the number of coins he can collect without being seen.

 An enemy can see a Pac-Man if they are standing on the same row or column. 

 It is guaranteed that no enemy can see Pac-Man on the starting position. There is a coin on each empty square (i.e. where there is no Pac-Man or enemy).

# Example

 For `N = 4, PM = [3, 0], enemies = [[1, 2]]`, the result should be `3`.
```
Let O represent coins, P - Pac-Man and E - enemy.
OOOO
OOEO
OOOO
POOO```
Pac-Man cannot cross row 1 and column 2. 

 He can only collect coins from points `(2, 0), (2, 1) and (3, 1)`, like this:
 ```
x is the points that Pac-Man can collect the coins.
OOOO
OOEO
xxOO
PxOO
 ```

# Input/Output

 - `[input]` integer `N`

  The field size.

 - `[input]` integer array `PM`

  Pac-Man's position (pair of integers)

 - `[input]` 2D integer array `enemies`

  Enemies' positions (array of pairs)

 - `[output]` an integer

  Number of coins Pac-Man can collect.

# More PacMan Katas

 - [Play PacMan: Devour all](https://www.codewars.com/kata/575c29d5fcee86cb8b000136)

 - [Play PacMan 2: The way home](https://www.codewars.com/kata/575ed46e23891f67d90000d8)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded