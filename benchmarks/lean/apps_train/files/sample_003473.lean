Happy traveller [Part 1]

There is a play grid NxN; Always square! 

   0  1  2  3
0 [o, o, o, X]
1 [o, o, o, o]
2 [o, o, o, o]
3 [o, o, o, o]

You start from a random point. I mean, you are given the coordinates of your start position in format (row, col). 

And your TASK is to define the number of unique paths to reach position X (always in the top right corner).

From any point you can go only UP or RIGHT.

Implement a function count_paths(N, (row, col)) which returns int; 
Assume input params are always valid.

Example:

count_paths(1, (0, 0))
grid 1x1:

[X]
 You are already in the target point, so return 0

count_paths(2, (1, 0))
grid 2x2:

[o, X]
[@, o]
 You are at point @; you can move UP-RIGHT or RIGHT-UP, and there are 2 possible unique paths here

count_paths(2, (1, 1))
grid 2x2:

[o, X]
[o, @]
 You are at point @; you can move only UP, so there is 1 possible unique path here

count_paths(3, (1, 0))
grid 3x3:

[o, o, X]
[@, o, o]
[o, o, o]
 You are at point @; you can move UP-RIGHT-RIGHT or RIGHT-UP-RIGHT, or RIGHT-RIGHT-UP, and there are 3 possible unique paths here

I think it's pretty clear =)

btw. you can use preloaded Grid class, which constructs 2d array for you. It's very very basic and simple. You can use numpy instead or any other way to produce the correct answer =)
 grid = Grid(2, 2, 0) 
samegrid = Grid.square(2) will give you a grid[2][2], which you can print easily to console. 

print(grid)

[0, 0]
[0, 0]

Enjoy!

You can continue adventures:
Happy traveller [Part 2]

def choose (n m : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
