-----Problem-----

There is an infinite one dimensional array ranging from (-infinity, infinity).A Zombie is currently at cell number 0. The zombie wants to reach cell number H. The Zombie moves in only two ways. The Zombie either

Makes U steps to the right (positive side) or

Makes D steps to the left (negative side).

Your task is to find the minimum number of moves the Zombie require to reach the goal.

-----Input-----

The first line contains the number of test cases T. Each of the next T lines contains 3 space

separated integers, H U D.

-----Output-----

For each test case, output one line with an integer, the minimum number of moves required to reach H from 0. If it is impossible, print -1 instead.

-----Constraints-----

- 

T ≤ 10000

- 

1 ≤ H, U, D ≤ 109

-----Sample Input-----
2

3 2 1

3 2 2

-----Sample Output-----
3

-1

-----Explanation-----

- 

In the first sample case, first move 2 steps to the right to reach cell number 2. Then 1 step to the left  to reach cell number 1 and finally 2 more steps to the right to reach the goal. Thus 3 moves are required

which is the minimum.

- 

Because both U and D are even, you will always be in an even cell.Thus there is no way to reach cell      number 3.

p { text-align:justify }

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
