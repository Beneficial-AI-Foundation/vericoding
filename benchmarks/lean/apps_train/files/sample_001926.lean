Eighth-grader Vova is on duty today in the class. After classes, he went into the office to wash the board, and found on it the number n. He asked what is this number and the teacher of mathematics Inna Petrovna answered Vova that n is the answer to the arithmetic task for first-graders. In the textbook, a certain positive integer x was given. The task was to add x to the sum of the digits of the number x written in decimal numeral system.

Since the number n on the board was small, Vova quickly guessed which x could be in the textbook. Now he wants to get a program which will search for arbitrary values of the number n for all suitable values of x or determine that such x does not exist. Write such a program for Vova.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 10^9).

-----Output-----

In the first line print one integer k — number of different values of x satisfying the condition. 

In next k lines print these values in ascending order.

-----Examples-----
Input
21

Output
1
15

Input
20

Output
0

-----Note-----

In the first test case x = 15 there is only one variant: 15 + 1 + 5 = 21.

In the second test case there are no such x.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded