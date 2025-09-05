There is a new prodigy in town and he has challenged people to a game. They have to give him an integer N and he will immediately respond with a number which has more than N factors.
What the prodigy really does is to do some complex calculations in his head to find out the smallest integer with more than N factors. However, he has a weakness - he knows to do those calculation only on numbers up to 1019, so if the answer to be reported is more than 1019, he will not be able to come up with his solution and will lose the game.
Given the integer the people give to the prodigy, you need to report whether he wins the game or not. If he wins, also output his answer.

-----Input-----
The first line of input contains T (T ≤ 25), the number of test cases. Following this are T lines, each containing an integer N (1 ≤ N ≤ 109) - the number which is given to the prodigy.

-----Output-----
Output one line per test case. If the smallest integer X with more than N factors is bigger than 1019 so that the prodigy does not win, print "lose". Otherwise print "win X" (quotes for clarity).

-----Example-----
Input:
3
3
5
12345678

Output:
win 6
win 12
lose

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
