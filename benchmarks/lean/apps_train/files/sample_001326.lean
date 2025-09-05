Chef Hari has got a new obsession now: he has started playing chess (read about it here) and he is liking this game very much. Since Hari has spent several months playing chess with his friends, he has now decided to take part in some chess tournament in Cheftown.

There are currently two tournaments going on in Cheftown and each tournament has its own entry fee. Due to this economical restriction and his budget, Hari can take part in only one tournament.

The entry fee for first tournament is F1 units of money. The structure of tournament is as follows: first there will be group matches and then there will be finals. If Hari reaches in finals and wins it, he'll get R1 units of money. If after reaching in finals, Hari loses, he'll get R2 units of money. If Hari fails to reach in finals, he'll get nothing. The probability of reaching in finals of first tournament for Hari is p1 and probability of winning in finals after reaching is p2.

The entry fee for second tournament is F2 units of money. The structure of tournament is as follows: first there will be group matches and then there will be finals. If Hari reaches in finals, he'll immediately get R3 units of money, otherwise he'll get nothing. If after reaching in finals, Hari wins, he'll get R4 units of money. The probability of reaching in finals of second tournament for Hari is p3 and probability of winning in finals after reaching is p4.

Now, Hari wants to maximise his profit. He wants to know which tournament he should participate in such that his expected profit is maximised. Help Hari in deciding this.

Note:
In the tournaments of Cheftown, the game never ends with a draw. So, either Hari wins a game, or he loses.

-----Input-----

First line of the input contains T, the number of test cases. The description of each test case is as following:

First line of each test case contains 6 integers F1, F2, R1, R2, R3 and R4.

Next line of each test case contains 4 floating point numbers p1, p2, p3 and p4.
Each number has exactly 2 digits after decimal point.

-----Output-----

For each test case, output a single line having "FIRST" if expected profit of first tournament is maximum or "SECOND" if expected profit of second tournament is maximum or "BOTH" if expected profits of both the tournaments is exactly same.

-----Constraints-----
- 1 ≤ T ≤ 100
- 1 ≤ F1, F2, R1, R2, R3, R4 ≤ 100
- 0.00 ≤ p1, p2, p3, p4 ≤ 1.00

-----Subtasks-----
Subtask#1: 30 points
- p1 = p3 and p2 = p4

Subtask#2: 70 points
- All usual constraints.

-----Example-----
Input:
2
30 50 70 10 40 30
0.25 0.10 0.30 0.05
50 36 80 38 65 32
0.55 0.12 0.33 0.54

Output:
FIRST
SECOND

-----Explanation-----

In the first case, the expected profit for first tournament is -26.00 and expected profit for second tournament is -37.55. So, first tournament has better expected profit.

In the second case, the expected profit for first tournament is -26.328 and expected profit for second tournament is -8.8476. So, second tournament has better expected profit.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded