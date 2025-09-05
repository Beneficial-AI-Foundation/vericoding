Jeff has become friends with Furik. Now these two are going to play one quite amusing game.

At the beginning of the game Jeff takes a piece of paper and writes down a permutation consisting of n numbers: p_1, p_2, ..., p_{n}. Then the guys take turns to make moves, Jeff moves first. During his move, Jeff chooses two adjacent permutation elements and then the boy swaps them. During his move, Furic tosses a coin and if the coin shows "heads" he chooses a random pair of adjacent elements with indexes i and i + 1, for which an inequality p_{i} > p_{i} + 1 holds, and swaps them. But if the coin shows "tails", Furik chooses a random pair of adjacent elements with indexes i and i + 1, for which the inequality p_{i} < p_{i} + 1 holds, and swaps them. If the coin shows "heads" or "tails" and Furik has multiple ways of adjacent pairs to take, then he uniformly takes one of the pairs. If Furik doesn't have any pair to take, he tosses a coin one more time. The game ends when the permutation is sorted in the increasing order.

Jeff wants the game to finish as quickly as possible (that is, he wants both players to make as few moves as possible). Help Jeff find the minimum mathematical expectation of the number of moves in the game if he moves optimally well.

You can consider that the coin shows the heads (or tails) with the probability of 50 percent.

-----Input-----

The first line contains integer n (1 ≤ n ≤ 3000). The next line contains n distinct integers p_1, p_2, ..., p_{n} (1 ≤ p_{i} ≤ n) — the permutation p. The numbers are separated by spaces.

-----Output-----

In a single line print a single real value — the answer to the problem. The answer will be considered correct if the absolute or relative error doesn't exceed 10^{ - 6}.

-----Examples-----
Input
2
1 2

Output
0.000000

Input
5
3 5 2 4 1

Output
13.000000

-----Note-----

In the first test the sequence is already sorted, so the answer is 0.

def CumTree.vstavi : CumTree → Int → Unit := sorry
def CumTree.manjsi : CumTree → Int → Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
