Jon Snow is on the lookout for some orbs required to defeat the white walkers. There are k different types of orbs and he needs at least one of each. One orb spawns daily at the base of a Weirwood tree north of the wall. The probability of this orb being of any kind is equal. As the north of wall is full of dangers, he wants to know the minimum number of days he should wait before sending a ranger to collect the orbs such that the probability of him getting at least one of each kind of orb is at least $\frac{p_{i} - \epsilon}{2000}$, where ε < 10^{ - 7}.

To better prepare himself, he wants to know the answer for q different values of p_{i}. Since he is busy designing the battle strategy with Sam, he asks you for your help.

-----Input-----

First line consists of two space separated integers k, q (1 ≤ k, q ≤ 1000) — number of different kinds of orbs and number of queries respectively.

Each of the next q lines contain a single integer p_{i} (1 ≤ p_{i} ≤ 1000) — i-th query.

-----Output-----

Output q lines. On i-th of them output single integer — answer for i-th query.

-----Examples-----
Input
1 1
1

Output
1

Input
2 2
1
2

Output
2
2

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded