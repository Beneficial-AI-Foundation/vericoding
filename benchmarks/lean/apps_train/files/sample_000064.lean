You and your friend are playing the game Mortal Kombat XI. You are trying to pass a challenge tower. There are $n$ bosses in this tower, numbered from $1$ to $n$. The type of the $i$-th boss is $a_i$. If the $i$-th boss is easy then its type is $a_i = 0$, otherwise this boss is hard and its type is $a_i = 1$.

During one session, either you or your friend can kill one or two bosses (neither you nor your friend can skip the session, so the minimum number of bosses killed during one session is at least one). After your friend session, your session begins, then again your friend session begins, your session begins, and so on. The first session is your friend's session.

Your friend needs to get good because he can't actually kill hard bosses. To kill them, he uses skip points. One skip point can be used to kill one hard boss.

Your task is to find the minimum number of skip points your friend needs to use so you and your friend kill all $n$ bosses in the given order.

For example: suppose $n = 8$, $a = [1, 0, 1, 1, 0, 1, 1, 1]$. Then the best course of action is the following:

  your friend kills two first bosses, using one skip point for the first boss;  you kill the third and the fourth bosses;  your friend kills the fifth boss;  you kill the sixth and the seventh bosses;  your friend kills the last boss, using one skip point, so the tower is completed using two skip points. 

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 2 \cdot 10^4$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the number of bosses. The second line of the test case contains $n$ integers $a_1, a_2, \dots, a_n$ ($0 \le a_i \le 1$), where $a_i$ is the type of the $i$-th boss.

It is guaranteed that the sum of $n$ does not exceed $2 \cdot 10^5$ ($\sum n \le 2 \cdot 10^5$).

-----Output-----

For each test case, print the answer: the minimum number of skip points your friend needs to use so you and your friend kill all $n$ bosses in the given order.

-----Example-----
Input
6
8
1 0 1 1 0 1 1 1
5
1 1 1 1 0
7
1 1 1 1 0 0 1
6
1 1 1 1 1 1
1
1
1
0

Output
2
2
2
2
1
0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded