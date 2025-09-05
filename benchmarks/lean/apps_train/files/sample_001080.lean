It is the end of 2019 — the 17th of November, the Cooking Challenge day.
There are N$N$ players participating in this competition, numbered 1$1$ through N$N$. Initially, the skill level of each player is zero. There are also M$M$ challenges (numbered 1$1$ through M$M$). For each valid i$i$, the i$i$-th challenge has three parameters Li$L_i$, Ri$R_i$ and Xi$X_i$ with the following meaning: for each player between the Li$L_i$-th and Ri$R_i$-th inclusive, if this player participates in this challenge, their skill level increases by Xi$X_i$ (Xi$X_i$ does not have to be positive).
The organizers of the Cooking Challenge decided that the contest would be boring if they let the participants participate in the challenges directly, so they decided to use the compos.
There are Q$Q$ compos (numbered 1$1$ through Q$Q$). For each valid i$i$, the i$i$-th compo has two parameters Ai$A_i$ and Bi$B_i$, which means that it includes the challenges Ai,Ai+1,…,Bi$A_i, A_i+1, \ldots, B_i$.
Each participant has to select a subset of the compos (possibly empty or the set of all Q$Q$ compos) and participate in all challenges those compos include. A participant may not select the same compo twice, but may participate in the same challenge more than once if it is included in multiple chosen compos.
For each player, find the maximum skill level this player can reach if the compos are chosen optimally.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains three space-separated integers N$N$, M$M$ and Q$Q$.
- M$M$ lines follow. For each valid i$i$, the i$i$-th of these lines contains three space-separated integers Li$L_i$, Ri$R_i$ and Xi$X_i$.
- Q$Q$ more lines follow. For each valid i$i$, the i$i$-th of these lines contains two space-separated integers Ai$A_i$ and Bi$B_i$.

-----Output-----
For each test case, print a single line containing N$N$ space-separated integers. For each valid i$i$, the i$i$-th of these integers should denote the maximum skill level of the i$i$-th player.

-----Constraints-----
- 1≤T≤1,000$1 \le T \le 1,000$
- 1≤N≤100,000$1 \le N \le 100,000$
- 1≤M≤1,000$1 \le M \le 1,000$
- 1≤Q≤10,000$1 \le Q \le 10,000$
- 1≤Li≤Ri≤N$1 \le L_i \le R_i \le N$ for each valid i$i$
- 1≤Ai≤Bi≤M$1 \le A_i \le B_i \le M$ for each valid i$i$
- |Xi|≤1,000,000$|X_i| \le 1,000,000$ for each valid i$i$
- the sum of N$N$ over all test cases does not exceed 1,000,000$1,000,000$
- the sum of M$M$ over all test cases does not exceed 5,000$5,000$
- the sum of Q$Q$ over all test cases does not exceed 50,000$50,000$

-----Example Input-----
1
5 3 4
1 1 3
1 2 -4
4 5 2
1 2
1 3
1 1
2 3

-----Example Output-----
3 0 0 4 4

-----Explanation-----
Example case 1:
- The first player will select the 3$3$-rd compo.
- The second and third players will not select any compo.
- The fourth player will select the 1$1$-st, 2$2$-nd and 4$4$-th compos.
- The fifth player will select all the compos.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded