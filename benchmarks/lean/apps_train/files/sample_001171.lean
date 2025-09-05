Chef and his competitor Kefa own two restaurants located at a straight road. The position of Chef's restaurant is $X_1$, the position of Kefa's restaurant is $X_2$.
Chef and Kefa found out at the same time that a bottle with a secret recipe is located on the road between their restaurants. The position of the bottle is $X_3$.
The cooks immediately started to run to the bottle. Chef runs with speed $V_1$, Kefa with speed $V_2$.
Your task is to figure out who reaches the bottle first and gets the secret recipe (of course, it is possible that both cooks reach the bottle at the same time).

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains five space-separated integers $X_1$, $X_2$, $X_3$, $V_1$ and $V_2$. 

-----Output-----
For each test case, print a single line containing the string "Chef" if Chef reaches the bottle first, "Kefa" if Kefa reaches the bottle first or "Draw" if Chef and Kefa reach the bottle at the same time (without quotes). 

-----Constraints-----
- $1 \le T \le 10^5$
- $|X_1|, |X_2|, |X_3| \le 10^5$
- $X_1 < X_3 < X_2$
- $1 \le V_1 \le 10^5$
- $1 \le V_2 \le 10^5$

-----Example Input-----
3
1 3 2 1 2
1 5 2 1 2
1 5 3 2 2

-----Example Output-----
Kefa
Chef
Draw

-----Explanation-----
Example case 1. Chef and Kefa are on the same distance from the bottle, but Kefa has speed $2$, while Chef has speed $1$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
