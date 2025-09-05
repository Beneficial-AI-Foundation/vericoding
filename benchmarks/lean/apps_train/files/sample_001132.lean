Roger recently built a circular race track with length K$K$. After hosting a few races, he realised that people do not come there to see the race itself, they come to see racers crash into each other (what's wrong with our generation…). After this realisation, Roger decided to hold a different kind of "races": he hired N$N$ racers (numbered 1$1$ through N$N$) whose task is to crash into each other.
At the beginning, for each valid i$i$, the i$i$-th racer is Xi$X_i$ metres away from the starting point of the track (measured in the clockwise direction) and driving in the direction Di$D_i$ (clockwise or counterclockwise). All racers move with the constant speed 1$1$ metre per second. The lengths of cars are negligible, but the track is only wide enough for one car, so whenever two cars have the same position along the track, they crash into each other and the direction of movement of each of these cars changes (from clockwise to counterclockwise and vice versa). The cars do not change the directions of their movement otherwise.
Since crashes reduce the lifetime of the racing cars, Roger sometimes wonders how many crashes happen. You should answer Q$Q$ queries. In each query, you are given an integer T$T$ and you should find the number of crashes that happen until T$T$ seconds have passed (inclusive).

-----Input-----
- The first line of the input contains three space-separated integers N$N$, Q$Q$ and K$K$.
- N$N$ lines follow. For each i$i$ (1≤i≤N$1 \le i \le N$), the i$i$-th of these lines contains two space-separated integers Di$D_i$ and Xi$X_i$, where Di=1$D_i = 1$ and Di=2$D_i = 2$ denote the clockwise and counterclockwise directions respectively.
- Each of the next Q$Q$ lines contain a single integer T$T$ describing a query.

-----Output-----
For each query, print a single line containing one integer — the number of crashes.

-----Constraints-----
- 1≤N≤105$1 \le N \le 10^5$
- 1≤Q≤1,000$1 \le Q \le 1,000$
- 1≤K≤1012$1 \le K \le 10^{12}$
- 1≤Di≤2$1 \le D_i \le 2$ for each valid i$i$
- 0≤Xi≤K−1$0 \le X_i \le K - 1$ for each valid i$i$
- X1,X2,…,XN$X_1, X_2, \ldots, X_N$ are pairwise distinct
- 0≤T≤1012$0 \le T \le 10^{12}$

-----Example Input-----
5 3 11
1 3
1 10
2 4
2 7
2 0
3
8
100

-----Example Output-----
4
10
110

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded