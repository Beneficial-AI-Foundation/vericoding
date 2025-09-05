Vanja and Miksi have already finished everything for this year at their university, so they decided to spend their free time playing a game with a binary sequence $A_1, A_2, \dots, A_N$ (i.e. a sequence containing only integers $0$ and $1$).
At the beginning of the game, Vanja and Miksi write down the expression $* A_1 * A_2 * A_3 * \ldots * A_N$ (note below that each $*$ is a placeholder and does not denote multiplication).
The players take turns alternately, starting with Vanja. The game lasts $N$ turns. In each turn, the current player must replace the first (leftmost) remaining $*$ by the sign $+$ or $-$ (or, equivalently, by the operation of addition or subtraction).
After the last turn, the boys calculate the resulting value $V$ of the expression. If $|V| \ge K$, the winner is Vanja; otherwise, the winner is Miksi.
Please predict the winner of the game if both players play optimally. 

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \dots, A_N$.

-----Output-----
For each test case, print a single line containing one integer — $1$ if Vanja (the first player) is the winner or $2$ if Miksi (the second player) is the winner.

-----Constraints-----
- $1 \le T \le 50$
- $1 \le N \le 3 \cdot 10^4$
- $0 \le K \le 3 \cdot 10^4$
- $0 \le A_i \le 1$ for each valid $i$

-----Example Input-----
2
2 1
1 0
3 5
0 1 0

-----Example Output-----
1
2

-----Explanation-----
Example case 1: $K = 1$, so if Vanja replaces the first $*$ by $+$, the value of the final expression will be $V = 1$; then, $K \le |V|$, so the winner is Vanja.
Example case 2: $K = 5$, but the absolute value of the final expression cannot be greater than $1$. The winner is Miksi.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded