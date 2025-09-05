Chef has invited Alice for his birthday party. Now, Alice is thinking about what to give Chef as a present. She should obviously choose a sequence ― what could possibly be a better birthday gift than a sequence!
After some thinking, Alice chose a sequence of integers $A_1, A_2, \ldots, A_N$. However, she does not want to simply give this sequence to Chef. Instead, she decided to give Chef a sequence $B_1, B_2, \ldots, B_N$, where $B_i = \bigvee_{j=1}^i A_j$ for each valid $i$ and $\bigvee$ denotes the bitwise OR operation. Chef can try to generate a sequence $A$ from $B$, but there could be more than one such possible sequence.
Now, Alice is wondering how many sequences $A$ correspond to the given sequence $B$. Since this number could be very large, compute it modulo $10^9 + 7$. Note that it is not guaranteed that the given sequence $B$ was generated from some sequence $A$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $B_1, B_2, \ldots, B_N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of possible sequences $A$ modulo $10^9 + 7$.

-----Constraints-----
- $1 \le T \le 25$
- $1 \le N \le 5 \cdot 10^4$
- $0 \le B_i < 2^{30}$ for each valid $i$

-----Example Input-----
2
2
2 3
4
2 6 7 7

-----Example Output-----
2
64

-----Explanation-----
Example case 1: There are two possible options for $A$: $(2, 1)$ and $(2, 3)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
