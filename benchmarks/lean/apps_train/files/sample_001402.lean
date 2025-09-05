Chef has a sequence $A_1, A_2, \ldots, A_N$; each element of this sequence is either $0$ or $1$. Appy gave him a string $S$ with length $Q$ describing a sequence of queries. There are two types of queries:
- '!': right-shift the sequence $A$, i.e. replace $A$ by another sequence $B_1, B_2, \ldots, B_N$ satisfying $B_{i+1} = A_i$ for each valid $i$ and $B_1 = A_N$
- '?': find the length of the longest contiguous subsequence of $A$ with length $\le K$ such that each element of this subsequence is equal to $1$
Answer all queries of the second type.

-----Input-----
- The first line of the input contains three space-separated integers $N$, $Q$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.
- The third line contains a string with length $Q$ describing queries. Each character of this string is either '?', denoting a query of the second type, or '!', denoting a query of the first type.

-----Output-----
For each query of the second type, print a single line containing one integer — the length of the longest required subsequence.

-----Constraints-----
- $1 \le K \le N \le 10^5$
- $1 \le Q \le 3 \cdot 10^5$
- $0 \le A_i \le 1$ for each valid $i$
- $S$ contains only characters '?' and '!'

-----Subtasks-----
Subtask #1 (30 points):
- $1 \le N \le 10^3$
- $1 \le Q \le 3 \cdot 10^3$
Subtask #2 (70 points): original constraints 

-----Example Input-----
5 5 3
1 1 0 1 1
?!?!?    

-----Example Output-----
2
3
3

-----Explanation-----
- In the first query, there are two longest contiguous subsequences containing only $1$-s: $A_1, A_2$ and $A_4, A_5$. Each has length $2$.
- After the second query, the sequence $A$ is $[1, 1, 1, 0, 1]$.
- In the third query, the longest contiguous subsequence containing only $1$-s is $A_1, A_2, A_3$.
- After the fourth query, $A = [1, 1, 1, 1, 0]$.
- In the fifth query, the longest contiguous subsequence containing only $1$-s is $A_1, A_2, A_3, A_4$ with length $4$. However, we only want subsequences with lengths $\le K$. One of the longest such subsequences is $A_2, A_3, A_4$, with length $3$.

def longest_contiguous_subsequence (N Q K : Nat) (A : List Nat) (S : String) : List Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
