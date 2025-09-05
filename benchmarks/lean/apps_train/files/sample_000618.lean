A balanced parenthesis string is defined as follows:
- The empty string is balanced
- If P is balanced, (P) is also 
- If P and Q are balanced, PQ is also balanced
You are given two even integers n$n$ and k$k$. Find any balanced paranthesis string of length n$n$ that doesn't contain a balanced substring of length k$k$, or claim that no such string exists.

-----Input-----
- First line will contain T$T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line containing n$n$ and k$k$.

-----Output-----
For every testcase, print on a new line, any balanced paranthesis string of length n$n$ that doesn't contain a balanced substring of length k$k$. If there doesn't exist any such string, print −1$-1$ instead.

-----Constraints-----
- 1≤T≤50000$1 \leq T \leq 50000$
- 2≤k≤n≤105$2 \leq k \leq n \leq 10^5$
- Sum of n$n$ over all testcases doesn't exceed 105$10^5$.
- n$n$ and k$k$ are both even integers.

-----Example Input-----
2
4 2
8 6

-----Example Output-----
-1
(())(())

-----Explanation-----
In the first testcase, the only balanced strings of length 4$4$ are (()) and ()(), both of which contain () as a substring.
In the second testcase, (())(()) is a balanced string that doesn't contain any balanced substring of length 6$6$.

def is_valid_parens (s : String) : Bool := sorry

def max_nested_depth (s : String) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded