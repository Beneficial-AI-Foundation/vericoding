Dustin, is the head of an Intelligence agency. He wants to send a secret message S$S$ to his colleague.The message is a single word consisting of only lowercase english letters but he decides to encrypt the message for security reasons. He makes a string M$M$ of length N$N$, such that after deleting a substring of non-zero length from M$M$, the remaining string is S$S$.
Calculate the number of all such possible strings he can form.

-----Input:-----
- First line will contain T$T$, number of testcases. Then the testcases follow.
- For each testcase the there is a single line which contains an integer, N$N$ and then a string S$S$.

-----Output:-----
For each testcase, output the number of possible strings modulo 109+7$10^9+7$.

-----Constraints-----
- 1≤T≤50$1 \leq T \leq 50$
- 1≤N≤1018$1 \leq N \leq 10^{18}$
- 1≤|S|≤105$1 \leq |S| \leq 10^5$
- S$S$ can contain only lowercase English letters.

-----Sample Input:-----
2

3 a

3 ab     

-----Sample Output:-----
1326

76

def count_possible_strings (n : Nat) (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible