To make Yalalovichik even more satisfied and happy, Jafar decided to invent Yalalovichik strings. A string is called a Yalalovichik string if the set of all of its distinct non-empty substrings is equal to the set of all of its distinct non-empty subsequences. 
You are given a string S$S$. You need to find the number of its distinct non-empty substrings which are Yalalovichik strings.
Note: A string A$A$ is called a subsequence of a string B$B$ if A$A$ can be formed by erasing some characters (possibly none) from B$B$. A string A$A$ is called a substring of a string B$B$ if it can be formed by erasing some characters (possibly none) from the beginning of B$B$ and some (possibly none) from the end of B$B$. Two substrings or subsequences are considered different if they are different strings.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains a single integer N=|S|$N = |S|$.
- The second line contains the string S$S$.

-----Output-----
For each test case, print a single line containing one integer — the number of distinct Yalalovichik substrings of S$S$.

-----Constraints-----
- 1≤T≤100$1 \le T \le 100$
- 1≤N≤106$1 \le N \le 10^6$
- the sum of N$N$ over all test cases does not exceed 2⋅106$2 \cdot 10^6$
- S$S$ contains only lowercase English letters

-----Example Input-----
1
3
xxx

-----Example Output-----
3

-----Explanation-----
Example case 1: The distinct Yalalovichik substrings are "x", "xx" and "xxx".

def count_yalalovichik_substrings (s: String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
