Your are given a string $S$ containing only lowercase letter and a array of character $arr$. Find whether the given string only contains characters from the given character array. 
Print $1$ if the string contains characters from the given array only else print $0$.
Note: string contains characters in lower case only.

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains- 
a string $S$ of lowercase letter
a integer $n$ denoting length of character array $arr$
next line contains $n$ space separated characters.

-----Output:-----
For each testcase, Print $1$ if the string contains characters from the given array only else print $0$.

-----Constraints-----
- $1 \leq T \leq 1000$
- $0 \leq n \leq 10^5$

-----Sample Input:-----
3
abcd
4
a b c d
aabbbcccdddd
4
a b c d
acd
3
a b d

-----Sample Output:-----
1
1
0

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
