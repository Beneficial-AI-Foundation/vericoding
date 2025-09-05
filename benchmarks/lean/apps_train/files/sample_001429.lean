A binary string is called a self-destructing string if it can reduced to an empty string by performing the following operation some number of times (possibly zero): Choose a valid integer $i$ such that the $i$-th character of the current string is different from the $i+1$-th character, and remove these two characters from the string.
You are given a binary string $s$. Your task is to convert $s$ to a self-destructing string. To do that, you may perform the following operation any number of times (possibly zero): Choose an integer $i$ ($1 \le i \le |s|-1$) such that the $i$-th character of $s$ is different from the $i+1$-th character, and invert one of these characters (inverting a character means changing '0' to '1' or '1' to '0', e.g. the string "01" can be changed to "00").
Find the smallest number of operations required to convert $s$ to a self-destructing string or determine that it is impossible.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single string $s$.

-----Output-----
For each test case, print a single line containing one integer ― the smallest required number of operations or $-1$ if it is impossible to convert $s$ to a self-destructing string.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le |s| \le 10^6$
- $s$ contains only characters '0' and '1'
- the sum of $|s|$ over all test cases does not exceed $10^6$

-----Example Input-----
3
001101
1101
110

-----Example Output-----
0
1
-1

-----Explanation-----
Example case 1: We already have a self-destructing string because "001101" can be converted to "0101", to "01" and finally to an empty string.
Example case 2: We can choose $i=3$ (since $s_3 \neq s_4$) and then invert $s_4$ to obtain "1100", which is a self-destructing string.
Example case 3: It can be shown that "110" cannot be converted to a self-destructing string.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded