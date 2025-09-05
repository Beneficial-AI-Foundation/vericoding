Chefina  is  always interested to play with string. But due to exam pressure she has no time to solve a string problem. She wants your help. Can you help her to solve that problem?
You are given a string. You have to find out the $Wonder$ $Sum$ of the string. $Wonder$ $Sum$ of a string is defined as the sum of the value of each character of the string. 
The value of each character means:
- If the string is started with "a" , then the value of each character of the string is like "a"=100, "b"=101, "c"="102" ………"z"=125.
- If the string is started with "z" , then the value of each character of the string is like "a"=2600, "b"=2601, "c"="2602" ………"z"=2625.
Since even the $Wonder$ $Sum$ can be large, output $Wonder$ $Sum$ modulo  ($10^9 + 7$).

-----Input:-----
- First line will contain $T$, number of testcases. Then the testcases follow. 
- Each testcase contains of a single line of input, a string $S$ with lower case alphabet 
only.

-----Output:-----
For each testcase, output in a single line integer i.e.  $Wonder$ $Sum$ modulo  ($10^9 + 7$).

-----Constraints-----
- $1 \leq T \leq 1000$
- $1 \leq |S| \leq 10^5$

-----Sample Input:-----
$2$$cab$
$sdef$

-----Sample Output:-----
$903$
$7630$

-----EXPLANATION:-----
i) For the first test case, since the string is started with "$c$", so output is ($302$+$300$+$301$)=$903$
ii)For the second test case, since the string is started with "$s$", so output is ($1918$+$1903$+$1904$+$1905$)=$7630$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible