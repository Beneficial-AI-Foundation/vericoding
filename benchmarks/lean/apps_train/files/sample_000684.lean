Chef gives an integer $K$ in the input.  If the given number is beautiful binary number, print it, Else find its previous beautiful binary number. A beautiful binary number is a number whose binary representation does not contain any consecutive 1s.
Note: 1 is also a beautiful binary number.

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, one integer $K$. 

-----Output:-----
For each test case, print a beautiful number.

-----Constraints-----
- $1 \leq T \leq 10^5$
- $1 \leq K \leq 10^5$

-----Sample Input:-----
3
3
6
8

-----Sample Output:-----
2
5
8

-----EXPLANATION:-----
For 1) 3 is not a beautiful binary number because the binary representation of 3 is "11" which has consecutive 1s.  hence 2 which is less than 3 is printed.
For 3) 8 is already a beautiful binary number with no consecutive 1s in its binary representation. so, print 8 as it is.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
