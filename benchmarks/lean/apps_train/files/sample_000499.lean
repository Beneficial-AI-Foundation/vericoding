You are given a string S of length N consisting of lowercase English letters.
Process Q queries of the following two types:
 - Type 1: change the i_q-th character of S to c_q. (Do nothing if the i_q-th character is already c_q.)
 - Type 2: answer the number of different characters occurring in the substring of S between the l_q-th and r_q-th characters (inclusive).

-----Constraints-----
 - N, Q, i_q, l_q, and r_q are integers.
 - S is a string consisting of lowercase English letters.
 - c_q is a lowercase English letter.
 - 1 \leq N \leq 500000
 - 1 \leq Q \leq 20000
 - |S| = N
 - 1 \leq i_q \leq N
 - 1 \leq l_q \leq r_q \leq N
 - There is at least one query of type 2 in each testcase.

-----Input-----
Input is given from Standard Input in the following format:
N
S
Q
Query_1
\vdots
Query_Q

Here, Query_i in the 4-th through (Q+3)-th lines is one of the following:
1 i_q c_q

2 l_q r_q

-----Output-----
For each query of type 2, print a line containing the answer.

-----Sample Input-----
7
abcdbbd
6
2 3 6
1 5 z
2 1 1
1 4 a
1 7 d
2 1 7

-----Sample Output-----
3
1
5

In the first query, cdbb contains three kinds of letters: b , c , and d, so we print 3.
In the second query, S is modified to abcdzbd.
In the third query, a contains one kind of letter: a, so we print 1.
In the fourth query, S is modified to abcazbd.
In the fifth query, S does not change and is still abcazbd.
In the sixth query, abcazbd contains five kinds of letters: a, b, c, d, and z, so we print 5.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
