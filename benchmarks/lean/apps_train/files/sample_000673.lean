There is crazy man named P29892P. He always tries to do crazy things as he thinks. One day he invented a machine and named it as ANGEN. The ANGEN is used to perform range operations. The range operation means performing operations on range values from {L..R}. At any time it performs operations on values in between L to R.
ANGEN can perform following operations
U I V - Update the value present at I  with value V
A L R - Find the sum between range L and R
M L R - Find the maximum number between L and R
m L R - Find the minimum number between L and R
S L R - Find second maximum value in between L and R
s L R - Find second mimimum value in between L and R
If it is not possible perform operation ANGEN returns “NA” with out quotes.
For Invalid operations ANGEN returns “!!!” with out quotes.
Now P29892P challenging his friends and you too, to build his invention with yourown code. So it's your time to defeat P29892P by implementing his invention with your own ability. Let's go and solve the problem.

-----Input-----
Input description.
- The first line of the input contains an integer N denoting the number of integers. 
- The next line contains N space separated integers."
- The next line contains a single integer Q denoting the number of Questions.
-  The next Q lines contains T Question type , L and R.

-----Output-----
Print output for each question in separate line.

-----Constraints-----
Should contain all the constraints on the input data that you may have. Format it like:
- 1 ≤ N ≤ 100000
- 1 ≤ values[i] ≤ 1000000000
- 1 ≤ Q ≤ 10000
- T in { A..Z, a..z }
- 1 ≤ L ≤ R ≤ N

-----Example-----
Input:
6
1 2 5 3 10 6
6
A 1 5
M 1 3
m 5 6
s 3 6
U 1 7
S 1 2

Output:
21
5
6
5
2

-----Explanation-----
...

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded