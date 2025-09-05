On Miu's smart phone, there is a search feature which lets her search for a contact name by typing digits on the keypad where each digit may correspond to any of the characters given below it. For example, to search for TOM, she can type 866 and for MAX she can type 629.
+------+-----+------+
|   1  |  2  |   3  |
|      | ABC |  DEF |
+------+-----+------+
|   4  |  5  |   6  |
|  GHI | JKL |  MNO |
+------+-----+------+
|   7  |  8  |   9  |
| PQRS | TUV | WXYZ |
+------+-----+------+
|      |  0  |      |
+------+-----+------+

Miu typed a random string of digits $S$ on the keypad while playing around, where each digit is between 2 and 9 inclusive. Now she wants to know the number of possible strings which would map to $S$. 
Since this number can be very large, output it modulo 10^9 + 7 (1000000007)

-----Input:-----
- 
The first line of the input consists of a single integer $T$ denoting the number of test cases.
- 
Each test case consists of a string $S$.

-----Output:-----
- For each test case, print a single line containing one integer - the count of all possible strings mod 1,000,000,007

-----Constraints-----
- 
1 <= $T$ <= 10
- 
1 <= $|S|$ <= 105

-----Subtasks-----
Subtask #1 (10 points):
- 1 <= $|S|$ <= 10
Subtask #2 (90 points):
- Original Constraints

-----Sample Input:-----
2

5

72  

-----Sample Output:-----
3

12  

-----EXPLANATION:-----
- 
Example Case 1:

On the key 5, we have the character set JKL.

Hence the possible strings are J,K,L.

Hence the answer is 3 % (1000000007) = 3.  
- 
Example Case 2:
On key 7, we have the character set PQRS.

On key 2, we have the character set ABC.

Hence the possible strings are PA,PB,PC,QA,QB,QC,RA,RB,RC,SA,SB,SC.

Hence the answer is 12 % (1000000007) = 12.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible