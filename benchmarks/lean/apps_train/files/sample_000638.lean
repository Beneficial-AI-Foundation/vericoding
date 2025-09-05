You will be given a two-dimensional array with row consisting values 0 or 1.  
A move consists of choosing any column or row, and toggling all the 0’s as 1’s and 1’s as 0’s.  
After making the required moves, every row represents a binary number and the score of the matrix will be sum of all the numbers represented as binary numbers in each row.  
Find the highest possible score.  
$Example:$ 
Input:

0 0 1 1

1 0 1 0

1 1 0 0  
Output:

39
Explanation:

Toggled to

1 1 1 1

1 0 0 1

1 1 1 1  
0b1111 + 0b1001 + 0b1111 = 15 + 9 + 15 = 39

-----Input:-----
- First line will contains $m$, $n$ for the size of the 2-D array. 
- Contains $m$ lines of $n$ space-separated values each. 

-----Output:-----
Single integer which is the maximum score obtained by the sum of binary numbers.

-----Constraints-----
- $1 \leq m, n \leq 20$
- $A[i][j] = 1$ or $0$ 

-----Sample Input:-----
3 4  
0 0 1 1  
1 0 1 0  
1 1 0 0  

-----Sample Output:-----
39

def matrix_score (m : BinaryMatrix) : Nat :=
  sorry

-- Define helper function to check if first element of each row is 1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded