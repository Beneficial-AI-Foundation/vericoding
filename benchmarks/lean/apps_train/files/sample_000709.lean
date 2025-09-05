Given a square matrix of size N×N, calculate the absolute difference between the sums of its diagonals. 

-----Input-----
The first line contains a single integer N. The next N lines denote the matrix's rows, with each line containing N space-separated integers describing the columns.

-----Output-----
Print the absolute difference between the two sums of the matrix's diagonals as a single integer.

-----Constraints-----
1<=N<=10

-----Example-----
Input:
3
11 2 4
4 5 6
10 8 -12

Output:
15

-----Explanation-----
The primary diagonal is: 
11
5
-12
Sum across the primary diagonal: 11 + 5 - 12 = 4
The secondary diagonal is:
4
5
10
Sum across the secondary diagonal: 4 + 5 + 10 = 19 
Difference: |4 - 19| = 15

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible