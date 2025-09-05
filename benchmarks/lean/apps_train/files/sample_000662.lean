You are playing following game: given an array A of N natural numbers. All numbers in the array A are at most M. On every turn you may pick any two different elements Ai and Aj (i≠j), such that Ai, Aj ≤ M, and add K to both. The game ends when you are not able to continue. That is, when there is no pair (i,j) left such that both of them are less than equal to M.

Let's call two arrays different if the sum of all their elements is different. When the game ends, you note down the final array A. How many different final arrays can you have.

-----Input-----

The first line contains three integers N, M and K. N elements of the array follow in the next line.

-----Output-----

Output single integer - answer for the given problem modulo 109+7.

-----Constraints-----
-  1 ≤ N ≤ 105
-  1 ≤ M,K ≤ 1012
-  1 ≤ Ai ≤ M

-----Example-----
Input:
3 3 2
1 2 3
Output:
2

-----Explanation-----

All possible sums are 14 and 10. You can get them by, for example, these arrays:
A=(5, 4, 5),
A=(1, 4, 5)

The above arrays are different because their sums are different.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
