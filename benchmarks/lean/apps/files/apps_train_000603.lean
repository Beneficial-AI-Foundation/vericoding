/-
Find the length of the longest contiguous segment in an array, in which if a given element $K$ is inserted, $K$ becomes the second largest element of that subarray.

-----Input:-----
- The first line will contain $T$, number of test cases. Then the test cases follow. 
- The first line of each test case contains two integers $N$ and $K$.
- The next line contains N space-separated integers Ai denoting the elements of the array.

-----Output:-----
Print a single line corresponding to each test case — the length of the largest segment.

-----Constraints-----
- $1 \leq T \leq 10$
- $1 \leq N \leq 10^6$
- $1 \leq Ai, K \leq 10^9$
- Sum of N across all test cases doesn't exceed $10^6$

-----Sample Input:-----
2
5 3
2 4 2 4 2
8 5
9 3 5 7 8 11 17 2

-----Sample Output:-----
5
3

-----EXPLANATION:-----
If 3 is inserted at anywhere in the array, it is the second largest element. Hence the maximum length is 5.
If 5 is inserted anywhere between 1st and 4th element, it is the second largest element. The length of such subarray is 3.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_longest_segment (n : Nat) (k : Nat) (nums : List Nat) : Nat := sorry 

-- Basic properties from known good test cases

theorem solve_basic_case_1 :
  solve_longest_segment 5 3 [2, 4, 2, 4, 2] = 5 := sorry

theorem solve_basic_case_2 : 
  solve_longest_segment 8 5 [9, 3, 5, 7, 8, 11, 17, 2] = 3 := sorry

theorem solve_repeated_number :
  solve_longest_segment 4 3 [2, 4, 4, 2] = 4 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded