Binod is a youtuber and he is busy in the fame of social media so he asked you to help him solve a problem.
You have been given an array of $positive$ $integers$ $a_{1},a_{2},a_{3},...,a_{i},...,a_{n}$ of size n.You have to find the smallest length of the subarray such that the length of the subarray must be $strictly$ greater than k and it's sum also must be $strictly$ greater than s. 

-----Input Format :------
- The first line of input contains three space-separated integers n, k and s
- The second line contains n space-separated integers,describing the array a 

-----Output Format:-----
- Print a single integer :- The smallest length of subarray if exists, Otherwise print "-1" (without quotes) 

-----Constraints:------
- $1 \leq n, k \leq 10^{6}$
- $1 \leq  a_{1},a_{2},a_{3},...,a_{i},...,a_{n}\leq 10^{9}$ 
- $1 \leq s \leq 10^{15}$ Subtask #1 (30 points):
- $1 \leq n, k \leq 10^{3}$ Subtask #2 (70 points):
$Original$ $Constraints$ 

-----Sample Test Cases:------

-----Example 1:-----
5 1 5

1 2 3 4 5 

-----Output :-----
2 

-----Explanation-----
$\textbf{There are two possibles answers} :$ 
- Index starts at 3 and ends at 4 have a sum of 7 which is strictly greater than 5 and has a length of subarray greater than 1.  
- Index starts at 4 and ends at 5 have a sum of 9 which is strictly greater than 5 and has a length of subarray greater than 1.
Any of the possible scenarios gives the same answer.

-----Example 2:-----
3 2 1

9 9 1 

-----Output :-----
3

-----Explanation :-----
- Each value in array index satisfies the condition sum greater than 1 but to satisfy the condition of length greater than 2 choose the subarray of length 3

def List.sum : List Int → Int 
  | [] => 0
  | x::xs => x + sum xs 

def find_subarray_length (n : Nat) (k : Nat) (s : Int) (arr : List Int) : Int :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded