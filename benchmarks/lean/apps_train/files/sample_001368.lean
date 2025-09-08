/-
Mr. Wilson was planning to record his new Progressive Rock music album called "Digits. Cannot. Separate". Xenny and PowerShell, popular pseudo-number-theoreticists from the Land of Lazarus were called by him to devise a strategy to ensure the success of this new album. Xenny and Powershell took their Piano Lessons and arrived at the Studio in different Trains.
Mr. Wilson, creative as usual, had created one single, long music track S. The track consisted of N musical notes. The beauty of each musical note was represented by a decimal digit from 0 to 9.
Mr. Wilson told them that he wanted to create multiple musical tracks out of this long song. Since Xenny and Powershell were more into the number theory part of music, they didn’t know much about their real workings. Mr. Wilson told them that a separator could be placed between 2 digits. After placing separators, the digits between 2 separators would be the constituents of this new track and the number formed by joining them together would represent the Quality Value of that track. He also wanted them to make sure that no number formed had greater than M digits.
Mr. Wilson had Y separators with him. He wanted Xenny and PowerShell to use at least X of those separators, otherwise he would have to ask them to Drive Home.
Xenny and PowerShell knew straight away that they had to put place separators in such a way that the Greatest Common Divisor (GCD) of all the Quality Values would eventually determine the success of this new album. Hence, they had to find a strategy to maximize the GCD.
If you find the maximum GCD of all Quality Values that can be obtained after placing the separators, Xenny and PowerShell shall present you with a Porcupine Tree.
Note:
- 
You can read about GCD here.

- 
Greatest Common Divisor of 0 and 0 is defined as 0.

-----Input-----
The first line of input consists of a single integer T - the number of testcases.
Each test case is of the following format:
First line contains a single integer N - the length of the long musical track.
Second line contains the string of digits S.
Third line contains 3 space-separated integers - M, X and Y - the maximum number of digits in a number, the minimum number of separators to be used and the maximum number of separators to be used.

-----Output-----
For each testcase, output a single integer on a new line - the maximum GCD possible after placing the separators.

-----Constraints-----
Subtask 1: 20 points

- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 18
- 1 ≤ M ≤ 2
- 1 ≤ X ≤ Y ≤ (N - 1)

Subtask 2: 80 points

- 1 ≤ T ≤ 10
- 1 ≤ N ≤ 300
- 1 ≤ M ≤ 10
- 1 ≤ X ≤ Y ≤ (N - 1)

For both Subtask 1 and Subtask 2:

- 1 ≤ X ≤ Y ≤ (N - 1)
- M*(Y+1) ≥ N
- S may contain leading 0s.

-----Example-----Input:
2
3
474
2 1 1
34
6311861109697810998905373107116111
10 4 25

Output:
2
1

-----Explanation-----
Test case 1. 
Since only 1 separator can be placed, we can only have 2 possibilities:

a. 4 | 74

The GCD in this case is 2.

b. 47 | 4

The GCD in this case is 1.

Hence, the maximum GCD is 2.
Test case 2.

One of the optimal partitions is:
63|118|61|109|69|78|109|98|90|53|73|107|116|111
Bonus: Decode the above partition to unlock a hidden treasure.
-/

def gcd (a b : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve_max_gcd (s : String) (m x y : Nat) : Nat :=
  sorry

theorem gcd_properties (a b : Int) (h : b ≠ 0) :
  let g := gcd a.natAbs b.natAbs
  g > 0 ∧ a.natAbs % g = 0 ∧ b.natAbs % g = 0 :=
  sorry

theorem solve_max_gcd_basic_properties
  (s : String) (m x y : Nat) 
  (h1 : s.length > 0) 
  (h2 : s.length ≤ 10)
  (h3 : m ≤ 5) 
  (h4 : m > 0)
  (h5 : x ≤ 3)
  (h6 : y ≤ 3)
  (h7 : x ≤ y) :
  let result := solve_max_gcd s m x y
  result ≥ 0 ∧ 
  result ≤ (sorry) -- max of all valid partition numbers
  :=
  sorry 

theorem solve_max_gcd_partition_bounds 
  (s : String)
  (h1 : s.length > 0)
  (h2 : s.length ≤ 5) :
  let m := s.length
  let full_partition := solve_max_gcd s m 0 m
  let single_partition := solve_max_gcd s m 0 0
  full_partition ≥ 0 ∧
  (single_partition = sorry ∨ single_partition = 0) -- equal to integer value of s or 0
  :=
  sorry

-- Apps difficulty: interview
-- Assurance level: unguarded