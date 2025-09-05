Chef likes problems which using some math. Now he asks you to solve next one. You have 4 integers, Chef wondering is there non-empty subset which has sum equals 0.

-----Input-----
The first line of input contains T - number of test cases. 
Each of the next T lines containing four pairwise distinct integer numbers - a, b, c, d.

-----Output-----
For each test case output "Yes", if possible to get 0 by choosing non-empty subset of {a, b, c, d} with sum equal 0, or "No" in another case.

-----Constraints-----
- 1 ≤ T ≤ 103
- -106 ≤ a, b, c, d ≤ 106 

-----Example-----
Input:
3
1 2 0 3
1 2 4 -1
1 2 3 4

Output:
Yes
Yes
No

-----Explanation-----
Example case 1. We can choose subset {0} 
Example case 2. We can choose subset {-1, 1}

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded