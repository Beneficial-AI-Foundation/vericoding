You want to build a temple for snakes. The temple will be built on a mountain range, which can be thought of as n blocks, where height of i-th block is given by hi. The temple will be made on a consecutive section of the blocks and its height should start from 1 and increase by exactly 1 each time till some height and then decrease by exactly 1 each time to height 1, 
i.e. a consecutive section of 1, 2, 3, .. x-1, x, x-1, x-2, .., 1 can correspond to a temple. Also, heights of all the blocks other than of the temple should have zero height, so that the temple is visible to people who view it from the left side or right side.
You want to construct a temple. For that, you can reduce the heights of some of the blocks. In a single operation, you can reduce the height of a block by 1 unit. Find out minimum number of operations required to build a temple.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows.
The first line of each test case contains an integer n.
The next line contains n integers, where the i-th integer denotes hi

-----Output-----
For each test case, output a new line with an integer corresponding to the answer of that testcase.

-----Constraints-----
- 1 ≤ T ≤ 10
- 2 ≤ n ≤ 105
- 1 ≤ hi ≤ 109

-----Example-----
Input
3
3
1 2 1
4
1 1 2 1
5
1 2 6 2 1

Output
0
1
3

-----Explanation-----
Example 1. The entire mountain range is already a temple. So, there is no need to make any operation.
Example 2. If you reduce the height of the first block to 0. You get 0 1 2 1. The blocks 1, 2, 1 form a temple. So, the answer is 1.
Example 3. One possible temple can be 1 2 3 2 1. It requires 3 operations to build. This is the minimum amount you have to spend in order to build a temple.

def min_temple_operations (n : Nat) (heights : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded