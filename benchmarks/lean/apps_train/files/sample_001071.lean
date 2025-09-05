Polo, the Penguin, likes numbers. He says that the goodness of a number is itself multiplied by the number of digits in it's decimal representation. For example, the goodness of the integer 474 is 474*3 = 1422.
Help him to count the sum of goodness of all integers from L to R, inclusive. Since the answer can be too large, output it modulo 1,000,000,007 (10^9+7).

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of T test cases follows. The only line of each test case contains the pair of integers L and R, separated by a single space.

-----Output-----
For each test case, output a single line containing the answer to the corresponding test case.

-----Constraints-----
- 1 ≤ T ≤ 1,000
- 1 ≤ L ≤ R ≤ 1,000,000,000 (10^9)

-----Example-----
Input:
1
9 12

Output:
75

-----Explanation-----
Example case 1. The answer is 9*1 + 10*2 + 11*2 + 12*2 = 75.

def calculate_goodness_sum (a b : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
