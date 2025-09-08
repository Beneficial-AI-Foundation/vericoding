/-
The Little Elephant from the Zoo of Lviv has an array A that consists of N positive integers. Let A[i] be the i-th number in this array (i = 1, 2, ..., N).

Find the minimal number x > 1 such that x is a divisor of all integers from array A. More formally, this x should satisfy the following relations:

A[1] mod x = 0, A[2] mod x = 0, ..., A[N] mod x = 0,

where mod stands for the modulo operation. For example,  8 mod 3 = 2,  2 mod 2 = 0, 100 mod 5 = 0 and so on. If such number does not exist, output -1.

-----Input-----

The first line of the input contains a single integer T, the number of test cases. T test cases follow. The first line of each test case contains a single integer N, the size of the array A for the corresponding test case. The second line contains N space separated integers A[1], A[2], ..., A[N].

-----Output-----

For each test case output a single line containing the answer for the corresponding test case.

-----Constraints-----
1 ≤ T ≤ 100000

1 ≤ N ≤ 100000

The sum of values of N in each test file does not exceed 100000

1 ≤ A[i] ≤ 100000

-----Example-----
Input:
2
3
2 4 8
3
4 7 5

Output:
2
-1

-----Explanation-----
Case 1. Clearly 2 is a divisor of each of the numbers 2, 4 and 8. Since 2 is the least number greater than 1 then it is the answer.

Case 2. Let's perform check for several first values of x.

x4 mod x7 mod x5 mod x20113112403154206415740584759475

As we see each number up to 9 does not divide all of the numbers in the array. Clearly all larger numbers also will fail to do this. So there is no such number x > 1 and the answer is -1.
-/

def find_min_divisor (nums: List Nat) : Int :=
  sorry

def is_divides_all (d: Nat) (nums: List Nat) : Bool :=
  sorry

def gcd (a b: Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def list_gcd (nums: List Nat) : Nat :=
  sorry

theorem result_divides_all_numbers (nums: List Nat) :
  let result := find_min_divisor nums 
  result ≠ -1 → is_divides_all result.toNat nums = true := by
  sorry

theorem negative_one_means_no_common_divisor (nums: List Nat) :
  let result := find_min_divisor nums
  result = -1 → list_gcd nums = 1 := by
  sorry

theorem result_is_minimal_divisor (nums: List Nat) :
  let result := find_min_divisor nums
  result ≠ -1 → 
  ∀ d: Nat, 2 ≤ d → d < result.toNat → 
  is_divides_all d nums = false := by
  sorry

theorem result_is_valid_number (nums: List Nat) :
  let result := find_min_divisor nums
  result = -1 ∨ result ≥ 2 := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_divisor [2, 4, 8]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_min_divisor [4, 7, 5]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_divisor [12, 18, 24]

-- Apps difficulty: interview
-- Assurance level: guarded