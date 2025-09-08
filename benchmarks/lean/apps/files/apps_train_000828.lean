/-
We all know how great ABD aka AB-DE-VILLIERS is. However his team mates were jealous of him and posed a problem for him to solve.The problem description is as follows :

Given an array of integers,find the length of the largest subarray(contiguous) of the given array with the maximum possible GCD (Greatest Common Divisor).

For info on GCD ,see this link: https://en.wikipedia.org/wiki/Greatest_common_divisor

GCD of the subarray is defined as the GCD of all the elements of the subarray.
As ABD is not aware of competitive programming he asks your help. Help him!

-----Input-----
First line will contain integer N denoting the size of array.

Second line will contain N integers denoting array elements.

-----Output-----
The answer as specified in the problem statement .

-----Constraints-----
1 <= N <= 1000000

1 <= array[i] <=100000000000

-----Example-----
Input:
4
2 4 8 3

Output:
1

Explanation
GCD of all possible subarrays of the given array are : 2 , 2 , 2 , 1 , 4 , 4, 1 , 8 , 1 , 3

Largest GCD possible : 8

Length of the largest subarray with GCD as 8 is 1

Hence answer is 1 .
-/

-- <vc-helpers>
-- </vc-helpers>

def find_largest_gcd_subarray (n : Nat) (arr : List Nat) : Nat :=
  sorry

theorem singleton_array {x : Nat} (h : x > 0) : 
  find_largest_gcd_subarray 1 [x] = 1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 4 [2, 4, 8, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 5 [10, 10, 10, 5, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_largest_gcd_subarray 3 [6, 12, 6]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible