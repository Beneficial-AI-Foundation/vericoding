Given an array A1,A2...AN, you have to print the size of the largest contiguous subarray such that 
GCD of all integers in that subarray is 1.

Formally,
For a subarray Ai,Ai+1...Aj where 1 ≤ i < j ≤ N to be valid: GCD(Ai,Ai+1...Aj) should be 1. You have to print the size of the largest valid subarray.
If no valid subarray exists, output -1.
Note:A single element is not considered as a subarray according to the definition of this problem.

-----Input-----
First line contains T, the number of testcases. Each testcase consists of N in one line followed by N integers in the next line.

-----Output-----
For each testcase, print the required answer in one line.

-----Constraints-----
- 1 ≤ T ≤ 10
- 2 ≤ N ≤ 105
- 1 ≤ Ai ≤ 105

-----Example-----
Input:
2
2
7 2
3
2 2 4

Output:
2
-1

-----Explanation-----
Example case 1.GCD(2,7)=1. So the subarray [A1,A2] is valid.
Example case 2.No subarray satisfies.
Note: Use scanf/print instead of cin/cout. Large input files.

def gcd (a b : Nat) : Nat :=
  sorry

def find_largest_gcd_1_subarray (arr : List Nat) : Int :=
  sorry

def reduce_gcd (l : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded