Given an array A of non-negative integers, the array is squareful if for every pair of adjacent elements, their sum is a perfect square.
Return the number of permutations of A that are squareful.  Two permutations A1 and A2 differ if and only if there is some index i such that A1[i] != A2[i].

Example 1:
Input: [1,17,8]
Output: 2
Explanation: 
[1,8,17] and [17,8,1] are the valid permutations.

Example 2:
Input: [2,2,2]
Output: 1

Note:

1 <= A.length <= 12
0 <= A[i] <= 1e9

def sqrt (n: Nat) : Nat :=
sorry

def isPerfectSquare (n: Nat) : Bool :=
  match n with
  | 0 => true 
  | n + 1 => 
    let sq := sqrt n
    sq * sq = n

def numSquarefulPerms (A: List Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded