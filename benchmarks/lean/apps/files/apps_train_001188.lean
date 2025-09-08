/-
The Gray code (see wikipedia for more details) is a well-known concept.
One of its important properties is that every two adjacent numbers have exactly one different digit in their binary representation.

In this problem, we will give you n non-negative integers in a sequence A[1..n] (0<=A[i]<2^64), such that every two adjacent integers have exactly one different digit in their binary representation, similar to the Gray code.

Your task is to check whether there exist 4 numbers A[i1], A[i2], A[i3], A[i4] (1 <= i1 < i2 < i3 < i4 <= n) out of the given n numbers such that A[i1] xor A[i2] xor A[i3] xor A[i4] = 0. Here xor is a bitwise operation which is same as ^ in C, C++, Java and xor in Pascal.

-----Input-----
First line contains one integer n (4<=n<=100000).
Second line contains n space seperated non-negative integers denoting the sequence A.

-----Output-----
Output “Yes” (quotes exclusive) if there exist four distinct indices i1, i2, i3, i4 such that A[i1] xor A[i2] xor A[i3] xor A[i4] = 0. Otherwise, output "No" (quotes exclusive) please.

-----Example-----
Input:

5
1 0 2 3 7

Output:

Yes
-/

-- <vc-helpers>
-- </vc-helpers>

def check_xor_sequence (n : Nat) (seq : List Nat) : String := sorry

theorem large_sequences_return_yes 
  (n : Nat) (seq : List Nat) 
  (h1 : n ≥ 68) 
  (h2 : seq.length = n) : 
  check_xor_sequence n seq = "Yes" := sorry

theorem small_sequences_return_no
  (n : Nat) (seq : List Nat)
  (h1 : n ≤ 67)
  (h2 : seq.length ≤ 1) :
  check_xor_sequence n seq = "No" := sorry

theorem permutation_invariant
  (n : Nat) (seq : List Nat)
  (h1 : 2 ≤ n) (h2 : n ≤ 67)
  (h3 : 2 ≤ seq.length) (h4 : seq.length ≤ 67) :
  check_xor_sequence n seq = check_xor_sequence n seq.reverse := sorry

theorem xor_pattern_valid 
  (n : Nat) (base : Nat)
  (h1 : 4 ≤ n) (h2 : n ≤ 67)
  (seq : List Nat)
  (h3 : seq = [base, base^^^1, base^^^2, base^^^3] ++ List.replicate (n-4) 0) :
  check_xor_sequence n seq = "Yes" := sorry

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 5 [1, 0, 2, 3, 7]

/-
info: 'No'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 4 [1, 2, 3, 4]

/-
info: 'Yes'
-/
-- #guard_msgs in
-- #eval check_xor_sequence 68 [1] * 68

-- Apps difficulty: interview
-- Assurance level: unguarded