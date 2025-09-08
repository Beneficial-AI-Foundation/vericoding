/-
A positive integer is magical if it is divisible by either A or B.
Return the N-th magical number.  Since the answer may be very large, return it modulo 10^9 + 7.

Example 1:
Input: N = 1, A = 2, B = 3
Output: 2

Example 2:
Input: N = 4, A = 2, B = 3
Output: 6

Example 3:
Input: N = 5, A = 2, B = 4
Output: 10

Example 4:
Input: N = 3, A = 6, B = 4
Output: 8

Note:

1 <= N <= 10^9
2 <= A <= 40000
2 <= B <= 40000
-/

-- <vc-helpers>
-- </vc-helpers>

def MOD := 1000000007

def nthMagicalNumber (n a b : Nat) : Nat :=
  sorry

theorem same_number_property {n : Nat} (h : n > 0) (h2 : n ≤ 10000) :
  nthMagicalNumber n 2 2 = (2 * n) % MOD := by
  sorry

theorem monotonic_increasing {a b : Nat} 
  (ha : a > 0) (hb : b > 0) (ha2 : a ≤ 100) (hb2 : b ≤ 100) :
  nthMagicalNumber 1 a b < nthMagicalNumber 2 a b := by
  sorry

theorem result_bounds {n a b : Nat}
  (hn : n > 0) (ha : a > 0) (hb : b > 0)
  (hn2 : n ≤ 100) (ha2 : a ≤ 100) (hb2 : b ≤ 100) :
  0 ≤ nthMagicalNumber n a b ∧ nthMagicalNumber n a b < MOD := by
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval nth_magical_number 1 2 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval nth_magical_number 4 2 3

/-
info: 10
-/
-- #guard_msgs in
-- #eval nth_magical_number 5 2 4

-- Apps difficulty: interview
-- Assurance level: guarded