-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseNum (n : Nat) : Nat := sorry

def sum_dif_rev (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_dif_rev_positive (n : Nat) (h : n > 0) (h2 : n ≤ 20) : 
  sum_dif_rev n > 0 := sorry

theorem sum_dif_rev_not_palindrome (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  sum_dif_rev n ≠ reverseNum (sum_dif_rev n) := sorry

theorem sum_dif_rev_satisfies_equation (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  let result := sum_dif_rev n
  let rev := reverseNum result
  (result + rev) % (if rev ≥ result then rev - result else result - rev) = 0 := sorry

theorem sum_dif_rev_strictly_increasing (n : Nat) (h : n > 0) (h2 : n ≤ 19) :
  sum_dif_rev n < sum_dif_rev (n + 1) := sorry

theorem sum_dif_rev_no_trailing_zero (n : Nat) (h : n > 0) (h2 : n ≤ 20) :
  sum_dif_rev n % 10 ≠ 0 := sorry
-- </vc-theorems>