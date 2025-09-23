-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def count_valid_subsequences (arr : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_positive (a b : Nat) (h : b > 0) : 
  gcd a b ≥ 1 := sorry

theorem gcd_divides (a b : Nat) (h : b > 0) :
  (a % gcd a b = 0 ∨ a = 0) ∧ b % gcd a b = 0 := sorry

theorem gcd_symmetric (a b : Nat) (h : b > 0) :
  gcd a b = gcd b a ∨ a = 0 := sorry

theorem subsequence_count_nonnegative (arr : List Nat) (h : arr ≠ []) :
  count_valid_subsequences arr ≥ 0 := sorry

theorem subsequence_count_upper_bound (arr : List Nat) (h : arr ≠ []) :
  count_valid_subsequences arr ≤ 2^(arr.length) := sorry

theorem subsequence_count_permutation_invariant (arr arr_perm : List Nat) 
  (h₁ : arr ≠ []) (h₂ : arr_perm.isPerm arr) :
  count_valid_subsequences arr = count_valid_subsequences arr_perm := sorry

theorem all_ones_subsequence_count (arr : List Nat) 
  (h₁ : arr ≠ []) (h₂ : ∀ x ∈ arr, x = 1) :
  count_valid_subsequences arr = 2^(arr.length) - 1 := sorry
-- </vc-theorems>