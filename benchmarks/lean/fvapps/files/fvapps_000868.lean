-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fac (n : Nat) : List Nat := sorry

def max_special_sum (n k s : Nat) (arr : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fac_product (n : Nat) (h : n ≥ 2) :
  let factors := fac n
  factors.foldl (· * ·) 1 = n := sorry

theorem fac_all_prime (n : Nat) (h : n ≥ 2) :
  let factors := fac n
  ∀ p ∈ factors,
    ∀ i : Nat, 2 ≤ i → i < p → ¬(p % i = 0) := sorry

theorem fac_ascending (n : Nat) (h : n ≥ 2) :
  let factors := fac n 
  ∀ i j, i < j → i < factors.length → j < factors.length →
    factors.get! i ≤ factors.get! j := sorry

theorem max_special_sum_exists (n k s : Nat) (arr : List Nat) (h₁ : n > 0) (h₂ : k > 0) (h₃ : s > 0) :
  ∃ i j : Nat, i ≤ j ∧ j < arr.length ∧
  let subarray := arr.take (j+1) |>.drop i
  let curr_sum := subarray.foldl (· + ·) 0
  let prod := subarray.foldl (· * ·) 1
  let prime_factors := (fac prod).eraseDups
  max_special_sum n k s arr = curr_sum * (k - prime_factors.length * s) := sorry

theorem max_special_sum_single (k s : Nat) (h₁ : k > 0) (h₂ : s > 0) :
  let arr := [2]
  max_special_sum 1 k s arr = 2 * (k - (fac 2).eraseDups.length * s) := sorry
-- </vc-theorems>