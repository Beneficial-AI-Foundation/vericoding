-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_speeches (n k m : Nat) (arr : List Nat) : Int := sorry

-- Theorem 1: If input array contains 0, result is -1
-- </vc-definitions>

-- <vc-theorems>
theorem min_speeches_zero_in_array
  (n k m : Nat)
  (arr : List Nat)
  (h1 : k ≤ n)
  (h2 : arr.length = n)
  (h3 : ∃ x ∈ arr, x = 0) :
  min_speeches n k m arr = -1 := sorry

-- Theorem 2: If no zeros in array, result is non-negative

theorem min_speeches_no_zero_nonneg
  (n k m : Nat)
  (arr : List Nat)
  (h1 : k ≤ n) 
  (h2 : arr.length = n)
  (h3 : ∀ x ∈ arr, x ≠ 0) :
  min_speeches n k m arr ≥ 0 := sorry

-- Theorem 3: Large enough values need 0 speeches

theorem min_speeches_large_values_zero
  (n k : Nat)
  (h : k ≤ n) :
  min_speeches n k 1 (List.replicate n 1000) = 0 := sorry
-- </vc-theorems>