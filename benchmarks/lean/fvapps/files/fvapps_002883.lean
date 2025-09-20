-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorsRange (n m : Nat) : List (Nat × List Nat) := sorry

-- All returned keys are within range
-- </vc-definitions>

-- <vc-theorems>
theorem factorsRange_keys_in_range
  {n m : Nat} (h : n ≤ m)
  : ∀ k, k ∈ (factorsRange n m).map Prod.fst → n ≤ k ∧ k ≤ m := sorry

-- Length of result matches range size when n ≤ m

theorem factorsRange_length
  {n m : Nat} (h : n ≤ m)
  : (factorsRange n m).length = m - n + 1 := sorry

-- For numbers with factors, each factor divides the number

theorem factorsRange_factors_divide
  {n m k : Nat} (h : n ≤ m)
  : ∀ factors, (k, factors) ∈ factorsRange n m →
    ∀ f ∈ factors, k % f = 0 := sorry

-- Factors are in ascending order

theorem factorsRange_factors_ascending
  {n m k : Nat} (h : n ≤ m)
  : ∀ factors, (k, factors) ∈ factorsRange n m →
    ∀ i j, i < j → i < factors.length → j < factors.length →
    factors[i]! < factors[j]! := sorry

-- Factors are less than their number

theorem factorsRange_factors_less
  {n m k : Nat} (h : n ≤ m)
  : ∀ factors, (k, factors) ∈ factorsRange n m →
    ∀ f ∈ factors, 2 ≤ f ∧ f < k := sorry

-- Single number case returns singleton list

theorem factorsRange_single_number
  {n : Nat}
  : (factorsRange n n).length = 1 ∧
    ∃ factors, (n, factors) ∈ factorsRange n n := sorry

-- Reversed inputs return empty list

theorem factorsRange_reversed_inputs
  {n m : Nat} (h : n > m)
  : factorsRange n m = [] := sorry
-- </vc-theorems>