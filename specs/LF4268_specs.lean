-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tribonacci (signature : List Int) (n : Nat) : List Int := sorry

theorem tribonacci_length (signature : List Int) (n : Nat) : 
  (tribonacci signature n).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem tribonacci_empty (signature : List Int) :
  tribonacci signature 0 = [] := sorry

theorem tribonacci_matches_signature (signature : List Int) (n : Nat) :
  n ≥ 3 → (tribonacci signature n).take 3 = signature.take 3 := sorry

theorem tribonacci_sum_rule (signature : List Int) (n : Nat) (i : Nat) :
  n > 3 → i ≥ 3 → i < n → 
  (tribonacci signature n).get! i = 
    (tribonacci signature n).get! (i-3) + 
    (tribonacci signature n).get! (i-2) + 
    (tribonacci signature n).get! (i-1) := sorry

theorem tribonacci_single_element (signature : List Int) :
  tribonacci signature 1 = signature.take 1 := sorry

theorem tribonacci_monotonic (signature : List Int) (i : Nat) :
  (∀ x ∈ signature, x ≥ 0) →
  i ≥ 3 → i < (tribonacci signature 10).length - 1 →
  (tribonacci signature 10).get! i ≤ (tribonacci signature 10).get! (i+1) := sorry
-- </vc-theorems>