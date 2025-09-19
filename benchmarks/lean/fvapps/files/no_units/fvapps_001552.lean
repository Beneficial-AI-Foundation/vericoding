-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subsets_parity (n k : Nat) : String := sorry

def choose (n k : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem subset_parity_full_set (n : Nat) (h : n > 0) : 
  subsets_parity n n = "ODD" := sorry

theorem subset_parity_empty_set (n : Nat) (h : n > 0) :
  subsets_parity n 0 = "ODD" := sorry

theorem valid_subset_parity (n k : Nat) (h1 : n > 0) (h2 : k ≤ n) :
  (subsets_parity n k = "ODD" ↔ choose n k % 2 = 1) ∧
  (subsets_parity n k = "EVEN" ↔ choose n k % 2 = 0) := sorry

theorem valid_subset_result (n k : Nat) (h1 : n > 0) (h2 : k ≤ n) :
  subsets_parity n k = "ODD" ∨ subsets_parity n k = "EVEN" := sorry
-- </vc-theorems>