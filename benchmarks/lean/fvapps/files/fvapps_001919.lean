-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_binary_after_delete (binary : String) : String := sorry

def stringToBinaryNat (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_valid_binary (binary : String) 
  (h : binary.length > 0)
  (h2 : ∀ c ∈ binary.data, c = '0' ∨ c = '1') :
  let result := find_max_binary_after_delete binary
  ∀ c ∈ result.data, c = '0' ∨ c = '1' ∧ result.length > 0 := sorry

theorem result_not_greater_than_original (binary : String)
  (h : binary.length > 0)
  (h2 : ∀ c ∈ binary.data, c = '0' ∨ c = '1') :
  let result := find_max_binary_after_delete binary 
  stringToBinaryNat result ≤ stringToBinaryNat binary := sorry

theorem result_no_leading_zeros (binary : String)
  (h : binary.length > 0) 
  (h2 : ∀ c ∈ binary.data, c = '0' ∨ c = '1') :
  let result := find_max_binary_after_delete binary
  result = "0" ∨ result.get 0 = '1' := sorry

theorem edge_cases :  
  find_max_binary_after_delete "0" = "0" ∧
  find_max_binary_after_delete "1" = "0" ∧
  find_max_binary_after_delete "00" = "0" := sorry
-- </vc-theorems>