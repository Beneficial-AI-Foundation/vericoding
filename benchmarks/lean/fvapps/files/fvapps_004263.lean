-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def positive_to_negative (binary : List Nat) : List Nat := sorry

theorem output_is_binary (binary : List Nat) 
  (h : binary.all (fun x => x = 0 ∨ x = 1)) 
  (h' : binary.length > 0) :
  (positive_to_negative binary).all (fun x => x = 0 ∨ x = 1) ∧ 
  (positive_to_negative binary).length = binary.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_zeros_unchanged (binary : List Nat)
  (h : binary.all (fun x => x = 0))
  (h' : binary.length > 0) :
  positive_to_negative binary = binary := sorry

theorem flips_after_rightmost_one (binary : List Nat)
  (h : binary.all (fun x => x = 0 ∨ x = 1))
  (h' : binary.length > 0) :
  match binary.findIdx? (· = 1) with
  | none => positive_to_negative binary = binary
  | some last_one_idx => 
    (∀ i, i < last_one_idx → 
      (positive_to_negative binary).get ⟨i, sorry⟩ = 1 - binary.get ⟨i, sorry⟩) ∧
    (∀ i, last_one_idx < i → i < binary.length →
      (positive_to_negative binary).get ⟨i, sorry⟩ = binary.get ⟨i, sorry⟩)
  := sorry

theorem double_conversion_preserves_magnitude (binary : List Nat)
  (h : binary.all (fun x => x = 0 ∨ x = 1))
  (h' : binary.length ≥ 2)
  (h'' : binary.head? = some 0) :
  positive_to_negative (positive_to_negative binary) = binary := sorry
-- </vc-theorems>