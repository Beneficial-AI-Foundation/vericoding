-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def to_bits (s : String) : List Nat := sorry

theorem to_bits_length (s : String) (h : ∃ nums : List Nat, 
    (∀ n ∈ nums, n < 5000) ∧ 
    (s = String.intercalate "\n" (nums.map toString))) : 
  (to_bits s).length = 5000 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem to_bits_binary (s : String) (h : ∃ nums : List Nat, 
    (∀ n ∈ nums, n < 5000) ∧ 
    (s = String.intercalate "\n" (nums.map toString))) :
  ∀ x ∈ to_bits s, x = 0 ∨ x = 1 := sorry

theorem to_bits_indices {nums : List Nat} (s : String) (h : 
    (∀ n ∈ nums, n < 5000) ∧ 
    (s = String.intercalate "\n" (nums.map toString))) :
  ((List.enum (to_bits s)).filter (fun p => p.2 = 1)).map Prod.fst = nums := sorry

theorem to_bits_invalid_chars (s : String) :
  (∃ c ∈ s.data, ¬(c = '\n' ∨ ('0' ≤ c ∧ c ≤ '9'))) →
  to_bits s = [] := sorry
-- </vc-theorems>