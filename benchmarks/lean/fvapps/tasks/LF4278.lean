-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_obj (nums: List Nat) : List (String × Char) := sorry

def charOfNat (n: Nat) : Char := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_obj_length {nums: List Nat} : 
  (nums.all (· ≤ 127)) → 
  (num_obj nums).length = nums.length := sorry

theorem num_obj_key_matches_input {nums: List Nat} :
  (nums.all (· ≤ 127)) →
  ∀ i, i < nums.length → 
  ((num_obj nums).get ⟨i, by sorry⟩).1 = toString (nums.get ⟨i, by sorry⟩) := sorry 

theorem num_obj_value_is_ascii {nums: List Nat} :
  (nums.all (· ≤ 127)) →
  ∀ i, i < nums.length →
  charOfNat (nums.get ⟨i, by sorry⟩) = ((num_obj nums).get ⟨i, by sorry⟩).2 := sorry

theorem num_obj_preserves_input {nums nums_copy: List Nat} :
  (nums.all (· ≤ 127)) →
  nums_copy = nums →
  nums_copy = nums := sorry
-- </vc-theorems>