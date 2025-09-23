-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_valid_password (s : String) : PasswordResult :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_invalid :
  check_valid_password "" = PasswordResult.Invalid := by
  sorry

theorem duplicate_chars_invalid (s : String) (h: s.length ≥ 2) 
  (h2: ∃ c, c ∈ s.data) : 
  let s' := s ++ (String.mk [s.data[0]!]) 
  check_valid_password s' = PasswordResult.Invalid := by
  sorry

theorem unique_alphanumeric_valid (s : String) 
  (h1: s.length > 0)
  (h2: ∀ c ∈ s.data, c.isAlphanum)
  (h3: ∀ i j, i < s.length → j < s.length → i ≠ j → s.data[i]! ≠ s.data[j]!) :
  check_valid_password s = PasswordResult.Valid := by
  sorry

theorem non_alphanumeric_invalid (s : String)
  (h1: s.length > 0) 
  (h2: ∃ c ∈ s.data, !c.isAlphanum) :
  check_valid_password s = PasswordResult.Invalid := by
  sorry

theorem result_is_valid_or_invalid (s : String) :
  (check_valid_password s = PasswordResult.Valid) ∨ 
  (check_valid_password s = PasswordResult.Invalid) := by
  sorry

/-
info: expected[i]
-/
-- #guard_msgs in
-- #eval check_valid_password passwords[i]

/-
info: 'Valid'
-/
-- #guard_msgs in
-- #eval check_valid_password "abc123"

/-
info: 'Invalid'
-/
-- #guard_msgs in
-- #eval check_valid_password "abcc123"
-- </vc-theorems>