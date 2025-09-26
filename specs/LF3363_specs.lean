-- <vc-preamble>
def calculateCheckDigit (code : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validateEAN (code : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_ean_with_check_digit {code : String} (h1 : code.length = 12) (h2 : ∀ c ∈ code.data, '0' ≤ c ∧ c ≤ '9') : 
  validateEAN (code ++ toString (calculateCheckDigit code)) = true :=
sorry

theorem invalid_ean_check {code : String} (h1 : code.length = 13) (h2 : ∀ c ∈ code.data, '0' ≤ c ∧ c ≤ '9') :
  ¬(validateEAN code) →
  let digits := code.data.map (fun c => c.toNat - '0'.toNat)
  ((digits.enum.foldl (fun acc (i, d) => acc + if i % 2 = 0 then d else d * 3) 0) % 10 ≠ 0) :=
sorry

theorem ean_length_requirement {code : String} :
  validateEAN code → code.length = 13 :=
sorry

theorem ean_digits_only {code : String} (h : ∃ c ∈ code.data, ¬('0' ≤ c ∧ c ≤ '9')) :
  ¬(validateEAN code) :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_ean "4003301018398"

/-
info: False
-/
-- #guard_msgs in
-- #eval validate_ean "4003301018392"

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_ean "9783815820865"
-- </vc-theorems>