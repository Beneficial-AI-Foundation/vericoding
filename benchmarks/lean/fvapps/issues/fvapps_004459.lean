-- <vc-preamble>
def isValidTime (t : Time) : Prop := 
  t.hours ≤ 23 ∧ t.minutes ≤ 59

def lateClock (digits : List Nat) : String :=
sorry

def toNat (c : Char) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getDigit (s : String) (i : Nat) : Char :=
s.data.get! i
-- </vc-definitions>

-- <vc-theorems>
theorem late_clock_output_format 
  {digits : List Nat}
  (h : digits.length = 4)
  (h' : ∀ d ∈ digits, d ≤ 9)
  (h'' : ∃ t : Time, isValidTime t) :
  let result := lateClock digits
  (result.length = 5) ∧ 
  (getDigit result 2 = ':') ∧
  (getDigit result 0).isDigit ∧
  (getDigit result 1).isDigit ∧
  (getDigit result 3).isDigit ∧
  (getDigit result 4).isDigit :=
sorry

theorem late_clock_valid_time
  {digits : List Nat}
  (h : digits.length = 4)
  (h' : ∀ d ∈ digits, d ≤ 9)
  (h'' : ∃ t : Time, isValidTime t) :
  let result := lateClock digits
  let t : Time := {
    hours := toNat (getDigit result 0) * 10 + toNat (getDigit result 1)
    minutes := toNat (getDigit result 3) * 10 + toNat (getDigit result 4)
  }
  isValidTime t :=
sorry

theorem late_clock_uses_all_digits
  {digits : List Nat}
  (h : digits.length = 4)
  (h' : ∀ d ∈ digits, d ≤ 9)
  (h'' : ∃ t : Time, isValidTime t) :
  let result := lateClock digits
  let result_digits := [
    toNat (getDigit result 0),
    toNat (getDigit result 1),
    toNat (getDigit result 3),
    toNat (getDigit result 4)
  ]
  ∃ σ : Fin 4 → Fin 4, 
    (∀ a b : Fin 4, σ a = σ b → a = b) ∧ 
    (∀ b : Fin 4, ∃ a : Fin 4, σ a = b) ∧
    (∀ i : Fin 4, digits.get! i.val = result_digits.get! (σ i).val) :=
sorry

/-
info: '21:59'
-/
-- #guard_msgs in
-- #eval late_clock [9, 1, 2, 5]

/-
info: '19:38'
-/
-- #guard_msgs in
-- #eval late_clock [1, 9, 8, 3]

/-
info: '22:20'
-/
-- #guard_msgs in
-- #eval late_clock [0, 2, 2, 2]
-- </vc-theorems>