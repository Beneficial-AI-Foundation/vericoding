-- <vc-preamble>
def pattern (n : Nat) : String := sorry 

def isSingleDigit (c: Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'

def stringContainsSubstr (s : String) (substr : String) : Bool := sorry
def stringContainsChar (s : String) (c : Char) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stringRepeat (n : Nat) (s : String) : String := sorry

theorem non_positive_input_returns_empty_string {n : Int} (h : n ≤ 0) :
  pattern n.toNat = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_correct {n : Nat} (h1 : n ≥ 1) (h2 : n ≤ 9) :
  let lines := (pattern n).splitOn "\n"
  let middle := lines.get! (n-1)
  (∀ i : Nat, 1 ≤ i ∧ i < n → stringContainsSubstr middle (toString i)) ∧
  stringContainsSubstr middle (stringRepeat n (toString n)) := sorry

theorem double_digit_wrapping {n : Nat} (h1 : n ≥ 10) (h2 : n ≤ 100) :
  let lines := (pattern n).splitOn "\n"
  let middle := lines.get! (n-1)
  ∀ c ∈ middle.data, isSingleDigit c := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval pattern 3

/-
info: expected2
-/
-- #guard_msgs in
-- #eval pattern 5

/-
info: ''
-/
-- #guard_msgs in
-- #eval pattern -3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded