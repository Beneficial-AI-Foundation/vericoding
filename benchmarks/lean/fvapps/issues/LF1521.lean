-- <vc-preamble>
def sum_of_digits (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem sum_of_digits_no_digits (s : String) 
  (h : ∀ c ∈ s.data, !c.isDigit) : 
  sum_of_digits s = 0 := 
  sorry

theorem sum_of_digits_all_digits (digits : List Nat)
  (h : ∀ d ∈ digits, d ≤ 9) :
  sum_of_digits (String.join (digits.map toString)) = List.sum digits := 
  sorry

theorem sum_of_digits_mixed (letters digits : String)
  (h1 : ∀ c ∈ letters.data, !c.isDigit)
  (h2 : ∀ c ∈ digits.data, c.isDigit) :
  sum_of_digits (letters ++ digits) = sum_of_digits digits :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval sum_of_digits "ab1231da"

/-
info: 6
-/
-- #guard_msgs in
-- #eval sum_of_digits "a1b2c3"

/-
info: 0
-/
-- #guard_msgs in
-- #eval sum_of_digits "nodigits"
-- </vc-theorems>