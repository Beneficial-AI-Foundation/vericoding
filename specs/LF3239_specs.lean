-- <vc-preamble>
def add_check_digit (num : String) : String := sorry

-- Length property: result is one char longer and preserves input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mkFactors (n : Nat) : List Nat :=
  let base := [2,3,4,5,6,7]
  let repeats := n / 6 + 1
  List.join (List.replicate repeats base)

-- Calculation property: check digit follows formula
-- </vc-definitions>

-- <vc-theorems>
theorem check_digit_length
  (num : String)
  (h : num.all (fun c => '0' ≤ c ∧ c ≤ '9')) :
  let result := add_check_digit num
  (result.length = num.length + 1) ∧
  (result.dropRight 1 = num) := sorry

-- Format property: last char is digit or X

theorem check_digit_format
  (num : String)
  (h : num.all (fun c => '0' ≤ c ∧ c ≤ '9')) :
  let result := add_check_digit num
  let last := result.back
  (('0' ≤ last ∧ last ≤ '9') ∨ last = 'X') := sorry

theorem check_digit_calculation
  (num : String)
  (h : num.all (fun c => '0' ≤ c ∧ c ≤ '9')) :
  let result := add_check_digit num
  let factors := mkFactors num.length
  let nums := num.toList.reverse.map (fun c => c.toNat - '0'.toNat)
  let products := List.zipWith (· * ·) nums factors
  let total := products.foldl (· + ·) 0
  let remainder := total % 11
  ((remainder = 0 → result.back = '0') ∧
   (remainder = 1 → result.back = 'X') ∧
   (remainder > 1 → result.back = (Char.ofNat ('0'.toNat + (11 - remainder))))) := sorry

/-
info: '0365327'
-/
-- #guard_msgs in
-- #eval add_check_digit "036532"

/-
info: '123888782'
-/
-- #guard_msgs in
-- #eval add_check_digit "12388878"

/-
info: '6789X'
-/
-- #guard_msgs in
-- #eval add_check_digit "6789"
-- </vc-theorems>