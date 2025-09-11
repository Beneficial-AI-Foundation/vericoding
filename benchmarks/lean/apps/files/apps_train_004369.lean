-- <vc-preamble>
def add (a b : String) : String := sorry

def binary_to_int (s : String) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_binary (s : String) : Bool := sorry

theorem strips_leading_zeros (binary : String) : 
  let result := add binary "0"
  (result.startsWith "0" → result = "0") ∧ 
  binary_to_int result = binary_to_int binary := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem add_commutative (a b : String) :
  add a b = add b a := sorry

theorem matches_integer_addition (a b : String) :
  let result := add a b
  is_valid_binary result ∧
  binary_to_int result = binary_to_int a + binary_to_int b := sorry

theorem identity (binary : String) :
  binary_to_int (add binary "0") = binary_to_int binary := sorry

theorem empty_strings_zero :
  add "" "" = "0" := sorry

theorem empty_string_one :
  add "" "1" = "1" ∧ add "1" "" = "1" := sorry

/-
info: '1001'
-/
-- #guard_msgs in
-- #eval add "111" "10"

/-
info: '10010'
-/
-- #guard_msgs in
-- #eval add "1101" "101"

/-
info: '100100'
-/
-- #guard_msgs in
-- #eval add "1101" "10111"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded