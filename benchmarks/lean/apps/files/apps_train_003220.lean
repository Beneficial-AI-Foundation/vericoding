-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binary_to_string (s : String) : String := sorry

def is_binary_string (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_to_string_length 
  (binary : String)
  (h : is_binary_string binary)
  (h2 : String.length binary % 8 = 0) :
  String.length (binary_to_string binary) = String.length binary / 8 := sorry

theorem binary_to_string_roundtrip
  (binary : String)
  (h : is_binary_string binary)
  (h2 : String.length binary % 8 = 0)
  (h3 : binary ≠ "") :
  let result := binary_to_string binary
  let binary_again := String.join (result.data.map (fun c => 
    String.mk [c]))
  binary = binary_again := sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval binary_to_string ""

/-
info: 'Hello'
-/
-- #guard_msgs in
-- #eval binary_to_string "0100100001100101011011000110110001101111"

/-
info: '1011'
-/
-- #guard_msgs in
-- #eval binary_to_string "00110001001100000011000100110001"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded