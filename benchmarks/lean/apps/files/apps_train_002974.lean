/-
# Task
 A media access control address (MAC address) is a unique identifier assigned to network interfaces for communications on the physical network segment.

 The standard (IEEE 802) format for printing MAC-48 addresses in human-friendly form is six groups of two hexadecimal digits (0 to 9 or A to F), separated by hyphens (e.g. 01-23-45-67-89-AB).

# Example

 For `inputString = "00-1B-63-84-45-E6"`, the output should be `true`;

 For `inputString = "Z1-1B-63-84-45-E6"`, the output should be `false`;

 For `inputString = "not a MAC-48 address"`, the output should be `false`.

# Input/Output

 - `[input]` string `inputString`

 - `[output]` a boolean value

    `true` if inputString corresponds to MAC-48 address naming rules, `false` otherwise.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_mac_48_address (s : String) : Bool := sorry

def is_valid_hex_digit (c : Char) : Bool :=
  (c.toNat ≥ 48 ∧ c.toNat ≤ 57) ∨ (c.toNat ≥ 65 ∧ c.toNat ≤ 70)

theorem valid_mac_is_accepted (mac : String)
  (h : ∃ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Char,
    is_valid_hex_digit h1 ∧ is_valid_hex_digit h2 ∧ is_valid_hex_digit h3 ∧ 
    is_valid_hex_digit h4 ∧ is_valid_hex_digit h5 ∧ is_valid_hex_digit h6 ∧
    is_valid_hex_digit h7 ∧ is_valid_hex_digit h8 ∧ is_valid_hex_digit h9 ∧
    is_valid_hex_digit h10 ∧ is_valid_hex_digit h11 ∧ is_valid_hex_digit h12 ∧
    mac = String.mk [h1, h2, '-', h3, h4, '-', h5, h6, '-', 
                    h7, h8, '-', h9, h10, '-', h11, h12]) :
  is_mac_48_address mac := sorry

theorem invalid_format_rejected (s : String)
  (h : ¬∃ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Char,
    is_valid_hex_digit h1 ∧ is_valid_hex_digit h2 ∧ is_valid_hex_digit h3 ∧ 
    is_valid_hex_digit h4 ∧ is_valid_hex_digit h5 ∧ is_valid_hex_digit h6 ∧
    is_valid_hex_digit h7 ∧ is_valid_hex_digit h8 ∧ is_valid_hex_digit h9 ∧
    is_valid_hex_digit h10 ∧ is_valid_hex_digit h11 ∧ is_valid_hex_digit h12 ∧
    s.toUpper = String.mk [h1, h2, '-', h3, h4, '-', h5, h6, '-', 
                          h7, h8, '-', h9, h10, '-', h11, h12]) :
  ¬is_mac_48_address s := sorry

theorem case_insensitive (mac : String) :
  is_mac_48_address mac.toLower = is_mac_48_address mac.toUpper := sorry

theorem invalid_separators (mac : String) (sep : Char)
  (h1 : sep ≠ '-')
  (h2 : ∃ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 : Char,
    is_valid_hex_digit h1 ∧ is_valid_hex_digit h2 ∧ is_valid_hex_digit h3 ∧ 
    is_valid_hex_digit h4 ∧ is_valid_hex_digit h5 ∧ is_valid_hex_digit h6 ∧
    is_valid_hex_digit h7 ∧ is_valid_hex_digit h8 ∧ is_valid_hex_digit h9 ∧
    is_valid_hex_digit h10 ∧ is_valid_hex_digit h11 ∧ is_valid_hex_digit h12 ∧
    mac = String.mk [h1, h2, '-', h3, h4, '-', h5, h6, '-', 
                    h7, h8, '-', h9, h10, '-', h11, h12]) :
  ¬is_mac_48_address (mac.replace "-" (String.mk [sep])) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_mac_48_address "00-1B-63-84-45-E6"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_mac_48_address "Z1-1B-63-84-45-E6"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_mac_48_address "not a MAC-48 address"

-- Apps difficulty: introductory
-- Assurance level: unguarded