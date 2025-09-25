-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_mac_48_address (s : String) : Bool := sorry

def is_valid_hex_digit (c : Char) : Bool :=
  (c.toNat ≥ 48 ∧ c.toNat ≤ 57) ∨ (c.toNat ≥ 65 ∧ c.toNat ≤ 70)
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>