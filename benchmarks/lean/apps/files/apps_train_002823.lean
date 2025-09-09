def bin_to_hex (b : String) : String := sorry 
def hex_to_bin (h : String) : String := sorry

def is_hex_digit (c : Char) : Bool := sorry 

-- Helper for theorem statement

-- <vc-helpers>
-- </vc-helpers>

def is_hex_string (s : String) : Bool := 
  s.all is_hex_digit

theorem hex_to_bin_roundtrip (h : String) :
  is_hex_string h → 
  bin_to_hex (hex_to_bin h) = 
    if h = "" then "0" 
    else if h = "0" then "0"
    else h := sorry

theorem empty_and_zero_bin_to_hex :
  bin_to_hex "" = "0" ∧ 
  bin_to_hex "0" = "0" := sorry

theorem empty_and_zero_hex_to_bin :
  hex_to_bin "" = "0" ∧
  hex_to_bin "0" = "0" := sorry

/-
info: '5'
-/
-- #guard_msgs in
-- #eval bin_to_hex "000101"

/-
info: '4d2'
-/
-- #guard_msgs in
-- #eval bin_to_hex "10011010010"

/-
info: '0'
-/
-- #guard_msgs in
-- #eval bin_to_hex "000"

/-
info: '1111'
-/
-- #guard_msgs in
-- #eval hex_to_bin "00F"

/-
info: '101'
-/
-- #guard_msgs in
-- #eval hex_to_bin "5"

/-
info: '10011010010'
-/
-- #guard_msgs in
-- #eval hex_to_bin "04D2"

-- Apps difficulty: introductory
-- Assurance level: unguarded