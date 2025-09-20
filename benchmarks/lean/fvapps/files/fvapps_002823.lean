-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bin_to_hex (b : String) : String :=
sorry

def hex_to_bin (h : String) : String :=
sorry

def is_hex_digit (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def is_hex_string (s : String) : Bool :=
  s.all is_hex_digit

theorem hex_to_bin_roundtrip (h : String) :
  is_hex_string h →
  bin_to_hex (hex_to_bin h) =
    if h = "" then "0"
    else if h = "0" then "0"
    else h :=
sorry

theorem empty_and_zero_bin_to_hex :
  bin_to_hex "" = "0" ∧
  bin_to_hex "0" = "0" :=
sorry

theorem empty_and_zero_hex_to_bin :
  hex_to_bin "" = "0" ∧
  hex_to_bin "0" = "0" :=
sorry
-- </vc-theorems>