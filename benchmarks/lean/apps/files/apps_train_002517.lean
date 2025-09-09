-- <vc-helpers>
-- </vc-helpers>

def extract_valid_hex_colors (s : String) : List String :=
  sorry

theorem extract_hex_empty_string :
  extract_valid_hex_colors "" = [] := 
  sorry

theorem extract_hex_simple_color :
  extract_valid_hex_colors "color: #fff;" = ["#fff"] :=
  sorry

theorem extract_hex_six_digit :
  extract_valid_hex_colors "color: #123456," = ["#123456"] :=
  sorry

theorem extract_hex_invalid :
  extract_valid_hex_colors "invalid" = [] :=
  sorry

-- Apps difficulty: introductory
-- Assurance level: guarded