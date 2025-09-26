-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isHexDigit (c : Char) : Bool :=
sorry

def rgb (r g b : Int) : String :=
sorry

def hexStringToNat (s : String) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rgb_output_format (r g b : Int) :
  let result := rgb r g b
  (result.length = 6) ∧
  (result.data.all isHexDigit)
  :=
sorry

theorem rgb_valid_inputs (r g b : Int)
  (hr : 0 ≤ r ∧ r ≤ 255)
  (hg : 0 ≤ g ∧ g ≤ 255)
  (hb : 0 ≤ b ∧ b ≤ 255) :
  let result := rgb r g b
  let r_hex := result.take 2
  let g_hex := result.drop 2 |>.take 2
  let b_hex := result.drop 4 |>.take 2
  (hexStringToNat r_hex = r) ∧
  (hexStringToNat g_hex = g) ∧
  (hexStringToNat b_hex = b)
  :=
sorry

theorem rgb_negative_inputs (r g b : Int)
  (hr : r < 0)
  (hg : g < 0)
  (hb : b < 0) :
  rgb r g b = "000000"
  :=
sorry

theorem rgb_large_inputs (r g b : Int)
  (hr : r > 255)
  (hg : g > 255)
  (hb : b > 255) :
  rgb r g b = "FFFFFF"
  :=
sorry
-- </vc-theorems>