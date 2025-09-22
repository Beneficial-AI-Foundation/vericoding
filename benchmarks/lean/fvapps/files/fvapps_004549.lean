-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (s : String) : String := sorry
def decode (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_decode_roundtrip (s : String) :
  decode (encode s) = s := sorry 

theorem decode_encode_roundtrip (s : String) :
  encode (decode s) = s := sorry

theorem map_symmetry {k v : Char} (h : encode k.toString = v.toString) :
  decode v.toString = k.toString := sorry

theorem case_preservation (s : String) (i : String.Pos) :
  let encoded := encode s
  (s.get i).isUpper = (encoded.get i).isUpper ∧ 
  (s.get i).isLower = (encoded.get i).isLower := sorry

theorem non_alpha_unchanged (s : String) (i : String.Pos) :
  let encoded := encode s
  ¬(s.get i).isAlpha → s.get i = encoded.get i := sorry
-- </vc-theorems>