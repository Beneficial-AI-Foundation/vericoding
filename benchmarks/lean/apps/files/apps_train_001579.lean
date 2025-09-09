-- <vc-helpers>
-- </vc-helpers>

def encode (s : String) : String × Nat := sorry
def decode (s : String) (n : Nat) : String := sorry

theorem encode_decode_roundtrip {s : String} (h : s ≠ "") : 
  let (encoded, idx) := encode s
  decode encoded idx = s := sorry

theorem encode_length {s : String} (h : s ≠ "") :
  let (encoded, idx) := encode s
  String.length encoded = String.length s ∧ 
  idx < String.length s := sorry 

theorem encode_empty :
  encode "" = ("", 0) := sorry

theorem decode_empty :
  decode "" 0 = "" := sorry

theorem encoded_chars_permutation {s : String} (h : s ≠ "") :
  let (encoded, _) := encode s
  encoded.data.length = s.data.length := sorry

theorem encode_output_type {s : String} (h : s ≠ "") :
  let (encoded, idx) := encode s
  encoded.length > 0 ∧ idx ≥ 0 := sorry

theorem decode_output_type {s : String} (h : s ≠ "") :
  let (encoded, idx) := encode s
  let decoded := decode encoded idx
  decoded.length = s.length := sorry

/-
info: s1
-/
-- #guard_msgs in
-- #eval decode *encoded1

/-
info: s2
-/
-- #guard_msgs in
-- #eval decode *encoded2

/-
info: s3
-/
-- #guard_msgs in
-- #eval decode *encoded3

-- Apps difficulty: interview
-- Assurance level: unguarded