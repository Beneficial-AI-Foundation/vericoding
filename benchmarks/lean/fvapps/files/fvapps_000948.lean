-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode_message (s : String) : String := sorry

theorem encode_preserves_length (s : String) : 
  (encode_message s).length = s.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_double_is_identity (s : String) : 
  encode_message (encode_message s) = s := sorry

theorem encode_reflection_property (s : String) (i : Nat) 
  (h1 : i + 1 < s.length) :
  let encoded := encode_message s
  have h_len : (encode_message s).length = s.length := encode_preserves_length s
  have h2 : i < s.length := Nat.lt_of_succ_lt h1
  have h3 : i < (encode_message s).length := by simp [h_len, h2]
  have h4 : i + 1 < (encode_message s).length := by simp [h_len, h1]
  (s.data[i]'h2).isLower = true →
  (s.data[i+1]'h1).isLower = true →
  Char.toNat 'a' + (Char.toNat 'z' - Char.toNat (s.data[i+1]'h1)) = Char.toNat ((encode_message s).data[i]'h3) ∧
  Char.toNat 'a' + (Char.toNat 'z' - Char.toNat (s.data[i]'h2)) = Char.toNat ((encode_message s).data[i+1]'h4) := sorry

theorem encode_output_lowercase (s : String) (i : Nat) (h : i < (encode_message s).length) :
  ((encode_message s).data[i]'h).isLower = true := sorry
-- </vc-theorems>