-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fixed_xor (a b : String) : String := sorry

theorem fixed_xor_identity {a b : String} (h : a.length = b.length) :
  let result := fixed_xor a b
  fixed_xor result b = a := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fixed_xor_commutative {a b : String} (h : a.length = b.length) :
  fixed_xor a b = fixed_xor b a := sorry 

theorem fixed_xor_with_zeros (hex_str : String) :
  let zeros := String.mk (List.replicate hex_str.length '0')
  fixed_xor hex_str zeros = hex_str := sorry

theorem fixed_xor_with_self (hex_str : String) :
  let result := fixed_xor hex_str hex_str
  result.data.all (· = '0') := sorry

/-
info: '07'
-/
-- #guard_msgs in
-- #eval fixed_xor "ab3f" "ac"

/-
info: '163d'
-/
-- #guard_msgs in
-- #eval fixed_xor "aadf" "bce2"

/-
info: '746865206b696420646f6e277420706c6179'
-/
-- #guard_msgs in
-- #eval fixed_xor "1c0111001f010100061a024b53535009181c" "686974207468652062756c6c277320657965"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded