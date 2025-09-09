-- <vc-helpers>
-- </vc-helpers>

def encode (s : String) : String := sorry

theorem encode_case_insensitive (s : String) : 
  encode s.toUpper = encode s.toLower := sorry

theorem encode_produces_only_digits (s : String) (p : String.Pos) :
  ((encode s).get p).isDigit := sorry

theorem encode_length_consistency (s : String) :
  (encode s).length = s.data.foldl (fun acc c => acc + (toString (c.toUpper.toNat - 64)).length) 0 := sorry

theorem encode_single_letter (c : Char) :
  encode (String.mk [c]) = toString (c.toUpper.toNat - 64) := sorry

/-
info: '123'
-/
-- #guard_msgs in
-- #eval encode "abc"

/-
info: '1234'
-/
-- #guard_msgs in
-- #eval encode "ABCD"

/-
info: '2626262626'
-/
-- #guard_msgs in
-- #eval encode "ZzzzZ"

/-
info: '123-#@5'
-/
-- #guard_msgs in
-- #eval encode "abc-#@5"

/-
info: '208919 919 1 1215147 1920189147!! 161251195 [51431545] @30181853201225'
-/
-- #guard_msgs in
-- #eval encode "this is a long string!! Please [encode] @C0RrEctly"

-- Apps difficulty: introductory
-- Assurance level: unguarded