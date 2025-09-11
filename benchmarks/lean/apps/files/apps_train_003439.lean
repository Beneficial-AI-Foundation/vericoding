-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (message : String) (key : String) : String := sorry
def decode (message : String) (key : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_key_chars_unchanged (message : String) (key : String) (i : String.Pos) :
  let key_chars := (key.toLower ++ key.toUpper).toList.toArray
  ¬(key_chars.contains (message.get i)) →
  (encode message key).get i = message.get i := sorry

theorem consistent_encoding (message key : String) :
  encode message key = encode message key := sorry

/-
info: 'Gug hgs g cgt'
-/
-- #guard_msgs in
-- #eval encode "Ala has a cat" "gaderypoluki"

/-
info: 'Dkucr pu yhr ykbir'
-/
-- #guard_msgs in
-- #eval encode "Dance on the table" "politykarenu"

/-
info: 'GBCE'
-/
-- #guard_msgs in
-- #eval encode "ABCD" "gaderypoluki"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded