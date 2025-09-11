-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contamination (text char : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contamination_length_matches_input
  (text char : String)
  (h : char.length = 1) :
  (contamination text char).length = text.length :=
sorry

theorem contamination_uses_char
  (text char : String)
  (h : char.length = 1)
  (i : Nat)
  (hi : i < (contamination text char).length)
  (h0 : 0 < char.data.length) :
  (contamination text char).data[i]'hi = char.data[0]'h0 :=
sorry

theorem contamination_empty_char
  (text : String) :
  contamination text "" = "" :=
sorry

theorem contamination_empty_text
  (char : String) :
  contamination "" char = "" :=
sorry

/-
info: 'zzz'
-/
-- #guard_msgs in
-- #eval contamination "abc" "z"

/-
info: ''
-/
-- #guard_msgs in
-- #eval contamination "" "z"

/-
info: ''
-/
-- #guard_msgs in
-- #eval contamination "abc" ""

/-
info: '&&&&&&&&'
-/
-- #guard_msgs in
-- #eval contamination "_3ebzgh4" "&"

/-
info: '      '
-/
-- #guard_msgs in
-- #eval contamination "//case" " "
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded