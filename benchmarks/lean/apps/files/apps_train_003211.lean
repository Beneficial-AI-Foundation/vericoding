-- <vc-helpers>
-- </vc-helpers>

def encrypter (s : String) : String := sorry

theorem encrypter_reversible {s : String} 
  (h : ∀ c ∈ s.data, 97 ≤ c.val ∧ c.val ≤ 122) :
  encrypter (encrypter s) = s.toLower := sorry

theorem encrypter_preserves_spaces {s : String}
  (h : ∀ c ∈ s.data, (97 ≤ c.val ∧ c.val ≤ 122) ∨ c = ' ') :
  (∀ i : String.Pos, s.get i = ' ' → (encrypter s).get i = ' ') ∧
  s.length = (encrypter s).length := sorry

theorem encrypter_output_charset {s : String}
  (h : ∀ c ∈ s.data, (97 ≤ c.val ∧ c.val ≤ 122) ∨ c = ' ') :
  ∀ c ∈ (encrypter s).data, (97 ≤ c.val ∧ c.val ≤ 122) ∨ c = ' ' := sorry

theorem encrypter_case_insensitive {s : String}
  (h : ∀ c ∈ s.data, 65 ≤ c.val ∧ c.val ≤ 122) :
  encrypter s.toLower = encrypter s.toUpper := sorry

/-
info: 'man'
-/
-- #guard_msgs in
-- #eval encrypter "amz"

/-
info: 'fibby'
-/
-- #guard_msgs in
-- #eval encrypter "hello"

/-
info: 'qibkyai ty tfi yvgmzenmteyz'
-/
-- #guard_msgs in
-- #eval encrypter "welcome to the organization"

-- Apps difficulty: introductory
-- Assurance level: unguarded