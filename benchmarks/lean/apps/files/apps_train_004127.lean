-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encrypt (text : String) (rule : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encrypt_preserves_length (text : String) (rule : Int) :
  (encrypt text rule).length = text.length :=
sorry

theorem encrypt_periodic_rule (text : String) (rule : Int) :
  encrypt text rule = encrypt text (rule % 256) :=
sorry

theorem encrypt_identity_rule (text : String) :
  encrypt text 0 = text :=
sorry

theorem encrypt_inverse_rules (text : String) (rule : Int) :
  encrypt (encrypt text rule) (-rule) = text :=
sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval encrypt "" 1

/-
info: 'b'
-/
-- #guard_msgs in
-- #eval encrypt "a" 1

/-
info: 'rngcug"gpet{rv"og'
-/
-- #guard_msgs in
-- #eval encrypt "please encrypt me" 2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded