-- <vc-helpers>
-- </vc-helpers>

def interpreter (s : String) : String :=
  sorry

theorem output_valid_chars {tape : String} 
  (h : String.contains tape '&') :
  ∀ c, c ∈ (interpreter tape).data → 0 ≤ Char.toNat c ∧ Char.toNat c < 256 :=
sorry

theorem arithmetic_wrapping (n : Nat) :
  let tape := String.mk ((List.replicate n '+') ++ 
               (List.replicate n '-') ++ ['*', '&'])
  interpreter tape = "\u0000" :=
sorry

/-
info: '\x00'
-/
-- #guard_msgs in
-- #eval interpreter "\\h*&"

/-
info: '\x00'
-/
-- #guard_msgs in
-- #eval interpreter "+-*&"

/-
info: '\x01'
-/
-- #guard_msgs in
-- #eval interpreter "+*&"

-- Apps difficulty: introductory
-- Assurance level: unguarded