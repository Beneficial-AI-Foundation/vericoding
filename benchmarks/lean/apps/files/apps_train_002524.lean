-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def duck_shoot (ammo : Nat) (aim : Float) (ducks : String) : String := sorry

theorem duck_shoot_length_preserving (ammo : Nat) (aim : Float) (ducks : String) :
  (duck_shoot ammo aim ducks).length = ducks.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem duck_shoot_valid_chars (ammo : Nat) (aim : Float) (ducks : String) (pos : String.Pos) :
  let result := duck_shoot ammo aim ducks
  result.get pos = '|' ∨ 
  result.get pos = '~' ∨
  result.get pos = '2' ∨ 
  result.get pos = 'X' := sorry

theorem duck_shoot_preserve_non_ducks (ammo : Nat) (aim : Float) (ducks : String) (pos : String.Pos) :
  ducks.get pos ≠ '2' →
  (duck_shoot ammo aim ducks).get pos = ducks.get pos := sorry

theorem duck_shoot_hits_bounded (ammo : Nat) (aim : Float) (ducks : String) :
  (duck_shoot ammo aim ducks).data.countP (· = 'X') ≤ UInt32.toNat (Float.toUInt32 (ammo.toFloat * aim)) := sorry

theorem duck_shoot_hits_match_remaining (ammo : Nat) (aim : Float) (ducks : String) :
  ducks.data.countP (· = '2') - (duck_shoot ammo aim ducks).data.countP (· = '2') = 
  (duck_shoot ammo aim ducks).data.countP (· = 'X') := sorry

/-
info: '|~~~~~XX~2~~~~~|'
-/
-- #guard_msgs in
-- #eval duck_shoot 6 0.41 "|~~~~~22~2~~~~~|"

/-
info: '|~~X~~~X2~2~~22~2~~~~2~~~|'
-/
-- #guard_msgs in
-- #eval duck_shoot 4 0.64 "|~~2~~~22~2~~22~2~~~~2~~~|"

/-
info: '|~~~~~~~X~2~~~|'
-/
-- #guard_msgs in
-- #eval duck_shoot 9 0.22 "|~~~~~~~2~2~~~|"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded