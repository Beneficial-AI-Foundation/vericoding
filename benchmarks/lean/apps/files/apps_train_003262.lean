def Result := String
deriving Repr, BEq

def alphabet_war (s : String) : Result := sorry

def alphabet_war_valid_result (s : String) : 
  let result := alphabet_war s
  result = "Left side wins!" ∨ result = "Right side wins!" ∨ result = "Let's fight again!" := sorry

def only_left_letters_never_right (s : String) :
  (∀ c ∈ s.data, c ∈ ['w', 'p', 'b', 's']) →
  s.length > 0 →
  alphabet_war s ≠ "Right side wins!" := sorry

def only_right_letters_never_left (s : String) :
  (∀ c ∈ s.data, c ∈ ['m', 'q', 'd', 'z']) →
  s.length > 0 →
  alphabet_war s ≠ "Left side wins!" := sorry

def only_bombs_is_draw (s : String) :
  (∀ c ∈ s.data, c = '*') →
  s.length > 0 →
  alphabet_war s = "Let's fight again!" := sorry

def adjacent_bomb_nullifies (c : Char) :
  c ∈ ['w', 'p', 'b', 's', 'm', 'q', 'd', 'z'] →
  alphabet_war (String.mk ['*', c]) = "Let's fight again!" ∧
  alphabet_war (String.mk [c, '*']) = "Let's fight again!" := sorry

-- <vc-helpers>
-- </vc-helpers>

def repeated_string_same_winner (s : String) :
  (∀ c ∈ s.data, c ∈ ['w', 'p', 'b', 's', 'm', 'q', 'd', 'z']) →
  s.length > 0 →
  alphabet_war s = alphabet_war (s ++ s) := sorry

/-
info: 'Right side wins!'
-/
-- #guard_msgs in
-- #eval alphabet_war "z"

/-
info: "Let's fight again!"
-/
-- #guard_msgs in
-- #eval alphabet_war "z*dq*mw*pb*s"

/-
info: 'Left side wins!'
-/
-- #guard_msgs in
-- #eval alphabet_war "sz**z**zs"

-- Apps difficulty: introductory
-- Assurance level: unguarded