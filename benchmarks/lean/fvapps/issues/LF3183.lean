-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hexStringToRGB (s : String) : Option RGB := sorry

theorem hex_string_to_RGB_valid {r g b : Nat} 
  (hr : r ≤ 255) (hg : g ≤ 255) (hb : b ≤ 255) :
  ∀ (hex : String),
  match hexStringToRGB hex with
  | none => True
  | some rgb => 
    rgb.r ≤ 255 ∧ 
    rgb.g ≤ 255 ∧ 
    rgb.b ≤ 255 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hex_string_to_RGB_correct {r g b : Nat}
  (hr : r ≤ 255) (hg : g ≤ 255) (hb : b ≤ 255) :
  ∀ (hex : String),
  match hexStringToRGB hex with
  | none => True
  | some rgb =>
    rgb.r = r ∧
    rgb.g = g ∧
    rgb.b = b := sorry

/-
info: {'r': 255, 'g': 153, 'b': 51}
-/
-- #guard_msgs in
-- #eval hex_string_to_RGB "#FF9933"

/-
info: {'r': 190, 'g': 173, 'b': 237}
-/
-- #guard_msgs in
-- #eval hex_string_to_RGB "#beaded"

/-
info: {'r': 0, 'g': 0, 'b': 0}
-/
-- #guard_msgs in
-- #eval hex_string_to_RGB "#000000"
-- </vc-theorems>