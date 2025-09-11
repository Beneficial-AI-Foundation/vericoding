-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def yellow_be_gone (color : String) : String := sorry

def yellow_colors : List String := ["gold", "khaki", "lemonchiffon", "lightgoldenrodyellow", 
                     "lightyellow", "palegoldenrod", "yellow"]

def yellow_mapping : List (String × String) := [("gold", "ForestGreen"), ("khaki", "LimeGreen"),
                      ("lemonchiffon", "PaleGreen"), ("lightgoldenrodyellow", "SpringGreen"),
                      ("lightyellow", "MintCream"), ("palegoldenrod", "LightGreen"),
                      ("yellow", "Lime")]
-- </vc-definitions>

-- <vc-theorems>
theorem yellow_mapping_consistent {color : String} (h : color ∈ yellow_colors) :
  ∃ mapped : String, (color, mapped) ∈ yellow_mapping ∧ yellow_be_gone color = mapped := sorry

theorem non_yellow_colors_unchanged {color : String} 
  (h1 : color.length > 0)
  (h2 : ¬color.startsWith "#") 
  (h3 : ¬(color.toLower ∈ yellow_colors)) :
  yellow_be_gone color = color := sorry

theorem hex_color_format {hex : String}
  (h1 : hex.startsWith "#")
  (h2 : hex.length = 7)
  (h3 : ∀ (c : Char), c ∈ hex.data.tail → 
       c.isDigit ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')) :
  let result := yellow_be_gone hex
  result.startsWith "#" ∧ result.length = 7 := sorry

/-
info: 'PaleGreen'
-/
-- #guard_msgs in
-- #eval yellow_be_gone "lemonchiffon"

/-
info: 'ForestGreen'
-/
-- #guard_msgs in
-- #eval yellow_be_gone "GOLD"

/-
info: 'LightGreen'
-/
-- #guard_msgs in
-- #eval yellow_be_gone "pAlEgOlDeNrOd"

/-
info: '#0bb886'
-/
-- #guard_msgs in
-- #eval yellow_be_gone "#b8860b"

/-
info: '#C71585'
-/
-- #guard_msgs in
-- #eval yellow_be_gone "#C71585"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded