-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def watch_pyramid_from_the_side (chars : Option String) : Option String :=
sorry

def watch_pyramid_from_above (chars : Option String) : Option String :=
sorry

def count_visible_characters_of_the_pyramid (chars : Option String) : Int :=
sorry

def count_all_characters_of_the_pyramid (chars : Option String) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_inputs {chars : Option String} :
  chars = none ∨ chars = some "" →
  watch_pyramid_from_the_side chars = chars ∧
  watch_pyramid_from_above chars = chars ∧
  count_visible_characters_of_the_pyramid chars = -1 ∧
  count_all_characters_of_the_pyramid chars = -1 :=
sorry

theorem count_visible_chars {s : String} (h : s.length > 0) :
  count_visible_characters_of_the_pyramid (some s) =
    (2 * s.length - 1) * (2 * s.length - 1) :=
sorry
-- </vc-theorems>