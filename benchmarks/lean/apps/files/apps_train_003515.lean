def CHARS_WITH_RINGS := "abdegopqABBDOPQR"

def olympic_ring (s : String) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

def POSSIBLE_OUTPUTS := ["Not even a medal!", "Bronze!", "Silver!", "Gold!"]

theorem output_in_possible_values (s : String) : 
  olympic_ring s ∈ POSSIBLE_OUTPUTS := sorry

theorem empty_string_not_medal (s : String) :
  (∀ c, c ∈ s.data → c ∉ CHARS_WITH_RINGS.data) → 
  olympic_ring s = "Not even a medal!" := sorry

theorem no_ring_chars_not_medal (s : String) :
  (∀ c, c ∈ s.data → c ∉ CHARS_WITH_RINGS.data) →
  olympic_ring s = "Not even a medal!" := sorry

/-
info: 'Bronze!'
-/
-- #guard_msgs in
-- #eval olympic_ring "wHjMudLwtoPGocnJ"

/-
info: 'Not even a medal!'
-/
-- #guard_msgs in
-- #eval olympic_ring "JKniLfLW"

/-
info: 'Gold!'
-/
-- #guard_msgs in
-- #eval olympic_ring "IMBAWejlGRTDWetPS"

-- Apps difficulty: introductory
-- Assurance level: unguarded