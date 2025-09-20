-- <vc-preamble>
def CHARS_WITH_RINGS := "abdegopqABBDOPQR"

def POSSIBLE_OUTPUTS := ["Not even a medal!", "Bronze!", "Silver!", "Gold!"]
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def olympic_ring (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_in_possible_values (s : String) :
  olympic_ring s ∈ POSSIBLE_OUTPUTS :=
sorry

theorem empty_string_not_medal (s : String) :
  (∀ c, c ∈ s.data → c ∉ CHARS_WITH_RINGS.data) →
  olympic_ring s = "Not even a medal!" :=
sorry

theorem no_ring_chars_not_medal (s : String) :
  (∀ c, c ∈ s.data → c ∉ CHARS_WITH_RINGS.data) →
  olympic_ring s = "Not even a medal!" :=
sorry
-- </vc-theorems>