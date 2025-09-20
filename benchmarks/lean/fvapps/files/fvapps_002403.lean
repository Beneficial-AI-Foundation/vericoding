-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prefix_of_word (sentence search : String) : Int :=
  sorry

def startsWith (s₁ s₂ : String) : Bool :=
  sorry

def words (s : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_search_property {sentence : String} :
  is_prefix_of_word sentence "" = 1 :=
sorry
-- </vc-theorems>