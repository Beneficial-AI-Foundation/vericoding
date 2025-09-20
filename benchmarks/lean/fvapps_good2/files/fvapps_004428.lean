-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def alphabetized (s : String) : String :=
sorry

def sorted_list (l : List Char) : List Char :=
sorry

def isAlpha (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alphabetized_is_sorted (s : String) :
  let result := alphabetized s
  result = String.mk (sorted_list (result.data)) :=
sorry

theorem alphabetized_only_letters (s : String) :
  let result := alphabetized s
  ∀ c ∈ result.data, isAlpha c :=
sorry

theorem alphabetized_preserves_count (s : String) :
  let result := alphabetized s
  let original_letters := s.data.filter isAlpha
  result.length = original_letters.length ∧
  sorted_list (result.data.map Char.toLower) = sorted_list (original_letters.map Char.toLower) :=
sorry

theorem alphabetized_empty_string :
  alphabetized "" = "" :=
sorry

theorem alphabetized_no_letters (s : String) :
  (∀ c ∈ s.data, ¬isAlpha c) →
  alphabetized s = "" :=
sorry
-- </vc-theorems>