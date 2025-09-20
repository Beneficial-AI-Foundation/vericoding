-- <vc-preamble>
def ALAN_TERMS : List String := ["Partridge", "PearTree", "Chat", "Dan", "Toblerone", "Lynn", "AlphaPapa", "Nomad"]

def isAlanTerm (s : String) : Bool :=
  ALAN_TERMS.contains s

def countChar (s : String) (c : Char) : Nat :=
  s.toList.filter (· = c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def part (arr : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_irrelevant_returns_spike_message {arr : List String} :
  (∀ x ∈ arr, ¬isAlanTerm x) →
  part arr = "Lynn, I've pierced my foot on a spike!!" :=
sorry

theorem alan_terms_return_pint_with_exclamations {arr : List String} :
  (arr ≠ []) →
  (∀ x ∈ arr, isAlanTerm x) →
  (part arr).startsWith "Mine's a Pint" ∧
  countChar (part arr) '!' = arr.length :=
sorry

theorem mixed_terms_count_only_alan_terms (alan_arr other_arr : List String) :
  (alan_arr ≠ []) →
  (∀ x ∈ alan_arr, isAlanTerm x) →
  (∀ x ∈ other_arr, ¬isAlanTerm x) →
  countChar (part (alan_arr ++ other_arr)) '!' = alan_arr.length :=
sorry
-- </vc-theorems>