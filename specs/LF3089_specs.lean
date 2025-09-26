-- <vc-preamble>
def isConsonant (c : Char) : Bool :=
  c ∈ ['b', 'c', 'd', 'f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't', 'v', 'w', 'x', 'y', 'z']

def isVowel (c : Char) : Bool :=
  c.toLower ∈ ['a', 'e', 'i', 'o', 'u']
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def short_form (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem short_form_length {s : String} :
  String.length (short_form s) ≤ String.length s :=
sorry

theorem short_form_first_last {s : String} (h: String.length s > 0) :
  (s.get! 0 = (short_form s).get! 0) ∧
  (String.length s > 1 → s.get! (String.Pos.mk (s.length - 1)) = (short_form s).get! (String.Pos.mk ((short_form s).length - 1))) :=
sorry

theorem short_form_consonants {s : String} (h : ∀ c, c ∈ s.data → isConsonant c) :
  short_form s = s :=
sorry

theorem short_form_case_preservation {s : String} :
  ∀ c, c ∈ (short_form s).data → c ∈ s.data :=
sorry

theorem short_form_middle_vowels_removed {s : String} :
  ∀ i, 1 ≤ i → i < String.length (short_form s) - 1 →
    ¬(isVowel ((short_form s).get! (String.Pos.mk i))) :=
sorry
-- </vc-theorems>