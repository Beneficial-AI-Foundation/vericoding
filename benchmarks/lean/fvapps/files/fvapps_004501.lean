-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isVowel (c : Char) : Bool :=
  sorry

def find_vowel_substrings (s : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_vowel_substrings_valid_input {s : String}
  (h : ∃ pre mid post : String,
    (∀ c, c ∈ pre.data → !isVowel c) ∧
    (∀ c, c ∈ mid.data → isVowel c) ∧
    (∀ c, c ∈ post.data → !isVowel c) ∧
    mid.length ≥ 2 ∧
    s = pre ++ mid ++ post) :
  ∃ result : List String,
    find_vowel_substrings s = result ∧
    result ≠ ["-1"] ∧
    ∀ substr ∈ result,
      substr.length ≥ 2 ∧
      ∀ c, c ∈ substr.data → isVowel c :=
sorry

theorem find_vowel_substrings_invalid_input {s : String}
  (h : ∀ c, c ∈ s.data → !isVowel c) :
  find_vowel_substrings s = ["-1"] :=
sorry

theorem find_vowel_substrings_general {s : String} :
  let result := find_vowel_substrings s
  result = ["-1"] ∨
  (∀ substr ∈ result,
    substr.length ≥ 2 ∧
    ∀ c, c ∈ substr.data → isVowel c) :=
sorry
-- </vc-theorems>