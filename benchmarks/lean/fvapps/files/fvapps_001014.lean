-- <vc-preamble>
def MOD := 1000000007

def isVowel (c : Char) : Bool :=
  match c.toLower with
  | 'a' | 'e' | 'i' | 'o' | 'u' => true
  | _ => false
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveBinaryNames (name : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binary_names_result_range
  (name : String)
  (h : ∃ c ∈ name.data, c.isAlpha) :
  0 ≤ solveBinaryNames name ∧ solveBinaryNames name < MOD :=
sorry

theorem only_letters_matter
  (name : String)
  (h : ∃ c ∈ name.data, c.isAlpha) :
  solveBinaryNames name = solveBinaryNames (String.mk (name.data.filter Char.isAlpha)) :=
sorry

theorem all_vowels_zero
  (name : String)
  (h₁ : name.length > 0)
  (h₂ : ∀ c ∈ name.data, isVowel c) :
  solveBinaryNames name = ((2 ^ name.length - 1) % MOD) :=
sorry

theorem all_consonants_one
  (name : String)
  (h₁ : name.length > 0)
  (h₂ : ∀ c ∈ name.data, c.isAlpha ∧ ¬isVowel c) :
  solveBinaryNames name = ((2 ^ name.length - 1) % MOD) :=
sorry
-- </vc-theorems>