def vowel (c : Char) : Bool :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def solve (s : String) : Nat :=
sorry

theorem solve_all_vowels (s : String) 
  (h₁ : s.length > 0)
  (h₂ : ∀ c ∈ s.data, vowel c = true) :
  solve s = s.length :=
sorry

theorem solve_interspersed
  (vowels : List String)
  (consonants : List String)
  (h₁ : vowels.length > 0) 
  (h₂ : ∀ s ∈ vowels, s.length > 0)
  (h₃ : ∀ s ∈ vowels, ∀ c ∈ s.data, vowel c = true)
  (h₄ : ∀ s ∈ consonants, ∀ c ∈ s.data, vowel c = false) :
  let combined := List.zip vowels consonants
  let s := String.join (combined.map (fun p => p.1 ++ p.2))
  solve s ≥ (List.foldl (fun acc x => max acc x.length) 0 vowels) :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded