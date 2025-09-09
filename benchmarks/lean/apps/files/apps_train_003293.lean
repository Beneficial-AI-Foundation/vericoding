def count_consonants (s : List Char) : Nat :=
  sorry

def isConsonant (c : Char) : Bool :=
  sorry

def isVowel (c : Char) : Bool :=
  sorry

def toLower (c : Char) : Char :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def toCharList (s : String) : List Char :=
  sorry

theorem count_consonants_bounds {s : List Char} :
  0 ≤ count_consonants s ∧ count_consonants s ≤ 21 :=
  sorry

theorem count_consonants_case_insensitive {s : List Char} :
  count_consonants s = count_consonants (List.map toLower s) :=
  sorry 

theorem count_consonants_letters_only {s s' : List Char}
  (h : s' = List.filter Char.isAlpha s) :
  count_consonants s = count_consonants s' :=
  sorry

theorem count_consonants_vowels_only {s : List Char}
  (h : ∀ c, c ∈ s → isVowel c) :
  count_consonants s = 0 :=
  sorry

theorem count_consonants_consonants_only {s : List Char} {n : Nat}
  (h1 : ∀ c, c ∈ s → isConsonant c)
  (h2 : n = (List.map toLower s).eraseDups.length) :
  count_consonants s = n :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval count_consonants "sillystring"

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_consonants "aeiou"

/-
info: 21
-/
-- #guard_msgs in
-- #eval count_consonants "abcdefghijklmnopqrstuvwxyz"

-- Apps difficulty: introductory
-- Assurance level: guarded