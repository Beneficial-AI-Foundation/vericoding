-- <vc-preamble>
def absent_vowel (s : String) : VowelIndex := 
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getVowel (i : Nat) : Char :=
  match i with
  | 0 => 'a'
  | 1 => 'e'
  | 2 => 'i'
  | 3 => 'o'
  | _ => 'u'
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_valid_index {s : String} (h : s.length > 0) :
  (absent_vowel s).val ≤ 4 :=
  sorry

theorem identified_vowel_actually_missing {s : String} (h : s.length > 0) :
  let result := (absent_vowel s).val
  ¬ s.contains (getVowel result) :=
  sorry

theorem only_one_vowel_missing {s : String} (h : s.length > 0) :
  let vowels := "aeiou"
  let text_vowels_count := (List.filter (fun c => vowels.contains c) s.data).length
  text_vowels_count = 4 →
  ¬ s.contains (getVowel (absent_vowel s).val) :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval absent_vowel "John Doe hs seven red pples under his bsket"

/-
info: 3
-/
-- #guard_msgs in
-- #eval absent_vowel "Bb Smith sent us six neatly arranged range bicycles"
-- </vc-theorems>