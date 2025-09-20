-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_unlock_phone (password : String) (words : List String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_valid (password : String) (words : List String) : 
  can_unlock_phone password words = "YES" ∨ can_unlock_phone password words = "NO" :=
sorry

theorem direct_match {words : List String} (h : words ≠ []) :
  can_unlock_phone (words[0]!) words = "YES" :=
sorry

theorem concat_match {words : List String} 
  (h1 : words.length ≥ 2)
  (h2 : words[0]!.length ≥ 2)
  (h3 : words[1]!.length ≥ 1) :
  let firstChar := words[0]!.data[1]!
  let secondChar := words[1]!.data[0]!
  let password := String.mk [firstChar, secondChar]
  can_unlock_phone password words = "YES" :=
sorry

theorem empty_words_no (password : String) :
  can_unlock_phone password [] = "NO" :=
sorry

theorem valid_match_exists (password : String) (words : List String) :
  can_unlock_phone password words = "YES" →
  (∃ w ∈ words, w = password) ∨
  (∃ (i j : Nat) (hi : i < words.length) (hj : j < words.length),
    words[i]!.length ≥ 2 ∧
    words[j]!.length ≥ 1 ∧
    String.mk [words[i]!.data[1]!, words[j]!.data[0]!] = password) :=
sorry
-- </vc-theorems>