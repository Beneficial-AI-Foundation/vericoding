-- <vc-helpers>
-- </vc-helpers>

def isSolvable (words : List String) (result : String) : Bool := sorry

theorem result_length_property 
  (words : List String) (result : String) :
  (∃ w ∈ (result :: words), String.length result < String.length w) →
  ¬(isSolvable words result) :=
sorry

theorem single_letter_words_solvable
  (words : List String) (result : String)
  (h1 : ∀ w ∈ words, String.length w = 1)
  (h2 : String.length result = 1)
  (h3 : result ∉ words) :
  (let chars := List.foldl (λ acc s => acc ++ s.data) [] (words ++ [result]);
   let uniqueChars := chars.eraseDups;
   uniqueChars.length ≤ 10) →
  isSolvable words result :=
sorry

theorem leading_zero_property
  (words : List String) (result : String) :
  let allWords := result :: words
  let firstChars := (allWords.map (λ w => w.data.get! 0)).eraseDups
  let allChars := List.foldl (λ acc s => acc ++ s.data) [] allWords
  let uniqueChars := allChars.eraseDups
  (uniqueChars.length ≤ 9 ∧ firstChars.length ≤ 9) →
  isSolvable words result →
  ∀ mapping : Char → Nat,
    (∀ c ∈ firstChars, mapping c ≠ 0) :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval isSolvable ["THIS", "IS", "TOO"] "FUNNY"

/-
info: True
-/
-- #guard_msgs in
-- #eval isSolvable ["SEND", "MORE"] "MONEY"

/-
info: True
-/
-- #guard_msgs in
-- #eval isSolvable ["AB", "CD"] "EF"

-- Apps difficulty: interview
-- Assurance level: unguarded