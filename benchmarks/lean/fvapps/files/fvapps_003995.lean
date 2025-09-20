-- <vc-preamble>
def countChar (s : String) (c : Char) : Nat :=
  s.foldl (fun acc x => if x = c then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spin_solve (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_string (s : String) :
  ∃ (result : String), spin_solve s = result :=
sorry

theorem single_word_properties (word : String) :
  word ≠ "" →
  (word.length > 6 ∨ (countChar word.toLower 't' > 1) →
    spin_solve word = String.join (word.data.reverse.map toString)) ∧
  (word.length = 2 → spin_solve word = word.toUpper) ∧
  (word.length = 1 → spin_solve word = "0") :=
sorry

theorem punctuation_preservation (word : String) (punct : Char) :
  word ≠ "" →
  punct ∈ ['.', '!', '?', ',', ':', ';'] →
  (spin_solve (word.push punct)).back = punct :=
sorry

theorem space_preservation (sentence : String) :
  countChar sentence ' ' = countChar (spin_solve sentence) ' ' :=
sorry
-- </vc-theorems>