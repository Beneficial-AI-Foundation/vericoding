-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_letter_count (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_letter_count_output_alnum (s : String) : ∀ c ∈ (string_letter_count s).data, 
  c.isAlphanum := by sorry

theorem string_letter_count_unique_letters (s : String) : 
  let letters := (string_letter_count s).data.filter Char.isAlpha
  letters.Nodup := by sorry 

theorem string_letter_count_correct_counts (s : String) (c : Char) : 
  let result := string_letter_count s
  let resultLetters := result.data.filter Char.isAlpha
  c ∈ resultLetters →
  let count := (s.data.filter (fun x => x.toLower = c.toLower)).length
  let numStr := String.mk (result.data.takeWhile Char.isDigit)
  numStr.length > 0 ∧ String.toNat! numStr = count := by sorry

theorem string_letter_count_sorted (s : String) :
  let letters := (string_letter_count s).data.filter Char.isAlpha
  List.Pairwise (· ≤ ·) letters := by sorry
-- </vc-theorems>