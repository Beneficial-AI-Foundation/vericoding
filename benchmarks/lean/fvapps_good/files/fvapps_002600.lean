-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def last (s : String) : List String := sorry

def isWordChar (c : Char) : Bool := 32 ≤ c.val ∧ c.val ≤ 126

-- All words from input are present in output with same frequency
-- </vc-definitions>

-- <vc-theorems>
theorem last_maintains_words (s : String) 
  (h : ∀ c ∈ s.data, isWordChar c) :
  ∀ w ∈ s.split (· = ' '), 
    (s.split (· = ' ')).count w = (last s).count w := sorry

-- Words are sorted by their last character

theorem last_sorted_by_last_char (s : String)
  (h : ∀ c ∈ s.data, isWordChar c) :
  ∀ i < (last s).length - 1,
    let w1 := (last s)[i]!
    let w2 := (last s)[i+1]!
    match w1.data.getLast?, w2.data.getLast? with
    | some c1, some c2 => c1 ≤ c2
    | _, _ => True := sorry

-- Duplicate words in input remain in output  

theorem last_preserves_duplicates (s : String)
  (h : ∀ c ∈ s.data, isWordChar c) :
  ∀ w ∈ s.split (· = ' '),
    (s.split (· = ' ')).count w = (last s).count w := sorry
-- </vc-theorems>