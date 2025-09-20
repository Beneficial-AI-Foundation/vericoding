-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def char_concat (s : String) : String := sorry

theorem spaces_handling (word : String) :
  char_concat word = char_concat (word.replace " " "") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_pair {word : String} (h : word.length ≥ 2) :
  let result := char_concat word
  (result.data[0]! = word.data[0]!) ∧ 
  (result.data[1]! = word.data[word.length - 1]!) ∧
  (result.data[2]! = '1') := sorry
-- </vc-theorems>