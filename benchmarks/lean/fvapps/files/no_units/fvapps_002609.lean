-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def scramble (text : String) (indices : List Int) : String := sorry

theorem scramble_length_preserved 
  (text : String) 
  (indices : List Int) 
  (h1 : text.length > 0) :
  (scramble text indices).length = text.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem scramble_chars_same_sorted
  (text : String)
  (indices : List Int)
  (h1 : text.length > 0) :
  String.toList (scramble text indices) = String.toList text := sorry
-- </vc-theorems>