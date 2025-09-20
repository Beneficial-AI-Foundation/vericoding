-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def esrever (s : String) : String := sorry

theorem esrever_preserves_length (s : String) (h : s ≠ "") :
  String.length (esrever s) = String.length s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_reversed_empty : 
  esrever "" = "" := sorry 

theorem double_reverse_equals_original (s : String) (h : s ≠ "") : 
  esrever (esrever s) = s := sorry

/- For any character that appears in the string, it appears the same number of times
    in the reversed string -/

theorem reverse_maintains_character_counts (s : String) (h : s ≠ "") (c : Char) :
  (s.data.countP (· = c)) = ((esrever s).data.countP (· = c)) := sorry
-- </vc-theorems>