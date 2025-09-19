-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def interweave (s1 s2 : List Char) : List Char := sorry

theorem interweave_length_property (s1 s2 : List Char) : 
  List.length (interweave s1 s2) ≤ List.length s1 + List.length s2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem interweave_empty_strings :
  interweave [] [] = [] := sorry

theorem interweave_all_digits :
  interweave ['1', '2', '3'] ['4', '5', '6'] = [] := sorry

theorem interweave_all_spaces :
  interweave [' '] [' '] = [] := sorry 

theorem interweave_basic_case :
  interweave ['a', 'b', 'c'] ['d', 'e', 'f'] = ['a', 'd', 'b', 'e', 'c', 'f'] := sorry
-- </vc-theorems>