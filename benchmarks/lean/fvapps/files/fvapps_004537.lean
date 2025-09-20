-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shorter_reverse_longer (a b : String) : String := sorry

def reverse (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shorter_reverse_longer_length (a b : String) : 
  let result := shorter_reverse_longer a b
  String.length result = 2 * min (String.length a) (String.length b) + max (String.length a) (String.length b)
  := sorry

theorem shorter_reverse_longer_empty_left (s : String) :
  shorter_reverse_longer "" s = reverse s := sorry

theorem shorter_reverse_longer_empty_right (s : String) :
  shorter_reverse_longer s "" = reverse s := sorry
-- </vc-theorems>