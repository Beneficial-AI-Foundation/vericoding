-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_numbers (nums : List String) : List Int := sorry

def is_palindrome (s : String) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_numbers_preserves_length {nums : List String} :
  List.length (reverse_numbers nums) = List.length nums := sorry
-- </vc-theorems>