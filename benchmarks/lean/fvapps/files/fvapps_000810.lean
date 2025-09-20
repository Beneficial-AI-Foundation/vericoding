-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_strings (a b : String) : List (List Nat) := sorry

def single_element_list (n : Nat) : List Nat := [n]
-- </vc-definitions>

-- <vc-theorems>
theorem convert_strings_nonempty (a b : String) :
  let result := convert_strings a b
  result.length ≥ 1 := sorry
-- </vc-theorems>