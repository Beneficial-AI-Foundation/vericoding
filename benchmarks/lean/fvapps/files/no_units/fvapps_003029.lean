-- <vc-preamble>
def sumNested : List (List Int) → Int
  | _ => sorry

def flatten : List (List Int) → List Int
  | _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listSum : List Int → Int
  | [] => 0
  | h :: t => h + listSum t

/- Sum of nested lists equals the sum of flattened list -/
-- </vc-definitions>

-- <vc-theorems>
theorem sum_nested_equals_flatten_sum (l : List (List Int)) :
  sumNested l = listSum (flatten l) := by
  sorry
-- </vc-theorems>