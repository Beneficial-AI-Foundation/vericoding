-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def print_rangoli (n: Nat) : String := sorry

def splitLines (s: String) : List String := 
  s.split (· = '\n')
-- </vc-definitions>

-- <vc-theorems>
theorem rangoli_edge_cases (n: Nat) (h: n = 1 ∨ n = 26):
  let result := print_rangoli n
  result.length > 0 ∧
  (result.data.filter (· = '\n')).length = 2*n-2 := sorry
-- </vc-theorems>