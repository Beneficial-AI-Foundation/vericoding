-- <vc-preamble>
@[reducible, simp]
def extractRearChars_precond (s : Array (Array Char)) :=
  ∀ i, i < s.size → s[i]!.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()