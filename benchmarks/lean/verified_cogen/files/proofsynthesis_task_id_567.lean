-- <vc-preamble>
@[reducible, simp]
def isSorted_precond (arr : Array Int) :=
  arr.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()