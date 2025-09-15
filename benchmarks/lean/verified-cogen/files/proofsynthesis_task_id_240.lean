-- <vc-preamble>
@[reducible, simp]
def replaceLastElement_precond (first : Array Int) (second : Array Int) : Prop :=
  first.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()