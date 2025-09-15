-- <vc-preamble>
@[reducible, simp]
def maxDafnyLsp_precond (a : Array Int) := a.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()