-- <vc-preamble>
-- Precondition for replace function (no specific requirements in this case)
@[reducible, simp]
def replace_precond (a : Array Int) (x : Int) (y : Int) := True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()