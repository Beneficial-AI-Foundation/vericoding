-- <vc-preamble>
@[reducible, simp]
def bitWiseXor_precond (arr1 : Array UInt32) (arr2 : Array UInt32) :=
  arr1.size = arr2.size
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()