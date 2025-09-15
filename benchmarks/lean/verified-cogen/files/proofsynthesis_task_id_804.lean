-- <vc-preamble>
@[reducible, simp]
def isEven (n : Nat) : Bool :=
  n % 2 = 0

@[reducible, simp]
def isProductEven_precond (arr : Array Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()