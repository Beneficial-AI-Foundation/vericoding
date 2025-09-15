-- <vc-preamble>
-- Specification function for rotation split point
def rotationSplit (len : Nat) (n : Nat) : Int :=
  len - (n % len)

-- Precondition for rotate_right function
@[reducible, simp]
def rotateRight_precond (list : Array UInt32) (n : Nat) : Prop :=
  list.size > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()