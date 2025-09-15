-- <vc-preamble>
@[reducible, simp]
def stringXor_precond (a : Array Char) (b : Array Char) : Prop :=
  a.size = b.size ∧ 
  (∀ i, i < a.size → a[i]! = '0' ∨ a[i]! = '1') ∧
  (∀ i, i < b.size → b[i]! = '0' ∨ b[i]! = '1')
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()