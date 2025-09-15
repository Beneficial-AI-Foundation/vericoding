-- <vc-preamble>
@[reducible, simp]
def simpleNested_precond (a : Array Int) (b : Array Int) (N : Int) :=
  (∀ k : Int, k ≤ b[k.toNat]! ∧ b[k.toNat]! ≤ k + 1) ∧
  a.size = N.toNat ∧
  b.size = N.toNat ∧
  N ≤ 0x3FFF_FFFF
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := return ()