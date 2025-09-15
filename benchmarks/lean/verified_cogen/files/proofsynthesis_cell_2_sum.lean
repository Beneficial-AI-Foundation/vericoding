-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array UInt32) (N : UInt32) :=
  a.size = N.toNat ∧ N.toNat ≤ 0x7FFF_FFFF
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

def main : IO Unit := pure ()