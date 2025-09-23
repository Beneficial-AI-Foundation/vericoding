-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array UInt32) (N : UInt32) :=
  a.size = N.toNat ∧ N.toNat ≤ 0x7FFF_FFFF
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array UInt32) (N : UInt32) (h_precond : myfun_precond a N) : UInt32 :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array UInt32) (N : UInt32) (sum: UInt32) (h_precond : myfun_precond a N) :=
  sum.toNat ≤ 2 * N.toNat

theorem myfun_spec_satisfied (a: Array UInt32) (N: UInt32) (h_precond : myfun_precond a N) :
    myfun_postcond a N (myfun a N h_precond) h_precond := by
  sorry
-- </vc-theorems>