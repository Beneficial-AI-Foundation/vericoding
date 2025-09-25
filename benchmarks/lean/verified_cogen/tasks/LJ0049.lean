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

-- <vc-definitions>
def simpleNested (a : Array Int) (b : Array Int) (N : Int) (h_precond : simpleNested_precond (a) (b) (N)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def simpleNested_postcond (a : Array Int) (b : Array Int) (N : Int) (sum : Int) (h_precond : simpleNested_precond (a) (b) (N)) :=
  N ≤ sum ∧ sum ≤ 2 * N

theorem simpleNested_spec_satisfied (a : Array Int) (b : Array Int) (N : Int) (h_precond : simpleNested_precond (a) (b) (N)) :
    simpleNested_postcond (a) (b) (N) (simpleNested (a) (b) (N) h_precond) h_precond := by
  sorry
-- </vc-theorems>