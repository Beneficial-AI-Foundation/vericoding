import Mathlib
-- <vc-preamble>
@[reducible, simp]
def myfun_precond (a : Array Int) (N : Nat) : Prop :=
  N > 0 ∧ a.size = N
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma toNat_lt_of_Int_bounds {k : Int} {N : Nat} (hk : 0 ≤ k ∧ k < (N : Int)) : k.toNat < N := by
  have hk0 : 0 ≤ k := hk.1
  have hkN : k < (N : Int) := hk.2
  have hk_eq : (k.toNat : Int) = k := by
    simpa using Int.toNat_of_nonneg hk0
  have hInt : (k.toNat : Int) < (N : Int) := by
    simpa [hk_eq] using hkN
  exact (Int.ofNat_lt.mp hInt)

-- </vc-helpers>

-- <vc-definitions>
def myfun (a : Array Int) (N : Nat) (h_precond : myfun_precond a N) : Array Int :=
  a.map (fun _ => (N : Int))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def myfun_postcond (a : Array Int) (N : Nat) (result: Array Int) (h_precond : myfun_precond a N) :=
  ∀ k : Int, 0 ≤ k ∧ k < N → result[k.toNat]! % 2 = N % 2

theorem myfun_spec_satisfied (a: Array Int) (N: Nat) (h_precond : myfun_precond a N) :
    myfun_postcond a N (myfun a N h_precond) h_precond := by
  classical
intro k hk
have hkNat : k.toNat < N := toNat_lt_of_Int_bounds hk
have hget : (myfun a N h_precond)[k.toNat]! = (N : Int) := by
  simpa [myfun, hkNat, h_precond.right]
simpa [hget]
-- </vc-theorems>
