import Mathlib
-- <vc-preamble>
def Lucas : Nat → Int
  | 0 => 2
  | 1 => 1
  | n + 2 => Lucas (n + 1) + Lucas n

def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 86

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma natAbs_eq_toNat {n : Int} (h : 0 ≤ n) : n.toNat = n.natAbs := by
  cases n with
  | ofNat m => rfl
  | negSucc m => contradiction
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  Lucas n.toNat
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result: Int) (h_precond : solve_precond n) : Prop :=
  result = Lucas n.natAbs

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve
  simp only [solve_precond, ValidInput] at h_precond
  have h_pos : 1 ≤ n := h_precond.1
  have h_nonneg : 0 ≤ n := by omega
  congr 1
  exact natAbs_eq_toNat h_nonneg
-- </vc-theorems>
