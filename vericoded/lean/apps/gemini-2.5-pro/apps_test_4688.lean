import Mathlib
-- <vc-preamble>
def Power (base : Int) (exp : Nat) : Int :=
  if exp = 0 then 1
  else base * Power base (exp - 1)

def ValidInput (n k : Int) : Prop :=
  1 ≤ n ∧ n ≤ 1000 ∧ 2 ≤ k ∧ k ≤ 1000

def PaintingWays (n k : Int) : Int :=
  k * Power (k - 1) (Int.natAbs (n - 1))

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
private theorem Power_pos {base : Int} {exp : Nat} (h_base : 0 < base) : 0 < Power base exp := by
  induction exp with
  | zero =>
    rw [Power, if_pos rfl]
    norm_num
  | succ e ih =>
    rw [Power, if_neg (Nat.succ_ne_zero e), Nat.succ_sub_one e]
    exact Int.mul_pos h_base ih

-- LLM HELPER
private theorem PaintingWays_pos {n k : Int} (h_precond : solve_precond n k) : 0 < PaintingWays n k := by
  obtain ⟨_, _, hk2, _⟩ := h_precond
  rw [PaintingWays]
  apply Int.mul_pos
  · exact lt_of_lt_of_le (by norm_num) hk2
  · have k_minus_one_pos : 0 < k - 1 := by
      exact sub_pos.mpr (lt_of_lt_of_le (by norm_num) hk2)
    exact Power_pos k_minus_one_pos

-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  PaintingWays n k
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : Int) (h_precond : solve_precond n k) : Prop :=
  result = PaintingWays n k ∧ result > 0

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve
  exact ⟨rfl, PaintingWays_pos h_precond⟩
-- </vc-theorems>
