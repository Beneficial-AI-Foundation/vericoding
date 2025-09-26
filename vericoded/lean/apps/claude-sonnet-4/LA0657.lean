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
-- LLM HELPER: Lemmas for proving positivity of PaintingWays
lemma Power_pos_of_pos_base {base : Int} {exp : Nat} (h : base > 0) : Power base exp > 0 := by
  induction exp with
  | zero => 
    unfold Power
    norm_num
  | succ n ih => 
    unfold Power
    apply mul_pos h ih

lemma PaintingWays_pos {n k : Int} (h : ValidInput n k) : PaintingWays n k > 0 := by
  unfold PaintingWays
  apply mul_pos
  · unfold ValidInput at h
    omega
  · apply Power_pos_of_pos_base
    unfold ValidInput at h
    omega
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
  constructor
  · rfl
  · exact PaintingWays_pos h_precond
-- </vc-theorems>
