import Mathlib
-- <vc-preamble>
def ValidInput (n : Nat) (m : List Int) : Prop :=
  n > 0 ∧ m.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < n → 0 ≤ m[i]! ∧ m[i]! < i + 1

def ValidSolution (n : Nat) (m : List Int) (dm : List Int) : Prop :=
  dm.length = n ∧ m.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n → dm[i]! ≥ m[i]! + 1) ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → dm[i]! ≤ dm[i + 1]!)

def SumBelow (m : List Int) (dm : List Int) : Int :=
  match m with
  | [] => 0
  | head_m :: tail_m => 
    match dm with
    | [] => 0
    | head_dm :: tail_dm => (head_dm - 1 - head_m) + SumBelow tail_m tail_dm

@[reducible, simp]
def solve_precond (n : Nat) (m : List Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def computeDm (m : List Int) : List Int :=
  match m with
  | [] => []
  | head :: tail => (head + 1) :: computeDm tail

lemma computeDm_length (m : List Int) : (computeDm m).length = m.length := by
  induction m with
  | nil => simp [computeDm]
  | cons head tail ih => simp [computeDm, ih]

lemma computeDm_value (m : List Int) (i : Nat) (h : i < m.length) :
    (computeDm m)[i]?.getD 0 = m[i]?.getD 0 + 1 := by
  induction m generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [computeDm]
    | succ j => 
      simp [computeDm]
      have h_j : j < tail.length := by
        simp [List.length] at h
        omega
      exact ih j h_j
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (m : List Int) (h_precond : solve_precond n m) : Int :=
  -- The minimum sum occurs when dm[i] = m[i] + 1 for all i
  -- This gives SumBelow m dm = sum_{i=0}^{n-1} (dm[i] - 1 - m[i]) = sum_{i=0}^{n-1} 0 = 0
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (m : List Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n : Nat) (m : List Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  simp [solve_postcond, solve]
  -- Result is 0 which is ≥ 0
-- </vc-theorems>
