-- <vc-preamble>
def ListMin (l : List Int) : Int := 
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => if y < acc then y else acc) x

def ValidInput (n : Int) (v : Int) (sellers : List (List Int)) : Prop :=
  n ≥ 0 ∧ v ≥ 0 ∧ sellers.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < sellers.length → (sellers[i]!).length > 0

def ValidOutput (count : Int) (indices : List Int) (n : Int) : Prop :=
  count = indices.length ∧ count ≥ 0 ∧ count ≤ n ∧
  (∀ i, 0 ≤ i ∧ i < indices.length → 1 ≤ (indices[i]!) ∧ (indices[i]!) ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < indices.length - 1 → (indices[i]!) < (indices[i+1]!))

def CorrectSolution (v : Int) (sellers : List (List Int)) (indices : List Int) : Prop :=
  (∀ i, 0 ≤ i ∧ i < sellers.length → (sellers[i]!).length > 0) →
  (∀ i, 0 ≤ i ∧ i < indices.length → 1 ≤ (indices[i]!) ∧ (indices[i]!) ≤ sellers.length) →
  (∀ i, 0 ≤ i ∧ i < indices.length → v > ListMin (sellers[Int.natAbs ((indices[i]!) - 1)]!)) ∧
  (∀ i, 0 ≤ i ∧ i < sellers.length → (v > ListMin (sellers[i]!) ↔ (i + 1) ∈ indices.map Int.natAbs))

@[reducible, simp]
def solve_precond (n : Int) (v : Int) (sellers : List (List Int)) : Prop :=
  ValidInput n v sellers
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (v : Int) (sellers : List (List Int)) (h_precond : solve_precond n v sellers) : Int × List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (v : Int) (sellers : List (List Int)) (result : Int × List Int) (h_precond : solve_precond n v sellers) : Prop :=
  ValidOutput result.1 result.2 n ∧ CorrectSolution v sellers result.2

theorem solve_spec_satisfied (n : Int) (v : Int) (sellers : List (List Int)) (h_precond : solve_precond n v sellers) :
    solve_postcond n v sellers (solve n v sellers h_precond) h_precond := by
  sorry
-- </vc-theorems>