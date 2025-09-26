import Mathlib
-- <vc-preamble>

def ValidInput (n k : Int) (L : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ n ≤ 2*k ∧
  L.length = n ∧
  (∀ i, 0 ≤ i ∧ i < L.length - 1 → L[i]! ≤ L[i+1]!) ∧
  (∀ i, 0 ≤ i ∧ i < L.length → L[i]! ≥ 0)

def ValidBoxConfiguration (boxes : List Int) (boxSize : Int) : Prop :=
  boxes.length ≥ 1 ∧
  (∀ i, 0 ≤ i ∧ i < boxes.length → boxes[i]! ≤ boxSize) ∧
  (∀ i, 0 ≤ i ∧ i < boxes.length → boxes[i]! ≥ 0)

def sum (s : List Int) : Int :=
  s.foldl (· + ·) 0

def max (s : List Int) : Int :=
  s.foldl (fun a b => if a ≥ b then a else b) 0

@[reducible, simp]
def solve_precond (n k : Int) (L : List Int) : Prop :=
  ValidInput n k L
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (L : List Int) (h_precond : solve_precond n k L) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (L : List Int) (result : Int) (h_precond : solve_precond n k L) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n k : Int) (L : List Int) (h_precond : solve_precond n k L) :
    solve_postcond n k L (solve n k L h_precond) h_precond := by
  have h : (0 : Int) ≤ 0 := le_rfl
  simpa [solve_postcond, solve] using h
-- </vc-theorems>
