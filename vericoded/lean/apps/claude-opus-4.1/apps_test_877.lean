import Mathlib
-- <vc-preamble>

def ValidInput (n m : Int) (pairs : List (Int × Int)) : Prop :=
  n ≥ 2 ∧ 
  m ≥ 0 ∧ 
  pairs.length = m ∧
  (∀ i, 0 ≤ i ∧ i < pairs.length → 1 ≤ (pairs[i]!).1 ∧ (pairs[i]!).1 ≤ n ∧ 1 ≤ (pairs[i]!).2 ∧ (pairs[i]!).2 ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < pairs.length → (pairs[i]!).1 ≠ (pairs[i]!).2)

def computeFinalL (pairs : List (Int × Int)) : Int :=
  match pairs with
  | [] => 1
  | _ :: rest => 
    let x := (pairs[pairs.length-1]!).1
    let y := (pairs[pairs.length-1]!).2
    let minVal := if x < y then x else y
    let restL := computeFinalL rest
    if restL > minVal then restL else minVal

def computeFinalR (n : Int) (pairs : List (Int × Int)) : Int :=
  match pairs with
  | [] => n
  | _ :: rest =>
    let x := (pairs[pairs.length-1]!).1
    let y := (pairs[pairs.length-1]!).2
    let maxVal := if x > y then x else y
    let restR := computeFinalR n rest
    if restR < maxVal then restR else maxVal

def myMax (a b : Int) : Int :=
  if a > b then a else b

def ValidResult (n : Int) (pairs : List (Int × Int)) (result : Int) : Prop :=
  result ≥ 0 ∧
  result ≤ n - 1 ∧
  result = myMax (computeFinalR n pairs - computeFinalL pairs) 0

@[reducible, simp]
def solve_precond (n m : Int) (pairs : List (Int × Int)) : Prop :=
  ValidInput n m pairs
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma computeFinalL_bounds (pairs : List (Int × Int)) : computeFinalL pairs ≥ 1 := by
  induction pairs with
  | nil => simp [computeFinalL]
  | cons _ rest ih =>
    simp [computeFinalL]
    split_ifs <;> linarith

-- LLM HELPER  
lemma computeFinalR_bounds (n : Int) (pairs : List (Int × Int)) (hn : n ≥ 2) : computeFinalR n pairs ≤ n := by
  induction pairs with
  | nil => simp [computeFinalR]
  | cons _ rest ih =>
    simp [computeFinalR]
    split_ifs <;> linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (pairs : List (Int × Int)) (h_precond : solve_precond n m pairs) : Int :=
  myMax (computeFinalR n pairs - computeFinalL pairs) 0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (pairs : List (Int × Int)) (result : Int) (h_precond : solve_precond n m pairs) : Prop :=
  ValidResult n pairs result

theorem solve_spec_satisfied (n m : Int) (pairs : List (Int × Int)) (h_precond : solve_precond n m pairs) :
    solve_postcond n m pairs (solve n m pairs h_precond) h_precond := by
  unfold solve_postcond solve ValidResult
  simp only [solve_precond, ValidInput] at h_precond
  constructor
  · -- result ≥ 0
    simp [myMax]
    split_ifs <;> linarith
  constructor
  · -- result ≤ n - 1  
    simp [myMax]
    split_ifs with h
    · have hl := computeFinalL_bounds pairs
      have hr := computeFinalR_bounds n pairs h_precond.1
      linarith
    · linarith [h_precond.1]
  · -- result = myMax ...
    rfl
-- </vc-theorems>
