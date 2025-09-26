import Mathlib
-- <vc-preamble>

@[reducible, simp]
def ValidInput (n k : Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0 ∧ k ≤ n

@[reducible, simp]
def ValidOutput (result : List Int) (n k : Int) : Prop :=
  result.length = 2 ∧ 
  result[0]! ≥ 0 ∧ 
  result[1]! ≥ 0 ∧ 
  result[0]! ≤ result[1]! ∧
  result[0]! ≤ n - k ∧
  result[1]! ≤ n - k

def MinGoodApartments (n k : Int) (h : ValidInput n k) : Int :=
  if k = 0 ∨ k = n then 0 else 1

def MaxGoodApartments (n k : Int) (h : ValidInput n k) : Int :=
  if k = 0 ∨ k = n then 0
  else if n - k < k * 2 then n - k
  else k * 2

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  ValidInput n k
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic lemmas for the proof
lemma list_length_two_cons : ∀ (a b : Int), [a, b].length = 2 := by simp

lemma list_getElem_zero_cons (a b : Int) : [a, b][0]! = a := by simp

lemma list_getElem_one_cons (a b : Int) : [a, b][1]! = b := by simp
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : List Int :=
  [MinGoodApartments n k h_precond, MaxGoodApartments n k h_precond]
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result : List Int) (h_precond : solve_precond n k) : Prop :=
  ValidOutput result n k ∧
  result[0]! = MinGoodApartments n k h_precond ∧
  result[1]! = MaxGoodApartments n k h_precond

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  unfold solve_postcond solve ValidOutput
  simp only [list_length_two_cons, list_getElem_zero_cons, list_getElem_one_cons]
  constructor
  · -- ValidOutput
    constructor
    · simp  -- length = 2
    constructor
    · -- MinGoodApartments ≥ 0
      unfold MinGoodApartments
      split_ifs
      · norm_num
      · norm_num
    constructor
    · -- MaxGoodApartments ≥ 0  
      unfold MaxGoodApartments
      split_ifs with h1 h2
      · norm_num
      · have : k ≥ 0 := h_precond.2.1
        have : n ≥ 1 := h_precond.1
        omega
      · have : k ≥ 0 := h_precond.2.1
        omega
    constructor
    · -- MinGoodApartments ≤ MaxGoodApartments
      unfold MinGoodApartments MaxGoodApartments
      split_ifs with h1 h2
      · norm_num
      · omega
      · omega
    constructor
    · -- MinGoodApartments ≤ n - k
      unfold MinGoodApartments
      split_ifs
      · omega
      · have : k ≤ n := h_precond.2.2
        omega
    · -- MaxGoodApartments ≤ n - k
      unfold MaxGoodApartments
      split_ifs with h1 h2
      · omega
      · simp
      · have : k ≤ n := h_precond.2.2
        omega
  constructor
  · simp  -- MinGoodApartments equality
  · simp  -- MaxGoodApartments equality
-- </vc-theorems>
