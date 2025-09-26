import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧
  a.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → 1 ≤ a[i.natAbs]! ∧ a[i.natAbs]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → a[i.natAbs]! ≠ a[j.natAbs]!)

def ValidOutput (n : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result ≤ n

def ReversedArray (a : List Int) : List Int :=
  List.range a.length |>.map (fun i => a[a.length - 1 - i]!)

def HasIncreasingPair (ar : List Int) : Bool :=
  if ar.length ≤ 1 then false
  else List.range (ar.length - 1) |>.any (fun i => ar[i + 1]! > ar[i]!)

def MinIndex (ar : List Int) (n : Int) : Int :=
  0

def CorrectResult (n : Int) (a : List Int) : Int :=
  let ar := ReversedArray a
  if HasIncreasingPair ar then
    let min_i := MinIndex ar n
    n - min_i
  else
    0

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemmas to help with bounds and properties
lemma MinIndex_nonneg (ar : List Int) (n : Int) : 0 ≤ MinIndex ar n := by
  unfold MinIndex
  norm_num

lemma MinIndex_le_n (ar : List Int) (n : Int) (h : n ≥ 1) : MinIndex ar n ≤ n := by
  unfold MinIndex
  linarith
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  let ar := ReversedArray a
  if HasIncreasingPair ar then
    let min_i := MinIndex ar n
    n - min_i
  else
    0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  ValidOutput n result ∧ result = CorrectResult n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve CorrectResult
  simp [ValidInput] at h_precond
  obtain ⟨h_pos, h_len, h_range, h_distinct⟩ := h_precond
  constructor
  · -- Show ValidOutput
    constructor
    · -- Show result ≥ 0
      by_cases h : HasIncreasingPair (ReversedArray a)
      · -- Case: has increasing pair
        simp [h]
        have h_min_nonneg : 0 ≤ MinIndex (ReversedArray a) n := MinIndex_nonneg _ _
        have h_min_le : MinIndex (ReversedArray a) n ≤ n := MinIndex_le_n _ _ h_pos
        linarith
      · -- Case: no increasing pair
        simp [h]
    · -- Show result ≤ n
      by_cases h : HasIncreasingPair (ReversedArray a) 
      · -- Case: has increasing pair
        simp [h]
        have h_min_nonneg : 0 ≤ MinIndex (ReversedArray a) n := MinIndex_nonneg _ _
        linarith
      · -- Case: no increasing pair
        simp [h]
        have h_n_nonneg : 0 ≤ n := by linarith [h_pos]
        exact h_n_nonneg
  · -- Show result = CorrectResult n a
    rfl
-- </vc-theorems>
