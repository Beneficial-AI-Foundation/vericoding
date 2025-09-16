-- <vc-preamble>
def ValidInput (n : Nat) (arr : List Int) : Prop :=
  n > 0 ∧ arr.length = n ∧ ∀ i, 0 ≤ i ∧ i < arr.length → arr[i]! ≥ 1

def ComputeIncreasingEnd (arr : List Int) (start : Nat) (lastVal : Int) : Nat :=
  sorry

def ComputeConstantEnd (arr : List Int) (start : Nat) (val : Int) : Nat :=
  sorry

def ComputeDecreasingEnd (arr : List Int) (start : Nat) (lastVal : Int) : Nat :=
  sorry

def ComputePhases (arr : List Int) : (Nat × Nat × Nat) :=
  let incEnd := ComputeIncreasingEnd arr 0 0
  let constEnd := ComputeConstantEnd arr incEnd (if incEnd > 0 then arr[incEnd-1]! else 0)
  let decEnd := ComputeDecreasingEnd arr constEnd (if constEnd > incEnd then arr[incEnd]! else if incEnd > 0 then arr[incEnd-1]! else 0)
  (incEnd, constEnd, decEnd)

def IsUnimodal (arr : List Int) : Prop :=
  (∀ i, 0 ≤ i ∧ i < arr.length → arr[i]! ≥ 1) →
  if arr.length ≤ 1 then true
  else
    let phases := ComputePhases arr
    let (incEnd, constEnd, decEnd) := phases
    incEnd ≤ constEnd ∧ constEnd ≤ decEnd ∧ decEnd = arr.length ∧
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < incEnd → arr[i]! < arr[j]!) ∧
    (∀ i, incEnd ≤ i ∧ i < constEnd → arr[i]! = (if incEnd > 0 then arr[incEnd]! else arr[0]!)) ∧
    (∀ i j, constEnd ≤ i ∧ i < j ∧ j < decEnd → arr[i]! > arr[j]!) ∧
    (incEnd > 0 ∧ constEnd < arr.length → arr[incEnd-1]! ≥ (if constEnd > incEnd then arr[incEnd]! else arr[constEnd]!))

@[reducible, simp]
def solve_precond (n : Nat) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (arr : List Int) (h_precond : solve_precond n arr) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (arr : List Int) (result : String) (h_precond : solve_precond n arr) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ IsUnimodal arr)

theorem solve_spec_satisfied (n : Nat) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  sorry
-- </vc-theorems>
