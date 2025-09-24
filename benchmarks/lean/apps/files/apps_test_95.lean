-- <vc-preamble>
def ValidInput (n : Nat) (arr : List Int) : Prop :=
  n > 0 ∧ arr.length = n ∧ ∀ i, 0 ≤ i ∧ i < arr.length → arr[i]! ≥ 1

def ComputeIncreasingEnd (arr : List Int) (start : Nat) : Nat :=
  if start ≥ arr.length then start
  else if start = 0 then
    if arr.length > 1 ∧ arr[0]! < arr[1]! then ComputeIncreasingEnd arr 1
    else 0
  else
    if start < arr.length - 1 ∧ arr[start]! < arr[start + 1]! then
      ComputeIncreasingEnd arr (start + 1)
    else start

def ComputeConstantEnd (arr : List Int) (incEnd : Nat) : Nat :=
  if incEnd ≥ arr.length then incEnd
  else if incEnd = 0 then
    if arr.length > 0 then
      let rec helper (pos : Nat) : Nat :=
        if pos ≥ arr.length then pos
        else if arr[pos]! = arr[0]! then helper (pos + 1)
        else pos
      helper 1
    else incEnd
  else
    let rec helper2 (pos : Nat) (targetVal : Int) : Nat :=
      if pos ≥ arr.length then pos
      else if arr[pos]! = targetVal then helper2 (pos + 1) targetVal
      else pos
    helper2 incEnd (if incEnd > 0 then arr[incEnd - 1]! else 0)

def ComputeDecreasingEnd (arr : List Int) (constEnd : Nat) : Nat :=
  if constEnd ≥ arr.length then constEnd
  else
    let rec helper (pos : Nat) : Nat :=
      if pos ≥ arr.length - 1 then arr.length
      else if arr[pos]! > arr[pos + 1]! then helper (pos + 1)
      else pos + 1
    helper constEnd

def ComputePhases (arr : List Int) : (Nat × Nat × Nat) :=
  let incEnd := ComputeIncreasingEnd arr 0
  let constEnd := ComputeConstantEnd arr incEnd
  let decEnd := ComputeDecreasingEnd arr constEnd
  (incEnd, constEnd, decEnd)

def IsUnimodal (arr : List Int) : Prop :=
  (∀ i, 0 ≤ i ∧ i < arr.length → arr[i]! ≥ 1) →
  if arr.length ≤ 1 then True
  else
    let phases := ComputePhases arr
    phases.1 ≤ phases.2.1 ∧ phases.2.1 ≤ phases.2.2 ∧ phases.2.2 = arr.length ∧
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < phases.1 → arr[i]! < arr[j]!) ∧
    (∀ i, phases.1 ≤ i ∧ i < phases.2.1 → arr[i]! = (if phases.1 > 0 then arr[phases.1]! else arr[0]!)) ∧
    (∀ i j, phases.2.1 ≤ i ∧ i < j ∧ j < phases.2.2 → arr[i]! > arr[j]!) ∧
    (phases.1 > 0 ∧ phases.2.1 < arr.length → arr[phases.1 - 1]! ≥ (if phases.2.1 > phases.1 then arr[phases.1]! else arr[phases.2.1]!))

@[reducible, simp]
def solve_precond (n : Nat) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (arr : List Int) (_ : solve_precond n arr) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (arr : List Int) (result : String) (_ : solve_precond n arr) : Prop :=
  (result = "YES" ∨ result = "NO") ∧ (result = "YES" ↔ IsUnimodal arr)

theorem solve_spec_satisfied (n : Nat) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  sorry
-- </vc-theorems>