-- <vc-preamble>
def prefixProduct (s : List Nat) (i : Nat) (mod : Nat) : Nat :=
  if i = 0 then 1
  else if i ≤ s.length ∧ mod > 0 then 
    if h : i - 1 < s.length then (s[i-1] * prefixProduct s (i-1) mod) % mod
    else 0
  else 0

def prefixProducts (s : List Nat) (mod : Nat) : List Nat :=
  if mod > 0 then (List.range s.length).map (fun i => prefixProduct s (i+1) mod)
  else []

def allDistinct {T : Type} [DecidableEq T] (s : List T) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → 
    if hi : i < s.length then
      if hj : j < s.length then s[i] ≠ s[j]
      else True
    else True

def noForbiddenProducts (s : List Nat) (forbidden : List Nat) (mod : Nat) : Prop :=
  if mod > 0 then
    let products := prefixProducts s mod
    ∀ i, 0 ≤ i ∧ i < products.length → 
      if h : i < products.length then products[i] ∉ forbidden
      else True
  else True

def ValidInput (n : Nat) (m : Nat) (forbidden : List Nat) : Prop :=
  m ≥ 1 ∧
  n ≥ 0 ∧
  forbidden.length = n ∧
  (∀ i, 0 ≤ i ∧ i < forbidden.length → 
    if h : i < forbidden.length then 0 ≤ forbidden[i] ∧ forbidden[i] < m
    else True) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < forbidden.length → 
    if hi : i < forbidden.length then
      if hj : j < forbidden.length then forbidden[i] ≠ forbidden[j]
      else True
    else True)

def ValidSequence (sequence : List Nat) (m : Nat) (forbidden : List Nat) : Prop :=
  if m > 0 then
    (∀ i, 0 ≤ i ∧ i < sequence.length → 
      if h : i < sequence.length then 0 ≤ sequence[i] ∧ sequence[i] < m
      else True) ∧
    allDistinct ([1] ++ prefixProducts sequence m) ∧
    noForbiddenProducts sequence forbidden m
  else True

@[reducible, simp]
def solve_precond (n : Nat) (m : Nat) (forbidden : List Nat) : Prop :=
  ValidInput n m forbidden
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (m : Nat) (forbidden : List Nat) (h_precond : solve_precond n m forbidden) : Nat × List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (m : Nat) (forbidden : List Nat) (result : Nat × List Nat) (h_precond : solve_precond n m forbidden) : Prop :=
  let length := result.1
  let sequence := result.2
  length = sequence.length ∧
  length ≥ 0 ∧
  (m = 1 → length = 0 ∧ sequence = []) ∧
  (m > 1 → ValidSequence sequence m forbidden) ∧
  (n = 0 ∧ m > 1 → length > 0)

theorem solve_spec_satisfied (n : Nat) (m : Nat) (forbidden : List Nat) (h_precond : solve_precond n m forbidden) :
    solve_postcond n m forbidden (solve n m forbidden h_precond) h_precond := by
  sorry
-- </vc-theorems>