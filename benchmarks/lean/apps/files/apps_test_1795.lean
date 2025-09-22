-- <vc-preamble>
def ValidInput (n : Int) (f : List Int) : Prop :=
  n ≥ 2 ∧ n ≤ 5000 ∧
  f.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < f.length → 1 ≤ f.get! i ∧ f.get! i ≤ n ∧ f.get! i ≠ i + 1

def ZeroIndexedArray (n : Int) (f : List Int) (h : ValidInput n f) : List Int :=
  List.range n.natAbs |>.map (fun j => f.get! j - 1)

def HasLoveTriangleWith (n : Int) (a : List Int) : Prop :=
  a.length = n.natAbs ∧
  (∀ k, 0 ≤ k ∧ k < n.natAbs → 0 ≤ a.get! k ∧ a.get! k < n) ∧
  ∃ i, 0 ≤ i ∧ i < n.natAbs ∧ 
    0 ≤ a.get! i ∧ a.get! i < n ∧ 0 ≤ a.get! (a.get! i).natAbs ∧ a.get! (a.get! i).natAbs < n ∧ 
    a.get! (a.get! (a.get! i).natAbs).natAbs = i

def HasLoveTriangle (n : Int) (f : List Int) (h : ValidInput n f) : Prop :=
  let a := ZeroIndexedArray n f h
  HasLoveTriangleWith n a

@[reducible, simp]
def solve_precond (n : Int) (f : List Int) : Prop :=
  ValidInput n f
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (f : List Int) (h_precond : solve_precond n f) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (f : List Int) (result : String) (h_precond : solve_precond n f) : Prop :=
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" ↔ HasLoveTriangle n f h_precond)

theorem solve_spec_satisfied (n : Int) (f : List Int) (h_precond : solve_precond n f) :
    solve_postcond n f (solve n f h_precond) h_precond := by
  sorry
-- </vc-theorems>