-- <vc-preamble>
def CanReachNodeOne (target : Int) (edges : List (Int × Int)) (maxDepth : Nat) : Prop :=
  if maxDepth = 0 then False
  else if target = 1 then True
  else 
      ∃ i, 0 ≤ i ∧ i < edges.length ∧ 
          ((edges[i]!.1 = target ∧ CanReachNodeOne edges[i]!.2 edges (maxDepth - 1)) ∨
           (edges[i]!.2 = target ∧ CanReachNodeOne edges[i]!.1 edges (maxDepth - 1)))

def IsConnectedGraph (n : Int) (edges : List (Int × Int)) : Prop :=
  n > 1 →
  (∀ node, 2 ≤ node ∧ node ≤ n → 
      CanReachNodeOne node edges n.natAbs)

def IsConnectedTree (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 1 ∧ edges.length = n - 1 ∧
  (n = 1 → edges.length = 0) ∧
  (n > 1 → IsConnectedGraph n edges)

def ValidTreeInput (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 1 ∧
  edges.length = n - 1 ∧
  (∀ i, 0 ≤ i ∧ i < edges.length → 1 ≤ edges[i]!.1 ∧ edges[i]!.1 ≤ n ∧ 1 ≤ edges[i]!.2 ∧ edges[i]!.2 ≤ n) ∧
  (∀ i, 0 ≤ i ∧ i < edges.length → edges[i]!.1 ≠ edges[i]!.2) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < edges.length → 
      ¬(edges[i]!.1 = edges[j]!.1 ∧ edges[i]!.2 = edges[j]!.2) ∧ 
      ¬(edges[i]!.1 = edges[j]!.2 ∧ edges[i]!.2 = edges[j]!.1)) ∧
  (n = 1 → edges.length = 0) ∧
  (n > 1 → (∀ node, 1 ≤ node ∧ node ≤ n → 
      (∃ i, 0 ≤ i ∧ i < edges.length ∧ (edges[i]!.1 = node ∨ edges[i]!.2 = node)))) ∧
  IsConnectedTree n edges

@[reducible, simp]
def solve_precond (n : Int) (edges : List (Int × Int)) : Prop :=
  ValidTreeInput n edges
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (edges : List (Int × Int)) (_ : solve_precond n edges) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (edges : List (Int × Int)) (result : Int) (h_precond : solve_precond n edges) : Prop :=
  result ≥ 0 ∧
  (∃ blue red, blue ≥ 0 ∧ red ≥ 0 ∧ blue + red = n ∧ result = blue * red - (n - 1)) ∧
  (n = 1 → result = 0) ∧
  (n = 2 → result = 0) ∧
  (n > 2 → (∃ blue red, blue > 0 ∧ red > 0 ∧ blue + red = n ∧ result = blue * red - (n - 1))) ∧
  result ≤ (n * n) / 4 - (n - 1) + (if n % 2 = 0 then 0 else 1)

theorem solve_spec_satisfied (n : Int) (edges : List (Int × Int)) (h_precond : solve_precond n edges) :
    solve_postcond n edges (solve n edges h_precond) h_precond := by
  sorry
-- </vc-theorems>