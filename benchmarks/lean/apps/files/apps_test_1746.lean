-- <vc-preamble>
def hasChildren (node : Nat) (parents : List Int) (n : Nat) : Bool :=
  (List.range (n - 1)).any (fun i => parents[i]! - 1 = Int.ofNat node)

def countLeafChildren (node : Nat) (parents : List Int) (n : Nat) : Nat :=
  (List.range (n - 1)).filter (fun i => 
    parents[i]! - 1 = Int.ofNat node ∧ ¬hasChildren (i + 1) parents n) |>.length

def ValidInput (n : Nat) (parents : List Int) : Prop :=
  n ≥ 3 ∧ parents.length = n - 1 ∧ 
  (∀ i, 0 ≤ i ∧ i < n - 1 → 1 ≤ parents[i]! ∧ parents[i]! ≤ Int.ofNat (i + 1))

def IsSpruce (n : Nat) (parents : List Int) : Prop :=
  ∀ node, 0 ≤ node ∧ node < n ∧ hasChildren node parents n → 
      countLeafChildren node parents n ≥ 3

@[reducible, simp]
def solve_precond (n : Nat) (parents : List Int) : Prop :=
  ValidInput n parents
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (parents : List Int) (h_precond : solve_precond n parents) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (parents : List Int) (result : String) (h_precond : solve_precond n parents) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ 
  (result = "Yes" ↔ IsSpruce n parents)

theorem solve_spec_satisfied (n : Nat) (parents : List Int) (h_precond : solve_precond n parents) :
    solve_postcond n parents (solve n parents h_precond) h_precond := by
  sorry
-- </vc-theorems>