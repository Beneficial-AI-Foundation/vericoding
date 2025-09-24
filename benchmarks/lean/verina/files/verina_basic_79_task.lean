-- <vc-preamble>
@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  a.size > 0 ∧ x < a.size
-- </vc-preamble>

-- <vc-helpers>
def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1
-- </vc-helpers>

-- <vc-definitions>
def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)

theorem onlineMax_spec_satisfied (a: Array Int) (x: Nat) (h_precond : onlineMax_precond (a) (x)) :
    onlineMax_postcond (a) (x) (onlineMax (a) (x) h_precond) h_precond := by
  sorry
-- </vc-theorems>