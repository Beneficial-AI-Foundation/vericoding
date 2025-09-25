-- <vc-preamble>
@[reducible, simp]
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList
-- </vc-preamble>

-- <vc-helpers>
def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n
-- </vc-helpers>

-- <vc-definitions>
def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))

theorem CanyonSearch_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    CanyonSearch_postcond (a) (b) (CanyonSearch (a) (b) h_precond) h_precond := by
  sorry
-- </vc-theorems>