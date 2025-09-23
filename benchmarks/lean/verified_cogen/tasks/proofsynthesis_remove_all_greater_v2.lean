-- <vc-preamble>
@[reducible, simp]
def removeAllGreater_precond (v : Array Int) (e : Int) :=
  ∀ k1 k2, 0 ≤ k1 → k1 < k2 → k2 < v.size → v[k1]! ≠ v[k2]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeAllGreater (v : Array Int) (e : Int) (h_precond : removeAllGreater_precond v e) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def removeAllGreater_postcond (v : Array Int) (e : Int) (result: Array Int) (h_precond : removeAllGreater_precond v e) :=
  (∀ k, k < result.size → result[k]! ≤ e ∧ v.toList.contains result[k]!) ∧
  (∀ k, k < v.size → v[k]! ≤ e → result.toList.contains v[k]!)

theorem removeAllGreater_spec_satisfied (v: Array Int) (e: Int) (h_precond : removeAllGreater_precond v e) :
    removeAllGreater_postcond v e (removeAllGreater v e h_precond) h_precond := by
  sorry
-- </vc-theorems>