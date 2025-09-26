import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
noncomputable instance instCoePropBool : Coe Prop Bool where
  coe p := by
    classical
    exact decide p
-- </vc-helpers>

-- <vc-definitions>
def notEqual {n : Nat} (a b : Vector Int n) : Vector Bool n :=
Vector.ofFn (fun i => decide (a[i] ≠ b[i]))
-- </vc-definitions>

-- <vc-theorems>
theorem notEqual_spec {n : Nat} (a b : Vector Int n) :
  (notEqual a b).toList.length = n ∧
  ∀ i : Fin n, (notEqual a b)[i] = (a[i] ≠ b[i]) :=
by
  constructor
  · simpa using (notEqual a b).toList_length
  · intro i
    calc
      (notEqual a b)[i]
          = decide (a[i] ≠ b[i]) := by simp [notEqual]
      _   = (a[i] ≠ b[i]) := rfl
-- </vc-theorems>
