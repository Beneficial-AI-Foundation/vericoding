-- <vc-preamble>
def ValidGraph (n : Int) (f : List Int) (w : List Int) : Prop :=
  n > 0 ∧ f.length = n ∧ w.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n → 0 ≤ f[i.toNat]! ∧ f[i.toNat]! < n) ∧
  (∀ i, 0 ≤ i ∧ i < n → w[i.toNat]! ≥ 0)

def ValidResult (n : Int) (sums : List Int) (mins : List Int) : Prop :=
  sums.length = n ∧ mins.length = n ∧
  ∀ i, 0 ≤ i ∧ i < n → sums[i.toNat]! ≥ 0 ∧ mins[i.toNat]! ≥ 0

def PathSum (start : Int) (k : Int) (f : List Int) (w : List Int) : Int :=
  if k ≤ 0 then 0
  else w[start.toNat]! + PathSum f[start.toNat]! (k - 1) f w
termination_by k.natAbs

def PathMin (start : Int) (k : Int) (f : List Int) (w : List Int) : Int :=
  if k ≤ 1 then w[start.toNat]!
  else
    let nextMin := PathMin f[start.toNat]! (k - 1) f w
    if w[start.toNat]! ≤ nextMin then w[start.toNat]! else nextMin
termination_by k.natAbs

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (f : List Int) (w : List Int) : Prop :=
  ValidGraph n f w ∧ k > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (f : List Int) (w : List Int) (h_precond : solve_precond n k f w) : List Int × List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (f : List Int) (w : List Int) (result : List Int × List Int) (h_precond : solve_precond n k f w) : Prop :=
  ValidResult n result.1 result.2

theorem solve_spec_satisfied (n : Int) (k : Int) (f : List Int) (w : List Int) (h_precond : solve_precond n k f w) :
    solve_postcond n k f w (solve n k f w h_precond) h_precond := by
  sorry
-- </vc-theorems>