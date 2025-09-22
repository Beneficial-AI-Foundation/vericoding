-- <vc-preamble>
def ValidInput (n : Int) (aa : List Int) : Prop :=
  n ≥ 2 ∧
  aa.length = (n - 1).natAbs ∧
  ∀ i, 0 ≤ i ∧ i < aa.length → 1 ≤ aa[i]! ∧ aa[i]! < i + 2

def SubordinateCount (aa : List Int) (boss_id : Int) : Int :=
  (List.range aa.length).filter (fun j => aa[j]! = boss_id) |>.length

def ValidOutput (n : Int) (aa : List Int) (result : List Int) : Prop :=
  result.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → result[i.natAbs]! ≥ 0) ∧
  (∀ i, 0 ≤ i ∧ i < n → result[i.natAbs]! = SubordinateCount aa (i + 1))

@[reducible, simp]
def solve_precond (n : Int) (aa : List Int) : Prop :=
  ValidInput n aa
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (aa : List Int) (h_precond : solve_precond n aa) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (aa : List Int) (result : List Int) (h_precond : solve_precond n aa) : Prop :=
  ValidOutput n aa result

theorem solve_spec_satisfied (n : Int) (aa : List Int) (h_precond : solve_precond n aa) :
    solve_postcond n aa (solve n aa h_precond) h_precond := by
  sorry
-- </vc-theorems>