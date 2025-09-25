-- <vc-preamble>
def concat_seqs (seqs : List (List Char)) : List Char :=
  match seqs with
  | [] => []
  | s :: rest => s ++ concat_seqs rest

def ValidSplit (result : List (List Char)) (k : Int) (q : List Char) : Prop :=
  result.length = k ∧
  (∀ i, 0 ≤ i ∧ i < result.length → result[i]!.length > 0) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < result.length → result[i]![0]! ≠ result[j]![0]!) ∧
  concat_seqs result = q

@[reducible, simp]
def solve_precond (k : Int) (q : List Char) : Prop :=
  k ≥ 0 ∧ q.length ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k : Int) (q : List Char) (h_precond : solve_precond k q) : List (List Char) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k : Int) (q : List Char) (result : List (List Char)) (h_precond : solve_precond k q) : Prop :=
  (k ≤ 0 ∨ q.length = 0 → result.length = 0) ∧
  (k > 0 ∧ q.length > 0 → (result.length = 0 ∨ ValidSplit result k q))

theorem solve_spec_satisfied (k : Int) (q : List Char) (h_precond : solve_precond k q) :
    solve_postcond k q (solve k q h_precond) h_precond := by
  sorry
-- </vc-theorems>