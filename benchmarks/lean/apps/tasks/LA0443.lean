-- <vc-preamble>
def UnnecessaryCardsCountHelper (sorted : List Int) (k : Int) (temp : Int) (ans : Int) (i : Nat) : Int :=
  if i ≥ sorted.length then ans
  else
    let x := sorted[i]!
    if temp + x < k then
      UnnecessaryCardsCountHelper sorted k (temp + x) (ans + 1) (i + 1)
    else
      UnnecessaryCardsCountHelper sorted k 0 0 (i + 1)
termination_by sorted.length - i

def UnnecessaryCardsCount (sorted : List Int) (k : Int) : Int :=
  if sorted.length = 0 then 0
  else UnnecessaryCardsCountHelper sorted k 0 0 0

@[reducible, simp]
def solve_precond (n k : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ a.length = n ∧ (∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 1)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (a : List Int) (h_precond : solve_precond n k a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (a : List Int) (result : Int) (h_precond : solve_precond n k a) : Prop :=
  result ≥ 0 ∧ result ≤ n ∧ 
  ∃ sorted, sorted.length = a.length ∧
  (∀ x, x ∈ sorted ↔ x ∈ a) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < sorted.length → sorted[i]! ≥ sorted[j]!) ∧
  (∀ i, 0 ≤ i ∧ i < sorted.length → sorted[i]! ≥ 1) ∧
  result = UnnecessaryCardsCount sorted k

theorem solve_spec_satisfied (n k : Int) (a : List Int) (h_precond : solve_precond n k a) :
    solve_postcond n k a (solve n k a h_precond) h_precond := by
  sorry
-- </vc-theorems>