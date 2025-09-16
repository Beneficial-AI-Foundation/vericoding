-- <vc-preamble>
-- <vc-preamble>
def ValidInput (N p : Int) (A : List Int) : Prop :=
  N ≥ 2 ∧ p ≥ 2 ∧ A.length = N ∧ ∀ i, 0 ≤ i ∧ i < N → A[i.natAbs]! ≥ 1

def SplitScore (A : List Int) (split_pos : Int) (p : Int) : Int :=
  sorry

def MaxSeq (scores : List Int) : Int :=
  sorry

def MaxSplitScore (A : List Int) (p : Int) : Int :=
  let scores := (List.range (A.length - 1)).map (fun i => SplitScore A (Int.ofNat (i + 1)) p)
  MaxSeq scores

@[reducible, simp]
def solve_precond (N p : Int) (A : List Int) : Prop :=
  ValidInput N p A
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (N p : Int) (A : List Int) (h_precond : solve_precond N p A) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N p : Int) (A : List Int) (result : Int) (h_precond : solve_precond N p A) : Prop :=
  result ≥ 0 ∧ result < 2 * p ∧ result = MaxSplitScore A p

theorem solve_spec_satisfied (N p : Int) (A : List Int) (h_precond : solve_precond N p A) :
    solve_postcond N p A (solve N p A h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
