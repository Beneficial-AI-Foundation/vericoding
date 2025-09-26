-- <vc-preamble>
def SplitScore (A : List Int) (splitPos : Int) (p : Int) : Int :=
  let leftPart := A.take splitPos.toNat
  let rightPart := A.drop splitPos.toNat
  let leftSum := leftPart.sum
  let rightSum := rightPart.sum
  (leftSum % p) + (rightSum % p)

def MaxSeq (scores : List Int) : Int :=
  scores.foldl max 0

@[reducible, simp]
def ValidInput (N : Int) (p : Int) (A : List Int) : Prop :=
  N ≥ 2 ∧ p ≥ 2 ∧ A.length = N.toNat ∧ ∀ i, 0 ≤ i ∧ i < N → A[i.toNat]! ≥ 1

def MaxSplitScore (A : List Int) (p : Int) : Int :=
  let scores := (List.range (A.length - 1)).map (fun i => SplitScore A (Int.ofNat (i + 1)) p)
  MaxSeq scores

@[reducible, simp]
def solve_precond (N : Int) (p : Int) (A : List Int) : Prop :=
  ValidInput N p A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (p : Int) (A : List Int) (h_precond : solve_precond N p A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (p : Int) (A : List Int) (result : Int) (h_precond : solve_precond N p A) : Prop :=
  result ≥ 0 ∧ result < 2 * p ∧ result = MaxSplitScore A p

theorem solve_spec_satisfied (N : Int) (p : Int) (A : List Int) (h_precond : solve_precond N p A) :
    solve_postcond N p A (solve N p A h_precond) h_precond := by
  sorry
-- </vc-theorems>