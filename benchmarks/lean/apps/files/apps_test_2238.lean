-- <vc-preamble>
def RepeatChar (c : Char) (n : Int) : String :=
  String.mk (List.replicate n.natAbs c)

def ValidInput (n : Int) : Prop :=
  n ≥ 3 ∧ n ≤ 101 ∧ n % 2 = 1

def ValidResult (result : List String) (n : Int) : Prop :=
  result.length = n.natAbs ∧
  ∀ i, 0 ≤ i ∧ i < result.length → (result[Int.natAbs i]!).length = n.natAbs

def CorrectDiamondPattern (result : List String) (n : Int) : Prop :=
  result.length = n.natAbs →
    let magic := (n - 1) / 2
    (∀ i, 0 ≤ i ∧ i ≤ magic ∧ i < result.length →
      let stars := magic - i
      let diamonds := n - 2 * stars
      result[Int.natAbs i]! = RepeatChar '*' stars ++ RepeatChar 'D' diamonds ++ RepeatChar '*' stars) ∧
    (∀ i, magic + 1 ≤ i ∧ i < n ∧ i < result.length →
      let u := i - magic
      let stars := u
      let diamonds := n - 2 * stars
      result[Int.natAbs i]! = RepeatChar '*' stars ++ RepeatChar 'D' diamonds ++ RepeatChar '*' stars)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List String) (h_precond : solve_precond n) : Prop :=
  ValidResult result n ∧ CorrectDiamondPattern result n

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>