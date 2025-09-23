-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 2 ∧ a.length = n.natAbs ∧ (∀ i, 0 ≤ i ∧ i < n → a.get! i.natAbs ≥ 0)

def ComputeB (a : List Int) (i : Int) : Int :=
  a.get! i.natAbs - i

def ComputeC (n : Int) (b : Int) : Int :=
  if b < 0 then b / n else (b + n - 1) / n

def ComputeCC (n : Int) (a : List Int) (i : Int) : Int :=
  let b := ComputeB a i
  let c := ComputeC n b
  n * c

def IsOptimalEntrance (n : Int) (a : List Int) (entrance : Int) : Prop :=
  let i := entrance - 1
  ∀ j, 0 ≤ j ∧ j < n →
    let cci := ComputeCC n a i
    let ccj := ComputeCC n a j
    cci ≤ ccj ∧ (cci < ccj ∨ i ≤ j)

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  1 ≤ result ∧ result ≤ n ∧ IsOptimalEntrance n a result

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>