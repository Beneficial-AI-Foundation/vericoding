-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧
  a.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → 1 ≤ a[i.natAbs]! ∧ a[i.natAbs]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → a[i.natAbs]! ≠ a[j.natAbs]!)

def ValidOutput (n : Int) (result : Int) : Prop :=
  0 ≤ result ∧ result ≤ n

def ReversedArray (a : List Int) : List Int :=
  List.range a.length |>.map (fun i => a[a.length - 1 - i]!)

def HasIncreasingPair (ar : List Int) : Bool :=
  if ar.length ≤ 1 then false
  else List.range (ar.length - 1) |>.any (fun i => ar[i + 1]! > ar[i]!)

def MinIndex (ar : List Int) (n : Int) : Int :=
  0

def CorrectResult (n : Int) (a : List Int) : Int :=
  let ar := ReversedArray a
  if HasIncreasingPair ar then
    let min_i := MinIndex ar n
    n - min_i
  else
    0

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
  ValidOutput n result ∧ result = CorrectResult n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>