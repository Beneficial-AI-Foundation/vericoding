-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = n ∧ ∀ i, 0 ≤ i ∧ i < a.length → a[i]! ≥ 1

def Transform (a : List Int) : List Int :=
  List.range a.length |>.mapIdx (fun i _ => a[i]! - (i + 1))

def Abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

def SumAbsDiffs (a : List Int) (target : Int) : Int :=
  match a with
  | [] => 0
  | h :: t => Abs (h - target) + SumAbsDiffs t target

def SortedSeq (a : List Int) : List Int :=
  a.mergeSort (· ≤ ·)

def RoundToInt (x : Int) (y : Int) : Int :=
  if y = 0 then 0
  else if x ≥ 0 then (x + y / 2) / y
  else (x - y / 2) / y

def MedianOf (a : List Int) : Int :=
  let sorted := SortedSeq a
  if sorted.length = 0 then 0
  else if sorted.length % 2 = 1 then
    sorted[sorted.length / 2]!
  else if sorted.length = 2 then
    RoundToInt (sorted[0]! + sorted[1]!) 2
  else
    RoundToInt (sorted[sorted.length / 2 - 1]! + sorted[sorted.length / 2]!) 2

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
  result ≥ 0 ∧ result = SumAbsDiffs (Transform a) (MedianOf (Transform a))

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>