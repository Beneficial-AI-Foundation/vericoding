-- <vc-preamble>
-- <vc-preamble>
def SplitLinesFunc (_ : String) : List String :=
  []

def SplitSpacesFunc (_ : String) : List String :=
  []

def IsValidPositiveInt (s : String) : Prop :=
  s.length ≥ 1 ∧ (∀ i, 0 ≤ i ∧ i < s.length → '0' ≤ s.get (String.Pos.mk i) ∧ s.get (String.Pos.mk i) ≤ '9')

def ParseIntFunc (s : String) (h : IsValidPositiveInt s := by sorry) : Int :=
  0

def ValidCompanyLine (line : String) : Prop :=
  let parts := SplitSpacesFunc line
  parts.length ≥ 1 ∧ IsValidPositiveInt (parts[0]!) ∧
  let m := ParseIntFunc (parts[0]!)
  m ≥ 1 ∧ parts.length = Int.natAbs m + 1 ∧
  (∀ j, 1 ≤ j ∧ j ≤ m → IsValidPositiveInt (parts[Int.natAbs j]!))

def ValidCompanyInput (input : String) : Prop :=
  let lines := SplitLinesFunc input
  lines.length ≥ 1 ∧ 
  IsValidPositiveInt (lines[0]!) ∧
  let n := ParseIntFunc (lines[0]!)
  n ≥ 1 ∧ lines.length ≥ Int.natAbs n + 1 ∧
  (∀ i, 1 ≤ i ∧ i ≤ n → ValidCompanyLine (lines[Int.natAbs i]!))

def MaxInSeq (s : List Int) (_ : s.length > 0) : Int :=
  match s with
  | [x] => x
  | x :: xs => if h_nonempty : xs.length > 0 then
      max x (MaxInSeq xs h_nonempty)
    else x

def MaxInSeqFunc (s : List Int) (_ : s.length > 0 := by sorry) : Int :=
  MaxInSeq s (by sorry)

def MaxInSeqOfSeq (s : List Int) (_ : s.length > 0 := by sorry) : Int :=
  match s with
  | [x] => x
  | x :: xs => if h_nonempty : xs.length > 0 then
      max x (MaxInSeqOfSeq xs h_nonempty)
    else x

def ParseCompanies (input : String) (_ : ValidCompanyInput input) : List (List Int) :=
  let lines := SplitLinesFunc input
  let n := ParseIntFunc (lines[0]!)
  List.range (Int.natAbs n) |>.map (fun i =>
    let parts := SplitSpacesFunc (lines[i + 1]!)
    let m := ParseIntFunc (parts[0]!)
    List.range (Int.natAbs m) |>.map (fun j => ParseIntFunc (parts[j + 1]!)))

def GlobalMaxSalary (companies : List (List Int)) 
  (_ : companies.length ≥ 1) (_ : ∀ i, 0 ≤ i ∧ i < companies.length → (companies[i]!).length ≥ 1) : Int :=
  MaxInSeqOfSeq (List.range companies.length |>.map (fun i => MaxInSeqFunc (companies[i]!)))

def SumOverCompanies (companies : List (List Int)) (globalMax : Int) 
  (_ : companies.length ≥ 1) (_ : ∀ i, 0 ≤ i ∧ i < companies.length → (companies[i]!).length ≥ 1) : Int :=
  if companies.length = 1 then
    let companyMax := MaxInSeqFunc (companies[0]!)
    let increasePerEmployee := globalMax - companyMax
    increasePerEmployee * (companies[0]!).length
  else
    let companyMax := MaxInSeqFunc (companies[0]!)
    let increasePerEmployee := globalMax - companyMax
    have h_tail_len : companies.tail.length ≥ 1 := by
      unfold List.tail
      cases companies with
      | nil => contradiction
      | cons head tail => 
        cases tail with
        | nil => simp; sorry
        | cons _ _ => simp
    have h_tail_elem : ∀ i, 0 ≤ i ∧ i < companies.tail.length → (companies.tail[i]!).length ≥ 1 := by sorry
    increasePerEmployee * (companies[0]!).length + SumOverCompanies companies.tail globalMax h_tail_len h_tail_elem

def CalculateMinimumIncrease (companies : List (List Int)) 
  (h1 : companies.length ≥ 1) (h2 : ∀ i, 0 ≤ i ∧ i < companies.length → (companies[i]!).length ≥ 1) : Int :=
  let globalMax := GlobalMaxSalary companies h1 h2
  SumOverCompanies companies globalMax h1 h2

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  input.length > 0 ∧ ValidCompanyInput input
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : Int) (h_precond : solve_precond input) : Prop :=
  result ≥ 0 ∧ result = CalculateMinimumIncrease (ParseCompanies input (h_precond.2)) (by sorry) (by sorry)

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
