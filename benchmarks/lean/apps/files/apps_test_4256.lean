-- <vc-preamble>
partial def IsValidInteger (s : String) : Bool :=
  s.length > 0 && (s.toList.all fun c => '0' ≤ c && c ≤ '9')

partial def StringToIntSpec (s : String) : Int :=
  if s.length = 1 then 
    s.data.head!.toNat - '0'.toNat
  else 
    StringToIntSpec (s.dropRight 1) * 10 + (s.data.getLast!.toNat - '0'.toNat)

partial def SplitHelper (s : String) (index : Nat) (current : String) : List String :=
  if index ≥ s.length then
    if current.length > 0 then [current] else []
  else 
    let c := s.data[index]!
    if c = ' ' ∨ c = '\n' ∨ c = '\t' then
      if current.length > 0 then [current] ++ SplitHelper s (index + 1) ""
      else SplitHelper s (index + 1) ""
    else
      SplitHelper s (index + 1) (current ++ c.toString)

partial def SplitStringSpec (s : String) : List String :=
  if s.length = 0 then []
  else SplitHelper s 0 ""

partial def IntToStringSpec (n : Int) : String :=
  if n = 0 then "0"
  else if n < 10 then (Char.ofNat ('0'.toNat + n.toNat)).toString
  else IntToStringSpec (n / 10) ++ (Char.ofNat ('0'.toNat + (n % 10).toNat)).toString

def ComputeDrinks (A B C : Int) : Int :=
  if B / A < C then B / A else C

def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < input.length ∧ 
  input.data[i]! = ' ' ∧ input.data[j]! = ' ' ∧
  (let parts := SplitStringSpec input
   parts.length ≥ 3 ∧ 
   IsValidInteger (parts[0]!) ∧ IsValidInteger (parts[1]!) ∧ IsValidInteger (parts[2]!) ∧
   let A := StringToIntSpec (parts[0]!)
   let B := StringToIntSpec (parts[1]!)  
   let C := StringToIntSpec (parts[2]!)
   1 ≤ A ∧ A ≤ 100 ∧ 1 ≤ B ∧ B ≤ 100 ∧ 1 ≤ C ∧ C ≤ 100)

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  result.length > 0 ∧
  result.data.getLast! = '\n' ∧
  (let parts := SplitStringSpec input
   let A := StringToIntSpec (parts[0]!)
   let B := StringToIntSpec (parts[1]!)
   let C := StringToIntSpec (parts[2]!)
   let drinks := ComputeDrinks A B C
   result = IntToStringSpec drinks ++ "\n")

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>