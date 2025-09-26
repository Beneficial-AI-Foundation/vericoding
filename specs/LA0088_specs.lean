-- <vc-preamble>
def ValidTimeFormat (time_str : String) : Prop :=
  time_str.length = 5 ∧
  time_str.data[2]! = ':' ∧
  '0' ≤ time_str.data[0]! ∧ time_str.data[0]! ≤ '9' ∧
  '0' ≤ time_str.data[1]! ∧ time_str.data[1]! ≤ '9' ∧
  '0' ≤ time_str.data[3]! ∧ time_str.data[3]! ≤ '9' ∧
  '0' ≤ time_str.data[4]! ∧ time_str.data[4]! ≤ '9' ∧
  ((time_str.data[0]!).toNat - '0'.toNat) * 10 + ((time_str.data[1]!).toNat - '0'.toNat) ≤ 23 ∧
  ((time_str.data[3]!).toNat - '0'.toNat) * 10 + ((time_str.data[4]!).toNat - '0'.toNat) ≤ 59

def FindFirstNewline (s : String) : Nat := 
  s.data.findIdx (· = '\n')

def FindSecondNewline (s : String) (first : Nat) : Nat := 
  let rest := s.data.drop (first + 1)
  first + 1 + rest.findIdx (· = '\n')

def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0 ∧
  ∃ i, 0 ≤ i ∧ i < stdin_input.length ∧ stdin_input.data[i]! = '\n' ∧
  ∃ i j, 0 ≤ i ∧ i < j ∧ j < stdin_input.length ∧ stdin_input.data[i]! = '\n' ∧ stdin_input.data[j]! = '\n' ∧
  let first_nl := FindFirstNewline stdin_input
  let second_nl := FindSecondNewline stdin_input first_nl
  let s := ⟨stdin_input.data.take first_nl⟩
  let t := ⟨stdin_input.data.drop (first_nl + 1) |>.take (second_nl - first_nl - 1)⟩
  ValidTimeFormat s ∧ ValidTimeFormat t

def ParseTime (time_str : String) : Int × Int :=
  let h := ((time_str.data[0]!).toNat - '0'.toNat) * 10 + ((time_str.data[1]!).toNat - '0'.toNat)
  let m := ((time_str.data[3]!).toNat - '0'.toNat) * 10 + ((time_str.data[4]!).toNat - '0'.toNat)
  (h, m)

def CalculateBedtime (wake_hour wake_min sleep_hour sleep_min : Int) : Int × Int :=
  let wake_total_min := wake_hour * 60 + wake_min
  let sleep_total_min := sleep_hour * 60 + sleep_min
  let bed_total_min := (wake_total_min - sleep_total_min + 24 * 60) % (24 * 60)
  (bed_total_min / 60, bed_total_min % 60)

def ValidOutput (result : String) : Prop :=
  result.length = 6 ∧
  result.data[(result.length - 1)]! = '\n' ∧
  result.data[2]! = ':' ∧
  '0' ≤ result.data[0]! ∧ result.data[0]! ≤ '9' ∧
  '0' ≤ result.data[1]! ∧ result.data[1]! ≤ '9' ∧
  '0' ≤ result.data[3]! ∧ result.data[3]! ≤ '9' ∧
  '0' ≤ result.data[4]! ∧ result.data[4]! ≤ '9' ∧
  ((result.data[0]!).toNat - '0'.toNat) * 10 + ((result.data[1]!).toNat - '0'.toNat) ≤ 23 ∧
  ((result.data[3]!).toNat - '0'.toNat) * 10 + ((result.data[4]!).toNat - '0'.toNat) ≤ 59

def CorrectBedtime (stdin_input result : String) : Prop :=
  let first_nl := FindFirstNewline stdin_input
  let second_nl := FindSecondNewline stdin_input first_nl
  let s := ⟨stdin_input.data.take first_nl⟩
  let t := ⟨stdin_input.data.drop (first_nl + 1) |>.take (second_nl - first_nl - 1)⟩
  let (wake_hour, wake_min) := ParseTime s
  let (sleep_hour, sleep_min) := ParseTime t
  let (bed_hour, bed_min) := CalculateBedtime wake_hour wake_min sleep_hour sleep_min
  let result_hour := ((result.data[0]!).toNat - '0'.toNat) * 10 + ((result.data[1]!).toNat - '0'.toNat)
  let result_min := ((result.data[3]!).toNat - '0'.toNat) * 10 + ((result.data[4]!).toNat - '0'.toNat)
  result_hour = bed_hour ∧ result_min = bed_min

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  ValidOutput result ∧ CorrectBedtime stdin_input result

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>