-- <vc-preamble>
def SumList (s : List Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => x + SumList xs

def ValidInput (digits : List Int) : Prop :=
  digits.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < digits.length → 0 ≤ digits[i]! ∧ digits[i]! ≤ 9

def IsGoodSubarray (digits : List Int) (start : Int) (end_pos : Int) : Prop :=
  0 ≤ start ∧ start ≤ end_pos ∧ end_pos < digits.length ∧
  let subarray_sum := SumList (digits.drop start.natAbs |>.take (end_pos - start + 1).natAbs)
  let subarray_length := end_pos - start + 1
  subarray_sum = subarray_length

partial def CountGoodSubarraysHelper (digits : List Int) (pos : Int) (freq_map : Int → Int) 
                            (current_sum : Int) (current_count : Int) : Int :=
  if pos ≥ digits.length then 0
  else
    let new_sum := current_sum + digits[pos.natAbs]!
    let new_count := current_count + 1
    let diff := new_count - new_sum
    let contribution := freq_map diff
    let new_freq_map := fun k => if k = diff then freq_map k + 1 else freq_map k
    contribution + CountGoodSubarraysHelper digits (pos + 1) new_freq_map new_sum new_count

def CountGoodSubarrays (digits : List Int) : Int :=
  CountGoodSubarraysHelper digits 0 (fun k => if k = 0 then 1 else 0) 0 0

@[reducible, simp]
def solve_precond (digits : List Int) : Prop :=
  ValidInput digits
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (digits : List Int) (h_precond : solve_precond digits) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (digits : List Int) (count : Int) (h_precond : solve_precond digits) : Prop :=
  count ≥ 0 ∧ count = CountGoodSubarrays digits

theorem solve_spec_satisfied (digits : List Int) (h_precond : solve_precond digits) :
    solve_postcond digits (solve digits h_precond) h_precond := by
  sorry
-- </vc-theorems>