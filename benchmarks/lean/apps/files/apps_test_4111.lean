-- <vc-preamble>
def ValidInput (n : Int) (arr : List Int) : Prop :=
  n ≥ 1 ∧ arr.length = n ∧ ∀ i, 0 ≤ i ∧ i < n → arr[i.toNat]! ≥ 1

def sum_even_indices (arr : List Int) (start : Nat) : Int :=
  if start ≥ arr.length then 0
  else
    let contribution := if start % 2 = 0 then arr[start]! else 0
    contribution + sum_even_indices arr (start + 1)

def sum_odd_indices (arr : List Int) (start : Nat) : Int :=
  if start ≥ arr.length then 0
  else
    let contribution := if start % 2 = 1 then arr[start]! else 0
    contribution + sum_odd_indices arr (start + 1)

def count_helper (arr : List Int) (i : Nat) (count1 : Int) (count2 : Int) (temp1 : Int) (temp2 : Int) : Int :=
  if i ≥ arr.length then 0
  else
    let contribution := 
      if i % 2 = 0 then
        let val1 := temp1 + count2 - temp2
        let val2 := temp2 + count1 - temp1 - arr[i]!
        if val1 = val2 then 1 else 0
      else
        let val1 := temp1 + count2 - temp2 - arr[i]!
        let val2 := temp2 + count1 - temp1
        if val1 = val2 then 1 else 0
    let new_temp1 := if i % 2 = 0 then temp1 + arr[i]! else temp1
    let new_temp2 := if i % 2 = 1 then temp2 + arr[i]! else temp2
    contribution + count_helper arr (i + 1) count1 count2 new_temp1 new_temp2

def count_balanced_removals (arr : List Int) : Int :=
  let n := arr.length
  if n = 0 then 0 else
  count_helper arr 0 (sum_even_indices arr 0) (sum_odd_indices arr 0) 0 0

@[reducible, simp]
def solve_precond (n : Int) (arr : List Int) : Prop :=
  ValidInput n arr
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (arr : List Int) (h_precond : solve_precond n arr) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (arr : List Int) (result : Int) (h_precond : solve_precond n arr) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = count_balanced_removals arr

theorem solve_spec_satisfied (n : Int) (arr : List Int) (h_precond : solve_precond n arr) :
    solve_postcond n arr (solve n arr h_precond) h_precond := by
  sorry
-- </vc-theorems>