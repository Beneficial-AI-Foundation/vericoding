import Mathlib
-- <vc-preamble>
def sum_seq : List Int → Int
  | [] => 0
  | h :: t => h + sum_seq t

def min_seq : List Int → Int
  | [x] => x
  | h :: t => min h (min_seq t)
  | [] => 0

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  a.length ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER Helper functions for counting and filtering
def count_negatives (a : List Int) : Nat :=
  (a.filter (fun x => x < 0)).length

-- LLM HELPER Helper to create absolute value list
def abs_list (a : List Int) : List Int :=
  a.map (fun x => if x < 0 then -x else x)

-- LLM HELPER Helper to check if a number is even
def is_even (n : Nat) : Bool :=
  n % 2 = 0

-- LLM HELPER Helper theorem about count_negatives and abs_list
theorem count_negatives_eq_length_filter (a : List Int) :
    count_negatives a = (a.filter (fun x => x < 0)).length := by
  rfl

-- LLM HELPER Helper theorem about abs_list
theorem abs_list_map (a : List Int) :
    abs_list a = a.map (fun x => if x < 0 then -x else x) := by
  rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  let count_neg := count_negatives a
  let abs_vals := abs_list a
  let sum_abs := sum_seq abs_vals
  let min_abs := min_seq abs_vals
  if is_even count_neg then sum_abs else sum_abs - 2 * min_abs
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : Int) (h_precond : solve_precond a) : Prop :=
  let count_neg := (a.filter (fun x => x < 0)).length
  let abs_list := a.map (fun x => if x < 0 then -x else x)
  let sum_abs := sum_seq abs_list
  let min_abs := min_seq abs_list
  result = if count_neg % 2 = 0 then sum_abs else sum_abs - 2 * min_abs

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  unfold solve_postcond solve
  unfold count_negatives abs_list is_even
  simp only [count_negatives_eq_length_filter, abs_list_map]
  split_ifs <;> simp_all
-- </vc-theorems>
