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
-- no helper code needed
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  let count_neg := (a.filter (fun x => x < 0)).length
let abs_list := a.map (fun x => if x < 0 then -x else x)
let sum_abs := sum_seq abs_list
let min_abs := min_seq abs_list
if count_neg % 2 = 0 then sum_abs else sum_abs - 2 * min_abs
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
  simpa [solve_postcond, solve]
-- </vc-theorems>
