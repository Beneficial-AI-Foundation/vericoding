import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (p : List Int) : Prop :=
  n > 0 ∧ p.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → 1 ≤ p[i.natAbs]! ∧ p[i.natAbs]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → p[i.natAbs]! ≠ p[j.natAbs]!)

def count_true (visited : List Bool) : Int :=
  visited.foldl (fun acc b => acc + if b then 1 else 0) 0

def sum_of_squares (s : List Int) : Int :=
  s.foldl (fun acc x => acc + x * x) 0

def find_unvisited (visited : List Bool) : Int :=
  match visited.findIdx? (· = false) with
  | some idx => idx
  | none => -1

def get_cycle_length (_ : List Int) (_ : List Bool) (_ : Int) : Int := 1

def mark_cycle_visited (_ : List Int) (visited : List Bool) (_ : Int) : List Bool := 
  visited

partial def get_cycles_helper (n : Int) (p : List Int) (visited : List Bool) (cycles : List Int) : List Int :=
  if count_true visited ≥ n then cycles
  else
    let unvisited := find_unvisited visited
    if unvisited = -1 then cycles
    else if 0 ≤ unvisited ∧ unvisited < n then
      let cycle_length := get_cycle_length p visited unvisited
      let new_visited := mark_cycle_visited p visited unvisited
      if count_true new_visited > count_true visited ∧ count_true new_visited ≤ n then
        get_cycles_helper n p new_visited (cycles ++ [cycle_length])
      else
        cycles ++ [cycle_length]
    else
      cycles

def get_cycle_lengths (n : Int) (p : List Int) : List Int :=
  get_cycles_helper n p (List.replicate n.natAbs false) []

@[reducible, simp]
def solve_precond (n : Int) (p : List Int) : Prop :=
  ValidInput n p
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma int_one_gt_zero : (1 : Int) > 0 := by
  simpa [gt_iff_lt] using (zero_lt_one : (0 : Int) < 1)

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (p : List Int) (h_precond : solve_precond n p) : Int :=
  1
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (p : List Int) (result : Int) (h_precond : solve_precond n p) : Prop :=
  result > 0

theorem solve_spec_satisfied (n : Int) (p : List Int) (h_precond : solve_precond n p) :
    solve_postcond n p (solve n p h_precond) h_precond := by
    simpa [solve_postcond, solve] using (int_one_gt_zero)
-- </vc-theorems>
