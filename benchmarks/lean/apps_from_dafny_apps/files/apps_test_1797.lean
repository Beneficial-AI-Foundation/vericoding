-- <vc-preamble>
-- <vc-preamble>
def ValidInput (n : Int) (p : List Int) : Prop :=
  n > 0 ∧ p.length = n.natAbs ∧
  (∀ i, 0 ≤ i ∧ i < n → 1 ≤ p[i.natAbs]! ∧ p[i.natAbs]! ≤ n) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < n → p[i.natAbs]! ≠ p[j.natAbs]!)

def count_true (visited : List Bool) : Int :=
  match visited with
  | [] => 0
  | h :: t => (if h then 1 else 0) + count_true t

def sum_of_squares (s : List Int) : Int :=
  match s with
  | [] => 0
  | h :: t => h * h + sum_of_squares t

def find_unvisited (visited : List Bool) : Int :=
  sorry

def get_cycle_length (p : List Int) (visited : List Bool) (start : Int) : Int :=
  sorry

def mark_cycle_visited (p : List Int) (visited : List Bool) (start : Int) : List Bool :=
  sorry

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
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (n : Int) (p : List Int) (_ : solve_precond n p) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (p : List Int) (result : Int) (_ : solve_precond n p) : Prop :=
  result > 0

theorem solve_spec_satisfied (n : Int) (p : List Int) (h_precond : solve_precond n p) :
    solve_postcond n p (solve n p h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
