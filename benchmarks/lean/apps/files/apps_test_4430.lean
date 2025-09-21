-- <vc-preamble>
def GreedyPackFromEndHelper (a : List Int) (pos : Int) (boxes_left : Int) (capacity : Int) (current_box_space : Int) : Int :=
  if pos < 0 then 0
  else if pos ≥ a.length then 0
  else 
    let item := a[pos.toNat]!
    if item > capacity then 0
    else if item ≤ current_box_space then
      1 + GreedyPackFromEndHelper a (pos - 1) boxes_left capacity (current_box_space - item)
    else if boxes_left > 1 then
      1 + GreedyPackFromEndHelper a (pos - 1) (boxes_left - 1) capacity (capacity - item)
    else
      0
termination_by (max 0 (pos + 1)).toNat

def GreedyPackFromEnd (a : List Int) (boxes : Int) (capacity : Int) : Int :=
  GreedyPackFromEndHelper a (a.length - 1) boxes capacity capacity

@[reducible, simp]
def solve_precond (n m k : Int) (a : List Int) : Prop :=
  n ≥ 0 ∧ m ≥ 1 ∧ k ≥ 1 ∧ a.length = n.toNat ∧ ∀ i, 0 ≤ i ∧ i < a.length → 1 ≤ a[i]! ∧ a[i]! ≤ k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (a : List Int) (h_precond : solve_precond n m k a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (a : List Int) (result : Int) (h_precond : solve_precond n m k a) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = GreedyPackFromEnd a m k

theorem solve_spec_satisfied (n m k : Int) (a : List Int) (h_precond : solve_precond n m k a) :
    solve_postcond n m k a (solve n m k a h_precond) h_precond := by
  sorry
-- </vc-theorems>