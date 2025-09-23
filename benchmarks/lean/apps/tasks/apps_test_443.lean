-- <vc-preamble>
def ValidInput (n : Int) (packets : List Int) : Prop :=
  n ≥ 1 ∧ packets.length = n ∧ ∀ i, 0 ≤ i ∧ i < packets.length → packets[i]! ≥ 1

def IsPossible (n : Int) (packets : List Int) : Prop :=
  n ≥ 2 ∧ (n > 2 ∨ packets[0]! ≠ packets[1]!)

def SumPackets (packets : List Int) : Int :=
  packets.sum

def ValidSolution (n : Int) (packets : List Int) (result : List Int) : Prop :=
  (¬IsPossible n packets → result.length = 0) ∧
  (IsPossible n packets → 
    result.length = 2 ∧ result[0]! = 1 ∧ 1 ≤ result[1]! ∧ result[1]! ≤ n ∧
    ∃ minIndex, 0 ≤ minIndex ∧ minIndex < packets.length ∧ 
    result[1]! = minIndex + 1 ∧
    (∀ j, 0 ≤ j ∧ j < packets.length → packets[minIndex]! ≤ packets[j]!) ∧
    (∀ k, 0 ≤ k ∧ k < minIndex → packets[k]! > packets[minIndex]!))

@[reducible, simp]
def solve_precond (n : Int) (packets : List Int) : Prop :=
  ValidInput n packets
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (packets : List Int) (h_precond : solve_precond n packets) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (packets : List Int) (result : List Int) (h_precond : solve_precond n packets) : Prop :=
  ValidSolution n packets result

theorem solve_spec_satisfied (n : Int) (packets : List Int) (h_precond : solve_precond n packets) :
    solve_postcond n packets (solve n packets h_precond) h_precond := by
  sorry
-- </vc-theorems>