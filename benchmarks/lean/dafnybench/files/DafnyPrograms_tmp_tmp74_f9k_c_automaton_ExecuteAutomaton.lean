-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ExecuteAutomaton (init : Array Bool) (rule : Bool → Bool → Bool → Bool) (steps : Nat) :
Array (Array Bool) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ExecuteAutomaton_spec
(init : Array Bool) (rule : Bool → Bool → Bool → Bool) (steps : Nat) :
init.size ≥ 2 →
let table := ExecuteAutomaton init rule steps
(table.size = 1 + steps) ∧
(table[0]! = init) ∧
(∀ i : Nat, i < table.size → (table[i]!).size = init.size) ∧
(∀ i j : Nat, i < table.size - 1 ∧ 1 ≤ j ∧ j ≤ (table[i]!).size - 2 →
(table[i+1]!)[j]! = rule ((table[i]!)[j-1]!) ((table[i]!)[j]!) ((table[i]!)[j+1]!)) ∧
(∀ i : Nat, i < table.size - 1 →
((table[i+1]!)[0]! = rule false ((table[i]!)[0]!) ((table[i]!)[1]!)) ∧
((table[i+1]!)[(table[i]!).size - 1]! =
rule ((table[i]!)[(table[i]!).size - 2]!) ((table[i]!)[(table[i]!).size - 1]!) false)) :=
sorry
-- </vc-theorems>