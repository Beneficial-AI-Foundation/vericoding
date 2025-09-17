

/-!
{
"name": "DafnyPrograms_tmp_tmp74_f9k_c_automaton_ExecuteAutomaton",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: DafnyPrograms_tmp_tmp74_f9k_c_automaton_ExecuteAutomaton",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Computes a cellular automaton given:
- init: Initial row of boolean cells
- rule: Function that determines next state based on cell and neighbors
- steps: Number of steps to simulate

The automaton table contains the initial row plus a row for each step.
Each cell's next state depends only on immediate neighbors.
Edge cells use 'false' for missing neighbors.
-/
def ExecuteAutomaton (init : Array Bool) (rule : Bool → Bool → Bool → Bool) (steps : Nat) :
Array (Array Bool) := sorry

/--
Specification for ExecuteAutomaton ensuring:
1. Initial row length ≥ 2
2. Table has initial row plus one row per step
3. Initial row is preserved at top
4. All rows have same length
5. Middle cells follow rule based on neighbors
6. Edge cells follow rule with false neighbor
-/
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
rule ((table[i]!)[(table[i]!).size - 2]!) ((table[i]!)[(table[i]!).size - 1]!) false)) := sorry
