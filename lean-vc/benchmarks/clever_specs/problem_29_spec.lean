import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List String → String → List String)
(strings: List String)
(pref: String) :=
let spec (result: List String) :=
result.all (λ s => s.startsWith pref) ∧
result.all (λ s => s ∈ strings) ∧
strings.all (λ s => s.startsWith pref → s ∈ result) ∧
∀ s : String, s ∈ result → result.count s = strings.count s;
∃ result, implementation strings pref = result ∧
spec result

def implementation (strings: List String) (pref: String) : List String := sorry

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := sorry 