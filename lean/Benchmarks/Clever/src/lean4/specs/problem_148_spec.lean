import Mathlib
import Benchmarks.Clever.CommonDefs
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → String → List String)
(planet1: String)
(planet2: String) :=
let spec (result: List String) :=
let planets := ["Mercury", "Venus", "Earth", "Mars", "Jupiter", "Saturn", "Uranus", "Neptune"];
if planet1 ∉ planets ∨ planet2 ∉ planets then
  result = []
else
  let index1 := listIndexOf planets planet1;
  let index2 := listIndexOf planets planet2;
  let minIdx := if index1 < index2 then index1 else index2;
  let maxIdx := if index1 < index2 then index2 else index1;
  (∀ str ∈ result, str ∈ planets) ∧
  (∀ planet ∈ planets, planet ∈ result ↔
    listIndexOf planets planet < maxIdx ∧
    minIdx < listIndexOf planets planet) ∧
  result.Sorted (fun a b => listIndexOf planets a < listIndexOf planets b)
∃ result, implementation planet1 planet2 = result ∧
spec result

def implementation (planet1: String) (planet2: String) : List String := sorry

theorem correctness
(planet1: String)
(planet2: String)
: problem_spec implementation planet1 planet2 := sorry 
