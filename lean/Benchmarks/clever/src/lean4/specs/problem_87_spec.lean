import Benchmarks.Clever.CommonDefs
import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic
import Plausible
import Testing.PlausibleUtils

def problem_spec
(implementation: List (List Int) → Int → List (Nat × Nat))
(lst: List (List Int))
(x: Int) :=
let spec (result : List (Nat × Nat)) :=
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    row < lst.length ∧
    col < lst[row]!.length ∧
    (lst[row]!)[col]! = x) ∧
  (∀ i j, i < lst.length → j < lst[i]!.length →
    (lst[i]!)[j]! = x → (i, j) ∈ result) ∧
  (result.map (fun (r, c) => r)).Sorted Nat.le ∧
  (∀ i < result.length,
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (fun a b => a ≥ b))
∃ result,
  implementation lst x = result ∧
  spec result

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) := sorry

section PlausibleTests

open Plausible Testing.PlausibleUtils

example : ∀ (lst : List (List Int)) (x : Int),
  lst.length = 0 → implementation lst x = [] := by
  quick_plausible

example : ∀ (lst : List (List Int)) (x : Int),
  (∀ row ∈ lst, row.length = 0) → implementation lst x = [] := by
  quick_plausible

example : ∀ (lst : List (List Int)) (x : Int),
  (∀ row ∈ lst, ∀ elem ∈ row, elem ≠ x) → implementation lst x = [] := by
  quick_plausible

#eval checkWithMsg "Implementation returns valid indices" <|
  ∀ (lst : List (List Int)) (x : Int),
    lst.length > 0 →
    let result := implementation lst x
    ∀ (r, c) ∈ result, r < lst.length ∧ 
      (lst[r]? = some row → c < row.length)

end PlausibleTests

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x := by
  plausible (config := { numInst := 50 })
  sorry 
