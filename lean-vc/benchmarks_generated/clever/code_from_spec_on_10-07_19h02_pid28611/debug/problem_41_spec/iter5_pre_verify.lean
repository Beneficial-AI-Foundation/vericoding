import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Nat → Nat)
(x : Nat) :=
let spec (result: Nat) :=
  ∃ x_list : List Nat, x_list.length = x ∧ x_list.all (fun i => i = x)
  ∧ x_list.sum = result
∃ result, implementation x = result ∧
spec result

def implementation (x : Nat) : Nat := x * x

-- LLM HELPER
lemma replicate_all (n : Nat) (x : Nat) : (List.replicate n x).all (fun i => i = x) = true := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, List.all_cons, ih]

-- LLM HELPER
lemma replicate_sum (n : Nat) (x : Nat) : (List.replicate n x).sum = n * x := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => 
    simp [List.replicate, List.sum_cons, ih]
    ring

theorem correctness
(x : Nat)
: problem_spec implementation x := by
  simp [problem_spec, implementation]
  use x * x
  constructor
  · rfl
  · use List.replicate x x
    constructor
    · exact List.length_replicate x x
    constructor
    · exact replicate_all x x
    · rw [replicate_sum]
      ring