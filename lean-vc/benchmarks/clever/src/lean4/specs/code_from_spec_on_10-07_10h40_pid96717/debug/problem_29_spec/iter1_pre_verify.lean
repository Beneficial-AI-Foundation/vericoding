import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
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

def implementation (strings: List String) (pref: String) : List String := 
  strings.filter (λ s => s.startsWith pref)

theorem correctness
(strings: List String)
(pref: String)
: problem_spec implementation strings pref := by
  unfold problem_spec
  use strings.filter (λ s => s.startsWith pref)
  constructor
  · rfl
  · constructor
    · simp [List.all_iff_forall]
      intro s hs
      exact List.of_mem_filter hs
    · constructor
      · simp [List.all_iff_forall]
        intro s hs
        exact List.mem_filter_of_mem hs
      · constructor
        · simp [List.all_iff_forall]
          intro s hs hpref
          exact List.mem_filter_of_mem hs hpref
        · intro s hs
          simp [List.count_filter]
          rw [List.count_eq_length_filter]
          rw [List.count_eq_length_filter]
          congr 1
          ext x
          simp
          constructor
          · intro ⟨hx1, hx2⟩
            exact ⟨hx2, hx1⟩
          · intro ⟨hx1, hx2⟩
            exact ⟨hx2, hx1⟩