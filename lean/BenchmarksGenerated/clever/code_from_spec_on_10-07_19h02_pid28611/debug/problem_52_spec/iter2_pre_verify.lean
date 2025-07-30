import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → Bool)
(numbers: List Int)
(threshold: Int) :=
let numbers_below_threshold :=
  ∀ i, i < numbers.length → numbers[i]! < threshold;
let spec (res: Bool) :=
(numbers.length = 0 → res) ∧
(res ↔ numbers_below_threshold)
∃ result, implementation numbers threshold = result ∧
spec result

-- LLM HELPER
def all_below_threshold (numbers: List Int) (threshold: Int) : Bool :=
  numbers.all (fun x => x < threshold)

def implementation (numbers: List Int) (threshold: Int) : Bool := 
  all_below_threshold numbers threshold

-- LLM HELPER
lemma all_below_threshold_correct (numbers: List Int) (threshold: Int) :
  all_below_threshold numbers threshold = true ↔ 
  ∀ i, i < numbers.length → numbers[i]! < threshold := by
  simp [all_below_threshold, List.all_eq_true]
  constructor
  · intro h i hi
    have : numbers[i]! ∈ numbers := List.getElem!_mem numbers i hi
    exact h numbers[i]! this
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact h i hi

-- LLM HELPER
lemma all_below_threshold_empty (threshold: Int) :
  all_below_threshold [] threshold = true := by
  simp [all_below_threshold, List.all_eq_true]

theorem correctness
(numbers: List Int)
(threshold: Int)
: problem_spec implementation numbers threshold := by
  simp [problem_spec, implementation]
  use all_below_threshold numbers threshold
  constructor
  · rfl
  · constructor
    · intro h
      rw [h]
      exact all_below_threshold_empty threshold
    · exact all_below_threshold_correct numbers threshold