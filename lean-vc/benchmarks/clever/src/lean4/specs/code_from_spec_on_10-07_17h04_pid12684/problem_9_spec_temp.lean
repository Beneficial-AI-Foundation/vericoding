import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def maxInPrefix (numbers: List Int) (i: Nat) : Int :=
match numbers.take (i + 1) with
| [] => 0
| h :: t => t.foldl max h

def implementation (numbers: List Int) : List Int := 
numbers.mapIdx (fun i _ => maxInPrefix numbers i)

-- LLM HELPER
lemma maxInPrefix_mem (numbers: List Int) (i: Nat) (h: i < numbers.length) : 
  maxInPrefix numbers i ∈ numbers.take (i + 1) := by
  unfold maxInPrefix
  simp only [List.take_succ]
  cases' ht : numbers.take (i + 1) with hd tl
  · simp [List.take_eq_nil_iff] at ht
    omega
  · simp [ht]
    apply List.mem_of_mem_foldl_max
    rw [← ht]
    simp [List.take_succ]

-- LLM HELPER
lemma maxInPrefix_ge (numbers: List Int) (i j: Nat) (hi: i < numbers.length) (hj: j ≤ i) : 
  numbers[j]! ≤ maxInPrefix numbers i := by
  unfold maxInPrefix
  cases' ht : numbers.take (i + 1) with hd tl
  · simp [List.take_eq_nil_iff] at ht
    omega
  · simp [ht]
    apply List.le_foldl_max_of_mem
    rw [← ht]
    apply List.mem_take_of_mem
    · omega
    · simp [List.mem_iff_get]
      use j
      constructor
      · omega
      · simp

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  simp only [implementation]
  use numbers.mapIdx (fun i _ => maxInPrefix numbers i)
  constructor
  · rfl
  · constructor
    · simp [List.length_mapIdx]
    · intro i hi
      simp [List.getElem_mapIdx]
      constructor
      · exact maxInPrefix_mem numbers i hi
      · intro j hj
        exact maxInPrefix_ge numbers i j hi hj