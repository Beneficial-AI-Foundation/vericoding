import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := ¬ n.isInt;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def shouldFilter (n : Rat) : Bool :=
  (n % 2 = 0) ∨ (n < 0) ∨ (¬ n.isInt)

def implementation (numbers: List Rat) : Int := 
  match numbers with
  | [] => 0
  | h :: t => 
    if shouldFilter h then 
      if t.length = 0 then 0 else implementation t
    else 
      h.floor ^ 2 + (if t.length = 0 then 0 else implementation t)

-- LLM HELPER
lemma implementation_nonneg (numbers: List Rat) : 0 ≤ implementation numbers := by
  induction numbers with
  | nil => simp [implementation]
  | cons h t ih =>
    simp [implementation]
    split_ifs with h1 h2 h3
    · exact le_refl (0 : Int)
    · exact ih
    · apply add_nonneg
      · exact sq_nonneg _
      · exact ih
    · apply add_nonneg
      · exact sq_nonneg _
      · exact le_refl (0 : Int)

-- LLM HELPER
lemma shouldFilter_def (n : Rat) : shouldFilter n = true ↔ (n % 2 = 0) ∨ (n < 0) ∨ (¬ n.isInt) := by
  simp [shouldFilter]

-- LLM HELPER
lemma implementation_single (h : Rat) : 
  implementation [h] = if shouldFilter h then 0 else h.floor ^ 2 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (h : Rat) (t : List Rat) (ht : t ≠ []) :
  implementation (h :: t) = if shouldFilter h then implementation t else h.floor ^ 2 + implementation t := by
  simp [implementation]
  cases' t with t_h t_t
  · contradiction
  · simp

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  exists implementation numbers
  constructor
  · rfl
  · intro h_pos
    constructor
    · exact implementation_nonneg numbers
    · cases' numbers with h t
      · simp at h_pos
      · simp [List.length_cons] at h_pos ⊢
        cases' t with t_h t_t
        · simp [List.length_nil]
          rw [implementation_single]
          simp [shouldFilter_def]
        · simp [List.length_cons]
          rw [implementation_cons]
          · simp [shouldFilter_def]
          · simp