import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def findMaxNegative (lst: List Int) : Option Int :=
  lst.filter (· < 0) |>.max?

-- LLM HELPER
def findMinPositive (lst: List Int) : Option Int :=
  lst.filter (· > 0) |>.min?

def implementation (lst: List Int) : (Option Int × Option Int) := 
  (findMaxNegative lst, findMinPositive lst)

-- LLM HELPER
lemma filter_neg_mem {lst : List Int} {x : Int} (h : x ∈ lst.filter (· < 0)) : x ∈ lst ∧ x < 0 := by
  simp [List.mem_filter] at h
  exact h

-- LLM HELPER
lemma filter_pos_mem {lst : List Int} {x : Int} (h : x ∈ lst.filter (· > 0)) : x ∈ lst ∧ x > 0 := by
  simp [List.mem_filter] at h
  exact h

-- LLM HELPER
lemma mem_filter_neg {lst : List Int} {x : Int} (h : x ∈ lst ∧ x < 0) : x ∈ lst.filter (· < 0) := by
  simp [List.mem_filter]
  exact h

-- LLM HELPER
lemma mem_filter_pos {lst : List Int} {x : Int} (h : x ∈ lst ∧ x > 0) : x ∈ lst.filter (· > 0) := by
  simp [List.mem_filter]
  exact h

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  simp [problem_spec]
  use (findMaxNegative lst, findMinPositive lst)
  simp [implementation]
  constructor
  · rfl
  · simp [findMaxNegative, findMinPositive]
    constructor
    · cases h : (lst.filter (· < 0)).max?
      · simp
        intro i hi_mem hi_neg
        have : i ∈ lst.filter (· < 0) := mem_filter_neg ⟨hi_mem, hi_neg⟩
        have empty : lst.filter (· < 0) = [] := List.max?_eq_none_iff.mp h
        rw [empty] at this
        simp at this
      · simp
        have spec := List.max?_eq_some_iff.mp h
        constructor
        · have : val ∈ lst.filter (· < 0) := spec.1
          exact (filter_neg_mem this).2
        · constructor
          · have : val ∈ lst.filter (· < 0) := spec.1
            exact (filter_neg_mem this).1
          · intro i hi_mem hi_neg
            have : i ∈ lst.filter (· < 0) := mem_filter_neg ⟨hi_mem, hi_neg⟩
            exact spec.2 i this
    · cases h : (lst.filter (· > 0)).min?
      · simp
        intro i hi_mem hi_pos
        have : i ∈ lst.filter (· > 0) := mem_filter_pos ⟨hi_mem, hi_pos⟩
        have empty : lst.filter (· > 0) = [] := List.min?_eq_none_iff.mp h
        rw [empty] at this
        simp at this
      · simp
        have spec := List.min?_eq_some_iff.mp h
        constructor
        · have : val ∈ lst.filter (· > 0) := spec.1
          exact (filter_pos_mem this).2
        · constructor
          · have : val ∈ lst.filter (· > 0) := spec.1
            exact (filter_pos_mem this).1
          · intro i hi_mem hi_pos
            have : i ∈ lst.filter (· > 0) := mem_filter_pos ⟨hi_mem, hi_pos⟩
            exact spec.2 i this