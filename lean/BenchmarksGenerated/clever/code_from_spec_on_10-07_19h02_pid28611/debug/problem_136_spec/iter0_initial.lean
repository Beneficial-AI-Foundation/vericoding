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
  lst.filter (· < 0) |>.maximum?

-- LLM HELPER
def findMinPositive (lst: List Int) : Option Int :=
  lst.filter (· > 0) |>.minimum?

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

-- LLM HELPER
lemma maximum_spec {lst : List Int} : 
  match lst.maximum? with
  | none => lst = []
  | some m => m ∈ lst ∧ ∀ x ∈ lst, x ≤ m := by
  cases h : lst.maximum?
  · exact List.maximum?_eq_none_iff.mp h
  · exact List.maximum?_eq_some_iff.mp h

-- LLM HELPER
lemma minimum_spec {lst : List Int} : 
  match lst.minimum? with
  | none => lst = []
  | some m => m ∈ lst ∧ ∀ x ∈ lst, m ≤ x := by
  cases h : lst.minimum?
  · exact List.minimum?_eq_none_iff.mp h
  · exact List.minimum?_eq_some_iff.mp h

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
    · cases h : (lst.filter (· < 0)).maximum?
      · simp
        intro i hi_mem hi_neg
        have : i ∈ lst.filter (· < 0) := mem_filter_neg ⟨hi_mem, hi_neg⟩
        have empty : lst.filter (· < 0) = [] := List.maximum?_eq_none_iff.mp h
        rw [empty] at this
        simp at this
      · simp
        have spec := maximum_spec (lst.filter (· < 0))
        rw [h] at spec
        constructor
        · have : val ∈ lst.filter (· < 0) := spec.1
          exact (filter_neg_mem this).2
        · constructor
          · have : val ∈ lst.filter (· < 0) := spec.1
            exact (filter_neg_mem this).1
          · intro i hi_mem hi_neg
            have : i ∈ lst.filter (· < 0) := mem_filter_neg ⟨hi_mem, hi_neg⟩
            exact spec.2 i this
    · cases h : (lst.filter (· > 0)).minimum?
      · simp
        intro i hi_mem hi_pos
        have : i ∈ lst.filter (· > 0) := mem_filter_pos ⟨hi_mem, hi_pos⟩
        have empty : lst.filter (· > 0) = [] := List.minimum?_eq_none_iff.mp h
        rw [empty] at this
        simp at this
      · simp
        have spec := minimum_spec (lst.filter (· > 0))
        rw [h] at spec
        constructor
        · have : val ∈ lst.filter (· > 0) := spec.1
          exact (filter_pos_mem this).2
        · constructor
          · have : val ∈ lst.filter (· > 0) := spec.1
            exact (filter_pos_mem this).1
          · intro i hi_mem hi_pos
            have : i ∈ lst.filter (· > 0) := mem_filter_pos ⟨hi_mem, hi_pos⟩
            exact spec.2 i this