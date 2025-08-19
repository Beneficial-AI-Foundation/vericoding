import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def List.all {α : Type*} (l : List α) (p : α → Bool) : Bool :=
  l.foldr (fun a b => p a && b) true

-- LLM HELPER
def List.count {α : Type*} [DecidableEq α] (l : List α) (a : α) : Nat :=
  l.filter (· == a) |>.length

-- LLM HELPER
lemma List.all_eq_true {α : Type*} (l : List α) (p : α → Bool) : 
  l.all p = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [List.all]
  | cons h t ih => 
    simp [List.all, Bool.and_eq_true]
    constructor
    · intro ⟨hp, ht⟩
      intro x hx
      cases hx with
      | head => exact hp
      | tail _ hxt => exact ih.mp ht x hxt
    · intro h
      constructor
      · exact h h (List.mem_cons_self h t)
      · apply ih.mpr
        intro x hx
        exact h x (List.mem_cons_of_mem h hx)

-- LLM HELPER
lemma List.mem_of_mem_filter {α : Type*} {l : List α} {p : α → Bool} {x : α} 
  (h : x ∈ l.filter p) : x ∈ l := by
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma List.of_mem_filter {α : Type*} {l : List α} {p : α → Bool} {x : α} 
  (h : x ∈ l.filter p) : p x = true := by
  exact List.of_mem_filter h

-- LLM HELPER
lemma List.mem_filter_iff {α : Type*} {l : List α} {p : α → Bool} {x : α} :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  exact List.mem_filter

-- LLM HELPER
lemma List.count_eq_zero {α : Type*} [DecidableEq α] {l : List α} {a : α} :
  l.count a = 0 ↔ a ∉ l := by
  simp [List.count, List.length_eq_zero, List.filter_eq_nil]
  constructor
  · intro h x hx
    simp at h
    exact h x hx rfl
  · intro h
    simp
    intro x hx heq
    rw [← heq] at hx
    exact h hx

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
  numbers.all (λ x => x > 0 → x ∈ result) ∧
  result.all (λ x => result.count x = numbers.count x);
-- program termination
∃ result,
  implementation numbers = result ∧
  spec result

def implementation (numbers: List Int): List Int := numbers.filter (λ x => x > 0)

-- LLM HELPER
lemma filter_positive_mem {numbers : List Int} {x : Int} (h : x ∈ numbers.filter (λ y => y > 0)) : x ∈ numbers := by
  exact List.mem_of_mem_filter h

-- LLM HELPER
lemma filter_positive_prop {numbers : List Int} {x : Int} (h : x ∈ numbers.filter (λ y => y > 0)) : x > 0 := by
  have : (λ y => y > 0) x = true := List.of_mem_filter h
  simp at this
  exact this

-- LLM HELPER
lemma mem_filter_of_mem_and_prop {numbers : List Int} {x : Int} (h_mem : x ∈ numbers) (h_prop : x > 0) : x ∈ numbers.filter (λ y => y > 0) := by
  rw [List.mem_filter_iff]
  constructor
  · exact h_mem
  · simp [h_prop]

-- LLM HELPER
lemma count_filter_eq {numbers : List Int} {x : Int} (h : x > 0) : (numbers.filter (λ y => y > 0)).count x = numbers.count x := by
  simp [List.count]
  congr 1
  ext y
  simp
  constructor
  · intro ⟨hy_mem, hy_pos, heq⟩
    exact ⟨hy_mem, heq⟩
  · intro ⟨hy_mem, heq⟩
    constructor
    · exact hy_mem
    · constructor
      · rw [← heq]; exact h
      · exact heq

-- LLM HELPER
lemma count_filter_zero {numbers : List Int} {x : Int} (h : ¬x > 0) : (numbers.filter (λ y => y > 0)).count x = 0 := by
  rw [List.count_eq_zero]
  intro hx
  have : x > 0 := filter_positive_prop hx
  exact h this

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use numbers.filter (λ x => x > 0)
  constructor
  · rfl
  · simp [List.all_eq_true]
    constructor
    · intro x h
      simp
      constructor
      · exact filter_positive_prop h
      · exact filter_positive_mem h
    · constructor
      · intro x h_mem h_pos
        simp at h_pos
        exact mem_filter_of_mem_and_prop h_mem h_pos
      · intro x h_mem
        by_cases h : x > 0
        · exact count_filter_eq h
        · rw [count_filter_zero h]
          rw [List.count_eq_zero]
          intro h_mem_orig
          have : x > 0 := by
            by_contra hnot
            exact h hnot
          exact h this