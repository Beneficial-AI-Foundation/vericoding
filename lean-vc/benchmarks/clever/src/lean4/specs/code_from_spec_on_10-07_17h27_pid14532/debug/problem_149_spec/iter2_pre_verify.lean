import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def find_min_even_string (lst: List String) : Option String :=
  let evens := lst.filter (fun s => Even s.length)
  match evens with
  | [] => none
  | _ => evens.min?

def implementation (lst: List String) : List String := 
  match find_min_even_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)
termination_by implementation lst => lst.length
decreasing_by
  simp_wf
  have h1 : head ∈ lst := by
    unfold find_min_even_string at *
    simp at *
    cases' evens_nonempty : lst.filter (fun s => Even s.length) with
    | nil => 
      simp at *
    | cons h t =>
      simp at *
      have := List.min?_mem evens_nonempty.symm
      rw [evens_nonempty] at this
      simp at this
      cases' this with left right
      · rw [← left]
        exact List.mem_of_mem_filter _ (List.mem_cons_self _ _)
      · exact List.mem_of_mem_filter _ (List.mem_cons_of_mem _ right)
  exact List.length_pos_of_mem h1

-- LLM HELPER
lemma find_min_even_string_spec (lst: List String) (head: String) :
  find_min_even_string lst = some head →
  head ∈ lst ∧ Even head.length ∧
  ∀ str ∈ lst, Even str.length → str.length ≥ head.length ∧ (str.length = head.length → str ≥ head) := by
  intro h
  unfold find_min_even_string at h
  simp at h
  constructor
  · cases' evens_case : lst.filter (fun s => Even s.length) with
    | nil => simp at h
    | cons hd tl =>
      have min_mem := List.min?_mem evens_case.symm
      rw [evens_case] at min_mem
      simp at min_mem
      rw [← h] at min_mem
      exact List.mem_of_mem_filter _ min_mem
  constructor
  · cases' evens_case : lst.filter (fun s => Even s.length) with
    | nil => simp at h
    | cons hd tl =>
      have min_mem := List.min?_mem evens_case.symm
      rw [evens_case] at min_mem
      simp at min_mem
      rw [← h] at min_mem
      exact List.of_mem_filter min_mem
  · intro str hstr heven
    cases' evens_case : lst.filter (fun s => Even s.length) with
    | nil => simp at h
    | cons hd tl =>
      have str_in_filter : str ∈ lst.filter (fun s => Even s.length) := 
        List.mem_filter.mpr ⟨hstr, heven⟩
      rw [evens_case] at str_in_filter
      have min_le := List.min?_le str_in_filter
      rw [← h] at min_le
      exact ⟨min_le, fun heq => by
        have min_mem := List.min?_mem evens_case.symm
        rw [evens_case] at min_mem
        simp at min_mem
        rw [← h] at min_mem
        exact List.min?_eq_min_of_mem min_mem str_in_filter heq⟩

-- LLM HELPER
lemma find_min_even_string_none (lst: List String) :
  find_min_even_string lst = none →
  ∀ str ∈ lst, Odd str.length := by
  intro h str hstr
  unfold find_min_even_string at h
  simp at h
  have : lst.filter (fun s => Even s.length) = [] := by
    cases' lst.filter (fun s => Even s.length) with
    | nil => rfl
    | cons hd tl => simp at h
  have not_even : ¬Even str.length := by
    intro heven
    have str_in_filter : str ∈ lst.filter (fun s => Even s.length) := 
      List.mem_filter.mpr ⟨hstr, heven⟩
    rw [this] at str_in_filter
    exact List.not_mem_nil _ str_in_filter
  exact Nat.odd_iff_not_even.mpr not_even

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · use implementation lst
    rfl
  · induction' lst using List.strongInductionOn with lst ih
    simp [implementation]
    cases h : find_min_even_string lst with
    | none =>
      simp
      exact find_min_even_string_none lst h
    | some head =>
      simp
      constructor
      · have spec := find_min_even_string_spec lst head h
        exact spec.2.1
      constructor
      · intro str hstr
        have spec := find_min_even_string_spec lst head h
        by_cases heven : Even str.length
        · right
          left
          have hge := spec.2.2 str hstr heven
          cases' Nat.lt_or_eq_of_le hge.1 with hlt heq
          · exact hlt
          · right
            exact ⟨heq.symm, hge.2 heq⟩
        · left
          exact Nat.odd_iff_not_even.mpr heven
      · have spec := find_min_even_string_spec lst head h
        have hmem : head ∈ lst := spec.1
        have hlen : lst.length > (lst.erase head).length := List.length_pos_of_mem hmem
        rw [ih (lst.erase head) hlen]