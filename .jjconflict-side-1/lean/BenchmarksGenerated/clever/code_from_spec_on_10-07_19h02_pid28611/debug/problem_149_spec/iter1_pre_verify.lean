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
def find_min_even_length_string (lst: List String) : Option String :=
  let even_strs := lst.filter (fun s => Even s.length)
  if even_strs.isEmpty then none
  else
    let min_len := even_strs.map (fun s => s.length) |>.minimum?
    match min_len with
    | none => none
    | some len =>
      let candidates := even_strs.filter (fun s => s.length = len)
      candidates.minimum?

def implementation (lst: List String) : List String :=
  match find_min_even_length_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)

-- LLM HELPER
lemma find_min_even_length_string_none_iff (lst: List String) :
  find_min_even_length_string lst = none ↔ ∀ str ∈ lst, Odd str.length := by
  constructor
  · intro h str hstr
    by_contra hodd
    have heven : Even str.length := Nat.odd_iff_not_even.mp hodd
    have : str ∈ lst.filter (fun s => Even s.length) := by
      rw [List.mem_filter]
      exact ⟨hstr, heven⟩
    have : ¬(lst.filter (fun s => Even s.length)).isEmpty := by
      rw [List.isEmpty_iff_eq_nil]
      intro hempty
      rw [hempty] at this
      exact this
    unfold find_min_even_length_string at h
    simp at h
    cases' h₁ : lst.filter (fun s => Even s.length) with
    | nil => 
      rw [h₁] at this
      exact this
    | cons head tail =>
      rw [h₁] at h
      simp at h
  · intro h
    unfold find_min_even_length_string
    have : lst.filter (fun s => Even s.length) = [] := by
      rw [List.filter_eq_nil]
      intro str hstr
      have := h str hstr
      exact Nat.odd_iff_not_even.mp this
    rw [this]
    simp

-- LLM HELPER
lemma find_min_even_length_string_some_properties (lst: List String) (head: String) :
  find_min_even_length_string lst = some head →
  head ∈ lst ∧ Even head.length ∧
  (∀ str ∈ lst, Odd str.length ∨ str.length > head.length ∨ str.length = head.length ∧ str ≥ head) := by
  intro h
  unfold find_min_even_length_string at h
  have even_strs := lst.filter (fun s => Even s.length)
  have hne : ¬even_strs.isEmpty := by
    by_contra hempty
    simp at h
    rw [if_pos hempty] at h
    simp at h
  simp at h
  rw [if_neg hne] at h
  have min_len := even_strs.map (fun s => s.length) |>.minimum?
  cases' hmin : min_len with
  | none =>
    rw [hmin] at h
    simp at h
  | some len =>
    rw [hmin] at h
    have candidates := even_strs.filter (fun s => s.length = len)
    have hcand : candidates.minimum? = some head := h
    have head_in_candidates : head ∈ candidates := by
      have := List.minimum?_eq_some_iff.mp hcand
      exact this.1
    have head_in_even_strs : head ∈ even_strs := by
      rw [List.mem_filter] at head_in_candidates
      exact head_in_candidates.1
    have head_in_lst : head ∈ lst := by
      rw [List.mem_filter] at head_in_even_strs
      exact head_in_even_strs.1
    have head_even : Even head.length := by
      rw [List.mem_filter] at head_in_even_strs
      exact head_in_even_strs.2
    have head_len_eq : head.length = len := by
      rw [List.mem_filter] at head_in_candidates
      exact head_in_candidates.2
    have len_is_min : ∀ s ∈ even_strs, len ≤ s.length := by
      have := List.minimum?_eq_some_iff.mp hmin
      intro s hs
      have := this.2 s.length
      have : s.length ∈ even_strs.map (fun s => s.length) := by
        rw [List.mem_map]
        exact ⟨s, hs, rfl⟩
      exact this this
    have head_is_min_in_candidates : ∀ s ∈ candidates, head ≤ s := by
      have := List.minimum?_eq_some_iff.mp hcand
      exact this.2
    constructor
    · exact head_in_lst
    constructor
    · exact head_even
    · intro str hstr
      by_cases hstr_even : Even str.length
      · right
        right
        have str_in_even_strs : str ∈ even_strs := by
          rw [List.mem_filter]
          exact ⟨hstr, hstr_even⟩
        have : len ≤ str.length := len_is_min str str_in_even_strs
        rw [head_len_eq] at this
        cases' Nat.lt_or_eq_of_le this with
        | inl hlt =>
          left
          exact hlt
        | inr heq =>
          constructor
          · exact heq.symm
          · have str_in_candidates : str ∈ candidates := by
              rw [List.mem_filter]
              exact ⟨str_in_even_strs, heq⟩
            exact head_is_min_in_candidates str str_in_candidates
      · left
        exact Nat.odd_iff_not_even.mpr hstr_even

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  induction lst using List.strong_induction_on with
  | ind lst ih =>
    let spec := fun result =>
      match result with
      | [] => ∀ str ∈ lst, Odd str.length
      | head::tail =>
        Even head.length ∧
        (∀ str ∈ lst,
          Odd str.length ∨
          str.length > head.length ∨
          str.length = head.length ∧ str ≥ head)
        ∧ implementation (lst.erase head) = tail
    use implementation lst
    constructor
    · rfl
    · unfold implementation
      cases' h : find_min_even_length_string lst with
      | none =>
        simp
        exact find_min_even_length_string_none_iff.mp h
      | some head =>
        simp
        have props := find_min_even_length_string_some_properties lst head h
        constructor
        · exact props.2.1
        constructor
        · exact props.2.2
        · have head_in_lst : head ∈ lst := props.1
          have lst_erase_lt : lst.erase head < lst := by
            exact List.length_erase_lt_of_mem head_in_lst
          have := ih (lst.erase head) lst_erase_lt
          have : ∃ result, implementation (lst.erase head) = result ∧ 
                 (match result with
                  | [] => ∀ str ∈ lst.erase head, Odd str.length
                  | head'::tail' =>
                    Even head'.length ∧
                    (∀ str ∈ lst.erase head,
                      Odd str.length ∨
                      str.length > head'.length ∨
                      str.length = head'.length ∧ str ≥ head')
                    ∧ implementation ((lst.erase head).erase head') = tail') := this
          cases' this with result hresult
          rw [hresult.1]
          exact hresult.1