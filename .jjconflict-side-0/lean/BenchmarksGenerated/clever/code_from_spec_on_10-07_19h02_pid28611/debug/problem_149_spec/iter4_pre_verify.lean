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
  let even_strs := lst.filter (fun s => decide (Even s.length))
  if even_strs.isEmpty then none
  else
    let min_len := even_strs.map (fun s => s.length) |>.min?
    match min_len with
    | none => none
    | some len =>
      let candidates := even_strs.filter (fun s => s.length = len)
      candidates.min?

def implementation (lst: List String) : List String :=
  match find_min_even_length_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)
termination_by lst.length
decreasing_by
  simp_wf
  apply List.length_erase_lt_of_mem
  unfold find_min_even_length_string at *
  simp at *
  have even_strs := lst.filter (fun s => decide (Even s.length))
  have hne : ¬even_strs.isEmpty := by
    by_contra hempty
    simp at *
    contradiction
  simp at *
  have min_len := even_strs.map (fun s => s.length) |>.min?
  cases' hmin : min_len with
  | none => simp at *
  | some len =>
    have candidates := even_strs.filter (fun s => s.length = len)
    have hcand : candidates.min? = some head := by assumption
    have head_in_candidates : head ∈ candidates := by
      have := List.min?_eq_some_iff.mp hcand
      exact this.1
    have head_in_even_strs : head ∈ even_strs := by
      rw [List.mem_filter] at head_in_candidates
      exact head_in_candidates.1
    rw [List.mem_filter] at head_in_even_strs
    exact head_in_even_strs.1

-- LLM HELPER
lemma find_min_even_length_string_none_iff (lst: List String) :
  find_min_even_length_string lst = none ↔ ∀ str ∈ lst, Odd str.length := by
  constructor
  · intro h str hstr
    by_contra hodd
    have heven : Even str.length := Nat.not_odd_iff_even.mp hodd
    have str_in_filter : str ∈ lst.filter (fun s => decide (Even s.length)) := by
      rw [List.mem_filter]
      exact ⟨hstr, by simp [heven]⟩
    have filter_nonempty : ¬(lst.filter (fun s => decide (Even s.length))).isEmpty := by
      rw [List.isEmpty_iff]
      intro hempty
      rw [hempty] at str_in_filter
      exact str_in_filter
    unfold find_min_even_length_string at h
    simp at h
    have : (lst.filter (fun s => decide (Even s.length))).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact ⟨str, str_in_filter⟩
    rw [if_neg (Bool.not_eq_true_of_eq_false this)] at h
    cases' h₁ : (lst.filter (fun s => decide (Even s.length))).map (fun s => s.length) |>.min? with
    | none => 
      rw [h₁] at h
      simp at h
    | some len =>
      rw [h₁] at h
      simp at h
  · intro h
    unfold find_min_even_length_string
    have : lst.filter (fun s => decide (Even s.length)) = [] := by
      rw [List.filter_eq_nil]
      intro str hstr
      have := h str hstr
      simp
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
  have even_strs := lst.filter (fun s => decide (Even s.length))
  have hne : ¬even_strs.isEmpty := by
    by_contra hempty
    simp at h
    rw [if_pos hempty] at h
    simp at h
  simp at h
  rw [if_neg (Bool.not_eq_true_of_eq_false _)] at h
  · have min_len := even_strs.map (fun s => s.length) |>.min?
    cases' hmin : min_len with
    | none =>
      rw [hmin] at h
      simp at h
    | some len =>
      rw [hmin] at h
      have candidates := even_strs.filter (fun s => s.length = len)
      have hcand : candidates.min? = some head := h
      have head_in_candidates : head ∈ candidates := by
        have := List.min?_eq_some_iff.mp hcand
        exact this.1
      have head_in_even_strs : head ∈ even_strs := by
        rw [List.mem_filter] at head_in_candidates
        exact head_in_candidates.1
      have head_in_lst : head ∈ lst := by
        rw [List.mem_filter] at head_in_even_strs
        exact head_in_even_strs.1
      have head_even : Even head.length := by
        rw [List.mem_filter] at head_in_even_strs
        simp at head_in_even_strs
        exact head_in_even_strs.2
      have head_len_eq : head.length = len := by
        rw [List.mem_filter] at head_in_candidates
        exact head_in_candidates.2
      have len_is_min : ∀ s ∈ even_strs, len ≤ s.length := by
        have := List.min?_eq_some_iff.mp hmin
        intro s hs
        have := this.2 s.length
        have : s.length ∈ even_strs.map (fun s => s.length) := by
          rw [List.mem_map]
          exact ⟨s, hs, rfl⟩
        exact this this
      have head_is_min_in_candidates : ∀ s ∈ candidates, head ≤ s := by
        have := List.min?_eq_some_iff.mp hcand
        exact this.2
      constructor
      · exact head_in_lst
      constructor
      · exact head_even
      · intro str hstr
        by_cases hstr_even : Even str.length
        · right
          have str_in_even_strs : str ∈ even_strs := by
            rw [List.mem_filter]
            exact ⟨hstr, by simp [hstr_even]⟩
          have : len ≤ str.length := len_is_min str str_in_even_strs
          rw [head_len_eq] at this
          cases' Nat.lt_or_eq_of_le this with
          | inl hlt =>
            left
            exact hlt
          | inr heq =>
            right
            constructor
            · exact heq.symm
            · have str_in_candidates : str ∈ candidates := by
                rw [List.mem_filter]
                exact ⟨str_in_even_strs, heq⟩
              exact head_is_min_in_candidates str str_in_candidates
        · left
          exact Nat.odd_iff_not_even.mpr hstr_even
  · rw [List.isEmpty_eq_false_iff_exists_mem]
    have : ∃ s ∈ lst, Even s.length := by
      by_contra h_all_odd
      simp at h_all_odd
      have : lst.filter (fun s => decide (Even s.length)) = [] := by
        rw [List.filter_eq_nil]
        intro s hs
        simp
        exact Nat.odd_iff_not_even.mp (h_all_odd s hs)
      rw [this] at hne
      simp at hne
    obtain ⟨s, hs_mem, hs_even⟩ := this
    use s
    rw [List.mem_filter]
    exact ⟨hs_mem, by simp [hs_even]⟩

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
        · rfl