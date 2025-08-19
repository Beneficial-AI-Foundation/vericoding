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
  let even_strings := lst.filter (fun s => Even s.length)
  match even_strings with
  | [] => none
  | _ => some (even_strings.foldl (fun acc s => if s.length < acc.length ∨ (s.length = acc.length ∧ s ≤ acc) then s else acc) even_strings.head!)

def implementation (lst: List String) : List String :=
  match find_min_even_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)

-- LLM HELPER
lemma list_erase_length_lt {α : Type*} [DecidableEq α] (lst : List α) (x : α) (h : x ∈ lst) :
  (lst.erase x).length < lst.length := by
  exact List.length_erase_of_mem h

-- LLM HELPER
lemma implementation_terminates (lst : List String) : ∃ result, implementation lst = result := by
  use implementation lst
  rfl

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  simp only [implementation_terminates]
  use implementation lst
  constructor
  · rfl
  · -- Show that the result satisfies the spec
    induction lst using List.strong_induction with
    | ind lst ih =>
      unfold implementation
      simp only [find_min_even_string]
      let even_strings := lst.filter (fun s => Even s.length)
      cases h : even_strings with
      | nil =>
        -- No even strings, so result is []
        simp only [List.filter_eq_nil_iff] at h
        simp
        intro str hstr
        exact h str hstr
      | cons head tail =>
        -- Found an even string
        have : head ∈ even_strings := by simp [h]
        have : Even head.length := by
          rw [List.mem_filter] at this
          exact this.2
        simp only [List.foldl_cons, List.head_cons]
        constructor
        · -- head has even length
          exact this
        constructor
        · -- For all strings in lst, either odd length or length > head.length or equal length and ≥ head
          intro str hstr
          by_cases h_even : Even str.length
          · -- str has even length
            have : str ∈ even_strings := by
              rw [List.mem_filter]
              exact ⟨hstr, h_even⟩
            -- head is the minimum even string
            right
            right
            sorry -- This requires showing head is lexicographically minimal
          · -- str has odd length
            left
            rw [Nat.odd_iff_not_even]
            exact h_even
        · -- Recursive call correctness
          have : (lst.erase head).length < lst.length := by
            apply list_erase_length_lt
            sorry -- Need to show head ∈ lst
          exact ih (lst.erase head) this