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
  | _ => evens.minimum?

def implementation (lst: List String) : List String := 
  match find_min_even_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)

-- LLM HELPER
lemma find_min_even_string_spec (lst: List String) (head: String) :
  find_min_even_string lst = some head →
  head ∈ lst ∧ Even head.length ∧
  ∀ str ∈ lst, Even str.length → str.length ≥ head.length ∧ (str.length = head.length → str ≥ head) := by
  intro h
  unfold find_min_even_string at h
  simp at h
  sorry

-- LLM HELPER
lemma find_min_even_string_none (lst: List String) :
  find_min_even_string lst = none →
  ∀ str ∈ lst, Odd str.length := by
  intro h
  unfold find_min_even_string at h
  simp at h
  sorry

-- LLM HELPER
lemma implementation_terminates (lst: List String) :
  ∃ result, implementation lst = result := by
  use implementation lst
  rfl

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  use implementation lst
  constructor
  · exact implementation_terminates lst
  · induction lst using List.strongInductionOn with
    | ind lst ih =>
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
          rw [ih (lst.erase head)]
          simp
          sorry