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
  | head :: tail => 
    some (tail.foldl (fun acc s => 
      if s.length < acc.length ∨ (s.length = acc.length ∧ s < acc) then s else acc) head)

def implementation (lst: List String) : List String := 
  match find_min_even_string lst with
  | none => []
  | some min_even => min_even :: implementation (lst.erase min_even)

-- LLM HELPER
lemma find_min_even_string_correct (lst: List String) :
  match find_min_even_string lst with
  | none => ∀ str ∈ lst, Odd str.length
  | some min_even => 
    min_even ∈ lst ∧ Even min_even.length ∧
    ∀ str ∈ lst, Odd str.length ∨ str.length > min_even.length ∨ 
    (str.length = min_even.length ∧ str ≥ min_even) := by
  sorry

-- LLM HELPER
lemma implementation_terminates (lst: List String) : 
  ∃ result, implementation lst = result := by
  sorry

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  cases h : find_min_even_string lst with
  | none => 
    use []
    simp [implementation, h]
    exact find_min_even_string_correct lst ▸ h ▸ rfl
  | some min_even =>
    have h_prop := find_min_even_string_correct lst
    rw [h] at h_prop
    obtain ⟨h_mem, h_even, h_min⟩ := h_prop
    use min_even :: implementation (lst.erase min_even)
    constructor
    · simp [implementation, h]
    · constructor
      · exact h_even
      · constructor
        · exact h_min
        · rfl