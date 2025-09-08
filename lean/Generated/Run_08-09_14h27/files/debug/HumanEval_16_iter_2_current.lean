/- 
function_signature: "def count_distinct_characters(string: str) -> int"
docstring: |
    Given a string, find out how many distinct characters (regardless of case) does it consist of
test_cases:
  - input: "xyzXYZ"
    expected_output: 3
  - input: "Jerry"
    expected_output: 4
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Nat :=
  (string.toList.map (fun c => c.toLower)).toFinset.card

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
let string_idx := {i: Nat | i < string.length}.toFinset
let characters := string_idx.image (fun i => string.toList[i]!)
let lowercase_characters := characters.image (fun c => c.toLower)
result = lowercase_characters.card;
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma string_idx_eq_list_range (s : String) :
    {i: Nat | i < s.length}.toFinset = (List.range s.length).toFinset := by
  ext i
  simp [Set.mem_setOf_eq, List.mem_range]

-- LLM HELPER
lemma characters_eq_toList (s : String) :
    let string_idx := {i: Nat | i < s.length}.toFinset
    string_idx.image (fun i => s.toList[i]!) = s.toList.toFinset := by
  simp only [string_idx_eq_list_range]
  ext c
  constructor
  · intro h
    simp at h
    obtain ⟨i, hi, hc⟩ := h
    simp [List.mem_range] at hi
    rw [← hc]
    simp [List.mem_toFinset]
    exact List.getElem_mem s.toList i hi
  · intro h
    simp [List.mem_toFinset] at h
    obtain ⟨i, hi, hc⟩ := List.mem_iff_get.mp h
    use i
    simp [List.mem_range, List.length_range]
    constructor
    · exact hi
    · rw [← hc]
      simp [List.getElem!_get]

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  unfold problem_spec
  use (string.toList.map (fun c => c.toLower)).toFinset.card
  constructor
  · rfl
  · simp only [characters_eq_toList]
    rw [← Finset.image_toFinset]
    simp [List.map_toFinset]

-- #test implementation "xyzXYZ" = 3
-- #test implementation "Jerry" = 4