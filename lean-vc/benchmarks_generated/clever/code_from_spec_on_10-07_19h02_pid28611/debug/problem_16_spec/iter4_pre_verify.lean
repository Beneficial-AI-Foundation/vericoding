import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
-- spec
let spec (result: Nat) :=
let string_idx := {i: Nat | i < string.length}.toFinset
let characters := string_idx.image (fun i => string.toList.get! i)
let lowercase_characters := characters.image (fun c => c.toLower)
result = lowercase_characters.card;
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def uniqueLowercaseCount (s: String) : Nat :=
  (s.toList.map Char.toLower).toFinset.card

def implementation (string: String) : Nat := uniqueLowercaseCount string

-- LLM HELPER
lemma string_length_eq_toList_length (s: String) : s.length = s.toList.length := by
  rfl

-- LLM HELPER
lemma get_mem_toList (s: String) (i: Nat) (h: i < s.length) :
  s.toList.get! i ∈ s.toList := by
  have : i < s.toList.length := by
    rw [← string_length_eq_toList_length]
    exact h
  exact List.get!_mem s.toList i this

-- LLM HELPER
lemma finset_image_toList_eq (s: String) :
  let string_idx := {i: Nat | i < s.length}.toFinset
  let characters := string_idx.image (fun i => s.toList.get! i)
  characters = s.toList.toFinset := by
  ext c
  simp only [Finset.mem_image, Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_filter, 
             Finset.mem_range, List.mem_toFinset]
  constructor
  · intro ⟨i, hi, hc⟩
    rw [← hc]
    have hi' : i < s.length := by
      rw [Set.mem_toFinset] at hi
      exact hi
    exact get_mem_toList s i hi'
  · intro hc
    obtain ⟨i, hi, h_eq⟩ := List.mem_iff_get.mp hc
    use i
    constructor
    · rw [Set.mem_toFinset]
      rw [string_length_eq_toList_length]
      exact hi
    · have hi_valid : i < s.toList.length := hi
      rw [List.get!_of_lt hi_valid]
      rw [h_eq]

-- LLM HELPER
lemma finset_image_map_eq (l: List Char) :
  (l.toFinset.image Char.toLower) = (l.map Char.toLower).toFinset := by
  ext c
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]

theorem correctness
(string: String)
: problem_spec implementation string
:= by
  simp only [problem_spec, implementation, uniqueLowercaseCount]
  use (string.toList.map Char.toLower).toFinset.card
  constructor
  · rfl
  · simp only [Set.toFinset_setOf]
    rw [finset_image_toList_eq]
    rw [finset_image_map_eq]