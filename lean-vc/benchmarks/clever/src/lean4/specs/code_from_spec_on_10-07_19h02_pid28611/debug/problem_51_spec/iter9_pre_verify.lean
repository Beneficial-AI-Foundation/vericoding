import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(string: String) :=
let is_consonant (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c);
-- spec
let spec (result: String) :=
result.all (λ c => is_consonant c) ∧ result.length ≤ string.length ∧
∀ c, result.contains c → string.contains c ∧
∀ c , string.contains c ∧ is_consonant c → (result.contains c);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def is_consonant_helper (c: Char): Bool :=
  let vowels := "aeiouAEIOU"
  not (vowels.contains c)

-- LLM HELPER
def filter_consonants (s: String) : String :=
  s.data.filter is_consonant_helper |>.asString

def implementation (string: String) : String := 
  filter_consonants string

-- LLM HELPER
lemma is_consonant_eq : ∀ c, is_consonant_helper c = 
  let vowels := "aeiouAEIOU"
  not (vowels.contains c) := by
  intro c
  rfl

-- LLM HELPER
lemma filter_consonants_all_consonant (s: String) : 
  (filter_consonants s).all is_consonant_helper = true := by
  simp [filter_consonants]
  apply String.all_eq_true.mpr
  intro c hc
  simp [String.mem_data] at hc
  simp [List.mem_filter] at hc
  exact hc.2

-- LLM HELPER
lemma filter_consonants_length_le (s: String) : 
  (filter_consonants s).length ≤ s.length := by
  simp [filter_consonants]
  rw [String.length_data]
  exact List.length_filter_le _ _

-- LLM HELPER
lemma filter_consonants_contains_subset (s: String) : 
  ∀ c, (filter_consonants s).contains c → s.contains c := by
  intro c h
  simp [filter_consonants] at h
  simp [String.contains] at h ⊢
  simp [List.mem_filter] at h
  exact h.1

-- LLM HELPER
lemma filter_consonants_contains_all_consonants (s: String) : 
  ∀ c, s.contains c ∧ is_consonant_helper c → (filter_consonants s).contains c := by
  intro c ⟨h1, h2⟩
  simp [filter_consonants]
  simp [String.contains] at h1 ⊢
  simp [List.mem_filter]
  exact ⟨h1, h2⟩

-- LLM HELPER
lemma String.contains_iff_mem_data (s: String) (c: Char) : 
  s.contains c ↔ c ∈ s.data := by
  simp [String.contains]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  simp only [is_consonant_eq]
  use filter_consonants s
  constructor
  · rfl
  · constructor
    · exact filter_consonants_all_consonant s
    · constructor
      · exact filter_consonants_length_le s
      · constructor
        · exact filter_consonants_contains_subset s
        · exact filter_consonants_contains_all_consonants s