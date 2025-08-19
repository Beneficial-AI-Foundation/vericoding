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
def filter_consonants (s: String) : String :=
  s.filter (fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c))

def implementation (string: String) : String := filter_consonants string

-- LLM HELPER
lemma filter_consonants_all_consonant (s: String) : 
  (filter_consonants s).all (fun c => 
    let vowels := "aeiouAEIOU"
    not (vowels.contains c)) := by
  simp [filter_consonants]
  exact String.all_filter _ _

-- LLM HELPER
lemma filter_consonants_length_le (s: String) : 
  (filter_consonants s).length ≤ s.length := by
  simp [filter_consonants]
  exact String.length_filter_le _ _

-- LLM HELPER
lemma filter_consonants_contains_subset (s: String) : 
  ∀ c, (filter_consonants s).contains c → s.contains c := by
  intro c h
  simp [filter_consonants] at h
  exact String.contains_filter_subset _ _ h

-- LLM HELPER
lemma filter_consonants_contains_all_consonants (s: String) : 
  ∀ c, s.contains c ∧ (let vowels := "aeiouAEIOU"; not (vowels.contains c)) → 
    (filter_consonants s).contains c := by
  intro c ⟨h1, h2⟩
  simp [filter_consonants]
  exact String.contains_filter_of_contains_and_pred h1 h2

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec, implementation]
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