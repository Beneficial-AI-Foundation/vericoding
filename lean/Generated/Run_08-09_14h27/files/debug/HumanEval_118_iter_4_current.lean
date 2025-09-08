import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_vowel (c : Char) : Bool :=
  c ∈ ['a', 'e', 'i', 'o', 'u', 'A', 'E', 'I', 'O', 'U']

-- LLM HELPER
def is_consonant (c : Char) : Bool :=
  c.isAlpha && !is_vowel c

-- LLM HELPER
def find_closest_vowel_aux (chars : List Char) : Option Char :=
  let n := chars.length
  if n < 3 then none
  else
    let rec search (i : Nat) : Option Char :=
      if i + 2 >= n then none
      else
        let prev := chars[i]!
        let curr := chars[i + 1]!
        let next := chars[i + 2]!
        if is_consonant prev && is_vowel curr && is_consonant next then
          match search (i + 1) with
          | some result => some result
          | none => some curr
        else
          search (i + 1)
    search 0

def implementation (s: String) : String :=
  match find_closest_vowel_aux s.data with
  | some c => String.mk [c]
  | none => ""

-- LLM HELPER
def is_consonant_prop (c: Char) : Prop :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
lemma is_consonant_bool_prop_equiv (c : Char) : 
  is_consonant c = true ↔ is_consonant_prop c := by
  constructor
  · intro h
    unfold is_consonant is_vowel at h
    simp at h
    exact h
  · intro h
    unfold is_consonant is_vowel
    simp
    exact h

-- LLM HELPER
def is_consonant_expanded (c : Char) : Prop :=
  c.isAlpha = true ∧
  ¬c = 'a' ∧ ¬c = 'e' ∧ ¬c = 'i' ∧ ¬c = 'o' ∧ ¬c = 'u' ∧ 
  ¬c = 'A' ∧ ¬c = 'E' ∧ ¬c = 'I' ∧ ¬c = 'O' ∧ ¬c = 'U'

-- LLM HELPER
lemma consonant_equiv (c : Char) : 
  is_consonant_prop c ↔ is_consonant_expanded c := by
  unfold is_consonant_prop is_consonant_expanded
  simp only [List.mem_cons, List.mem_singleton, not_or]
  constructor
  · intro ⟨h1, h2, h3⟩
    constructor
    · exact h3
    · exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    constructor
    · exact h2.1
    constructor
    · exact h2.2
    · exact h1

-- LLM HELPER  
lemma is_vowel_not_consonant (c : Char) : 
  is_vowel c = true → ¬is_consonant_expanded c := by
  intro h
  unfold is_vowel at h
  simp only [List.mem_cons, List.mem_singleton] at h
  unfold is_consonant_expanded
  intro ⟨_, not_vowels⟩
  cases h with
  | inl h => exact not_vowels.1 h
  | inr h => 
    cases h with
    | inl h => exact not_vowels.2.1 h
    | inr h =>
      cases h with
      | inl h => exact not_vowels.2.2.1 h
      | inr h =>
        cases h with
        | inl h => exact not_vowels.2.2.2.1 h
        | inr h =>
          cases h with
          | inl h => exact not_vowels.2.2.2.2.1 h
          | inr h =>
            cases h with
            | inl h => exact not_vowels.2.2.2.2.2.1 h
            | inr h =>
              cases h with
              | inl h => exact not_vowels.2.2.2.2.2.2.1 h
              | inr h =>
                cases h with
                | inl h => exact not_vowels.2.2.2.2.2.2.2.1 h
                | inr h =>
                  cases h with
                  | inl h => exact not_vowels.2.2.2.2.2.2.2.2.1 h
                  | inr h => exact not_vowels.2.2.2.2.2.2.2.2.2 h

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (fun c => c.isAlpha) →
  let is_consonant (c: Char) :=
    c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
    c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
    c.isAlpha
  (result = "" → ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]!) ∧
  (result ≠ "" →
    result.length = 1 ∧
    result.data[0]! ∈ s.data ∧
    ¬ is_consonant result.data[0]! ∧
    ∃ (i j k : Nat),
      i < j ∧ j < k ∧ k < s.length ∧
      is_consonant s.data[i]! ∧ ¬ is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
      result.data[0]! = s.data[j]! ∧
      (∀ (i' j' k' : Nat),
        i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant s.data[i']! ∧ ¬ is_consonant s.data[j']! ∧ is_consonant s.data[k']! →
        j' ≤ j)
  )
-- program termination
∃ result,
  implementation s = result ∧
  spec result

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    unfold implementation
    split <;> simp
    · sorry
    · constructor
      · rfl
      constructor
      · sorry
      constructor  
      · sorry
      · sorry