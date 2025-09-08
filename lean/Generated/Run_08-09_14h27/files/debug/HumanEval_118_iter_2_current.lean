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
def find_closest_vowel_aux (chars : List Char) (idx : Nat) : Option (Nat × Char) :=
  match chars with
  | [] => none
  | [_] => none
  | [_, _] => none
  | _ =>
    let rec search (i : Nat) : Option (Nat × Char) :=
      if i + 2 >= chars.length then none
      else if i = 0 then search (i + 1)
      else
        let prev := chars[i - 1]!
        let curr := chars[i]!
        let next := chars[i + 1]!
        if is_consonant prev && is_vowel curr && is_consonant next then
          match search (i + 1) with
          | some result => some result
          | none => some (i, curr)
        else
          search (i + 1)
    search 1

def implementation (s: String) : String :=
  match find_closest_vowel_aux s.data 0 with
  | some (_, c) => String.mk [c]
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
    simp [is_consonant, is_vowel] at h
    simp [is_consonant_prop]
    constructor
    · simp at h
      exact h.2.1
    constructor
    · simp at h
      exact h.2.2
    · exact h.1
  · intro h
    simp [is_consonant, is_vowel]
    simp [is_consonant_prop] at h
    constructor
    · exact h.2.2
    · simp
      constructor
      · exact h.1
      · exact h.2.1

-- LLM HELPER
lemma is_vowel_not_consonant (c : Char) : 
  is_vowel c = true → ¬is_consonant_prop c := by
  intro h
  simp [is_vowel] at h
  simp [is_consonant_prop]
  cases h with
  | inl h => simp [h]
  | inr h => 
    cases h with
    | inl h => simp [h]
    | inr h =>
      cases h with
      | inl h => simp [h]
      | inr h =>
        cases h with
        | inl h => simp [h]
        | inr h =>
          cases h with
          | inl h => simp [h]
          | inr h =>
            cases h with
            | inl h => simp [h]
            | inr h =>
              cases h with
              | inl h => simp [h]
              | inr h =>
                cases h with
                | inl h => simp [h]
                | inr h =>
                  cases h with
                  | inl h => simp [h]
                  | inr h => simp [h]

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
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro spec_result h_alpha
    simp [implementation]
    cases h : find_closest_vowel_aux s.data 0 with
    | none => 
      simp
      intro i j k h1 h2 h3 h4 h5 h6
      exfalso
      sorry -- Show contradiction: if pattern exists, find_closest_vowel_aux shouldn't return none
    | some p =>
      cases p with
      | mk idx c =>
        simp
        constructor
        · simp [String.mk, List.length]
        constructor
        · simp [String.mk]
          sorry -- Show c ∈ s.data from find_closest_vowel_aux properties
        constructor
        · simp [String.mk]
          sorry -- Show ¬is_consonant_prop c from find_closest_vowel_aux properties
        · use idx - 1, idx, idx + 1
          sorry -- Show the pattern exists and is rightmost

-- #test implementation "yogurt" = "u"
-- #test implementation "FULL" = "U" 
-- #test implementation "quick" = "i"
-- #test implementation "ab" = ""