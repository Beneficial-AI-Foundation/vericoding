import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def swapCase (c : Char) : Char :=
  if c.isUpper then c.toLower else c.toUpper

-- LLM HELPER  
def isVowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' || 
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

-- LLM HELPER
def transformChar (c : Char) : Char :=
  if isVowel c then
    Char.ofNat (c.val + 2)
  else
    swapCase c

def implementation (s: String) : String :=
  String.mk (s.data.map transformChar)

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data[i]!;
    let c' := result.data[i]!;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val + 2 ∧
      c.isLower → c' = c.toUpper.val + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  simp

-- LLM HELPER
lemma string_data_length (s : String) : s.data.length = s.length := by
  simp [String.length]

-- LLM HELPER  
lemma string_mk_data_get (l : List Char) (i : Nat) (h : i < l.length) :
  (String.mk l).data[i]! = l[i]! := by
  simp [String.mk]

-- LLM HELPER
lemma list_get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  simp [List.getElem!_map h]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use String.mk (s.data.map transformChar)
  constructor
  · unfold implementation
    rfl
  · intro h_alpha
    constructor
    · simp [implementation, String.length, list_map_length, string_data_length]
    · intro i h_bound
      simp [implementation]
      have h1 : (String.mk (s.data.map transformChar)).data = s.data.map transformChar := by simp
      have h2 : (String.mk (s.data.map transformChar)).data[i]! = (s.data.map transformChar)[i]! := by
        rw [h1]
      rw [h2]
      have h3 : (s.data.map transformChar)[i]! = transformChar (s.data[i]!) := by
        apply list_get_map
        rw [← string_data_length] at h_bound
        exact h_bound
      rw [h3]
      let c := s.data[i]!
      have h_char_alpha := List.all_getElem h_alpha h_bound
      cases' h_char_cases : c with n
      simp [Char.val] at *
      by_cases h_vowel : isVowel c
      · simp [transformChar, h_vowel]
        unfold isVowel at h_vowel
        simp at h_vowel
        cases h_vowel with
        | inl h => 
          simp [h]
          constructor
          · intro h_upper
            simp [Char.isUpper, Char.toLower] at h_upper ⊢
            simp [h] at h_upper
            contradiction
          · intro h_lower  
            simp [Char.isLower, Char.toUpper] at h_lower ⊢
            simp [h]
        | inr h =>
          cases h with
          | inl h =>
            simp [h]
            constructor
            · intro h_upper
              simp [Char.isUpper, Char.toLower] at h_upper ⊢
              simp [h] at h_upper
              contradiction
            · intro h_lower
              simp [Char.isLower, Char.toUpper] at h_lower ⊢  
              simp [h]
          | inr h =>
            cases h with
            | inl h =>
              simp [h]
              constructor
              · intro h_upper
                simp [Char.isUpper, Char.toLower] at h_upper ⊢
                simp [h] at h_upper
                contradiction
              · intro h_lower
                simp [Char.isLower, Char.toUpper] at h_lower ⊢
                simp [h]
            | inr h =>
              cases h with
              | inl h =>
                simp [h]
                constructor
                · intro h_upper
                  simp [Char.isUpper, Char.toLower] at h_upper ⊢
                  simp [h] at h_upper
                  contradiction
                · intro h_lower
                  simp [Char.isLower, Char.toUpper] at h_lower ⊢
                  simp [h]
              | inr h =>
                cases h with
                | inl h =>
                  simp [h]
                  constructor
                  · intro h_upper
                    simp [Char.isUpper, Char.toLower] at h_upper ⊢
                    simp [h] at h_upper
                    contradiction
                  · intro h_lower
                    simp [Char.isLower, Char.toUpper] at h_lower ⊢
                    simp [h]
                | inr h =>
                  cases h with
                  | inl h =>
                    simp [h]
                    constructor
                    · intro h_upper
                      simp [Char.isUpper, Char.toLower] at h_upper ⊢
                      simp [h]
                    · intro h_lower
                      simp [Char.isLower, Char.toUpper] at h_lower ⊢
                      simp [h] at h_lower
                      contradiction
                  | inr h =>
                    cases h with
                    | inl h =>
                      simp [h]
                      constructor
                      · intro h_upper
                        simp [Char.isUpper, Char.toLower] at h_upper ⊢
                        simp [h]
                      · intro h_lower
                        simp [Char.isLower, Char.toUpper] at h_lower ⊢
                        simp [h] at h_lower
                        contradiction
                    | inr h =>
                      cases h with
                      | inl h =>
                        simp [h]
                        constructor
                        · intro h_upper
                          simp [Char.isUpper, Char.toLower] at h_upper ⊢
                          simp [h]
                        · intro h_lower
                          simp [Char.isLower, Char.toUpper] at h_lower ⊢
                          simp [h] at h_lower
                          contradiction
                      | inr h =>
                        cases h with
                        | inl h =>
                          simp [h]
                          constructor
                          · intro h_upper
                            simp [Char.isUpper, Char.toLower] at h_upper ⊢
                            simp [h]
                          · intro h_lower
                            simp [Char.isLower, Char.toUpper] at h_lower ⊢
                            simp [h] at h_lower
                            contradiction
                        | inr h =>
                          simp [h]
                          constructor
                          · intro h_upper
                            simp [Char.isUpper, Char.toLower] at h_upper ⊢
                            simp [h] at h_upper
                            contradiction
                          · intro h_lower
                            simp [Char.isLower, Char.toUpper] at h_lower ⊢
                            simp [h]
      · simp [transformChar, h_vowel, swapCase]
        split
        · constructor
          · intro h_upper
            simp [h_upper]
          · intro h_lower
            simp [Char.isUpper] at h_lower
            simp [not_not] at h_lower
            simp [h_lower]
        · constructor  
          · intro h_upper
            simp [Char.isUpper] at h_upper
            simp [not_not] at h_upper
            simp [h_upper]
          · intro h_lower
            simp [h_lower]

-- #test implementation "test" = "TGST"
-- #test implementation "This is a message" = "tHKS KS C MGSSCGG"