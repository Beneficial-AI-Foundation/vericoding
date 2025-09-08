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
    Char.ofNat (c.val.toNat + 2)
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
      c.isUpper → c'.val.toNat = c.toLower.val.toNat + 2 ∧
      c.isLower → c'.val.toNat = c.toUpper.val.toNat + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma list_map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  rw [List.length_map]

-- LLM HELPER
lemma string_data_length (s : String) : s.data.length = s.length := by
  rw [String.length]

-- LLM HELPER  
lemma string_mk_data_get (l : List Char) (i : Nat) (h : i < l.length) :
  (String.mk l).data[i]! = l[i]! := by
  rw [String.mk_data]

-- LLM HELPER
lemma list_get_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.getElem!_map]

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
    · rw [String.length_mk, list_map_length, ← string_data_length]
    · intro i h_bound
      rw [implementation]
      have h1 : (String.mk (s.data.map transformChar)).data = s.data.map transformChar := by rw [String.mk_data]
      have h2 : (String.mk (s.data.map transformChar)).data[i]! = (s.data.map transformChar)[i]! := by
        rw [h1]
      rw [h2]
      have h3 : (s.data.map transformChar)[i]! = transformChar (s.data[i]!) := by
        rw [List.getElem!_map]
      rw [h3]
      let c := s.data[i]!
      have h_char_alpha := List.all_getElem h_alpha h_bound
      by_cases h_vowel : isVowel c
      · rw [transformChar, if_pos h_vowel]
        unfold isVowel at h_vowel
        simp only [Bool.or_eq_true] at h_vowel
        cases h_vowel with
        | inl h => 
          rw [h]
          constructor
          · intro h_upper
            simp [Char.isUpper] at h_upper
          · intro h_lower
            simp [Char.isLower, Char.toUpper] 
            rfl
        | inr h =>
          cases h with
          | inl h =>
            rw [h]
            constructor
            · intro h_upper
              simp [Char.isUpper] at h_upper
            · intro h_lower
              simp [Char.isLower, Char.toUpper]
              rfl
          | inr h =>
            cases h with
            | inl h =>
              rw [h]
              constructor
              · intro h_upper
                simp [Char.isUpper] at h_upper
              · intro h_lower
                simp [Char.isLower, Char.toUpper]
                rfl
            | inr h =>
              cases h with
              | inl h =>
                rw [h]
                constructor
                · intro h_upper
                  simp [Char.isUpper] at h_upper
                · intro h_lower
                  simp [Char.isLower, Char.toUpper]
                  rfl
              | inr h =>
                cases h with
                | inl h =>
                  rw [h]
                  constructor
                  · intro h_upper
                    simp [Char.isUpper] at h_upper
                  · intro h_lower
                    simp [Char.isLower, Char.toUpper]
                    rfl
                | inr h =>
                  cases h with
                  | inl h =>
                    rw [h]
                    constructor
                    · intro h_upper
                      simp [Char.isUpper, Char.toLower]
                      rfl
                    · intro h_lower
                      simp [Char.isLower] at h_lower
                  | inr h =>
                    cases h with
                    | inl h =>
                      rw [h]
                      constructor
                      · intro h_upper
                        simp [Char.isUpper, Char.toLower]
                        rfl
                      · intro h_lower
                        simp [Char.isLower] at h_lower
                    | inr h =>
                      cases h with
                      | inl h =>
                        rw [h]
                        constructor
                        · intro h_upper
                          simp [Char.isUpper, Char.toLower]
                          rfl
                        · intro h_lower
                          simp [Char.isLower] at h_lower
                      | inr h =>
                        cases h with
                        | inl h =>
                          rw [h]
                          constructor
                          · intro h_upper
                            simp [Char.isUpper, Char.toLower]
                            rfl
                          · intro h_lower
                            simp [Char.isLower] at h_lower
                        | inr h =>
                          rw [h]
                          constructor
                          · intro h_upper
                            simp [Char.isUpper] at h_upper
                          · intro h_lower
                            simp [Char.isLower, Char.toUpper]
                            rfl
      · rw [transformChar, if_neg h_vowel, swapCase]
        split
        · next h_upper =>
          constructor
          · intro h_upper_eq
            rw [Char.toLower]
            rfl
          · intro h_lower
            simp [Char.isUpper] at h_lower
            contradiction
        · next h_not_upper =>
          constructor  
          · intro h_upper
            contradiction
          · intro h_lower
            rw [Char.toUpper]
            rfl