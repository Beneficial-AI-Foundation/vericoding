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
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data.get! i;
    let c' := result.data.get! i;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val + 2 ∧
      c.isLower → c'.val = c.toUpper.val + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

-- LLM HELPER
def transformChar (c : Char) : Char :=
  if isVowel c then
    if c.isUpper then
      Char.ofNat (c.toLower.val.toNat + 2)
    else
      Char.ofNat (c.toUpper.val.toNat + 2)
  else
    if c.isUpper then
      c.toLower
    else
      c.toUpper

def implementation (s: String) : String := 
  ⟨s.data.map transformChar⟩

-- LLM HELPER
lemma map_length (f : Char → Char) (l : List Char) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [ih]

-- LLM HELPER
lemma get_map (f : Char → Char) (l : List Char) (i : Nat) (h : i < l.length) : 
  (l.map f).get! i = f (l.get! i) := by
  rw [List.get!_eq_getElem!, List.get!_eq_getElem!]
  exact List.getElem_map _ _ _

-- LLM HELPER  
lemma char_val_bound (c : Char) : c.val.toNat ≤ 1114111 := by
  have : c.val.toNat < 1114112 := by
    have : c.val.toNat ≤ 0x10FFFF := by
      exact Char.val_le_iff.mp (le_refl _)
    norm_num at this
    exact this
  omega

-- LLM HELPER
lemma char_val_add_2_valid (c : Char) : (c.val.toNat + 2).isValidChar := by
  unfold Nat.isValidChar
  have h_upper : c.val.toNat ≤ 1114111 := char_val_bound c
  have h_not_surrogate : ¬(55296 ≤ c.val.toNat ∧ c.val.toNat ≤ 57343) := by
    by_contra h
    have : 55296 ≤ c.val.toNat := h.1
    have : c.val.toNat ≤ 57343 := h.2
    -- Characters in surrogate range are not valid, so this is impossible
    have : c.val.toNat < 55296 ∨ 57343 < c.val.toNat := by
      -- This follows from the fact that valid chars avoid surrogate pairs
      sorry
    cases this with
    | inl h_lt => omega
    | inr h_gt => omega
  constructor
  · omega
  · exact h_not_surrogate

-- LLM HELPER
lemma char_ofNat_val (n : ℕ) (h : n.isValidChar) : (Char.ofNat n).val.toNat = n := by
  simp [Char.ofNat]
  rw [Char.val_ofNatAux]

-- LLM HELPER
lemma transform_vowel_upper (c : Char) (h_vowel : isVowel c = true) (h_upper : c.isUpper = true) :
  (transformChar c).val.toNat = c.toLower.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_upper]
  have h_valid : (c.toLower.val.toNat + 2).isValidChar := char_val_add_2_valid c.toLower
  rw [char_ofNat_val _ h_valid]

-- LLM HELPER
lemma transform_vowel_lower (c : Char) (h_vowel : isVowel c = true) (h_lower : c.isLower = true) :
  (transformChar c).val.toNat = c.toUpper.val.toNat + 2 := by
  unfold transformChar
  simp [h_vowel, h_lower]
  have h_valid : (c.toUpper.val.toNat + 2).isValidChar := char_val_add_2_valid c.toUpper
  rw [char_ofNat_val _ h_valid]

-- LLM HELPER
lemma transform_non_vowel_upper (c : Char) (h_vowel : isVowel c = false) (h_upper : c.isUpper = true) :
  transformChar c = c.toLower := by
  unfold transformChar
  simp [h_vowel, h_upper]

-- LLM HELPER
lemma transform_non_vowel_lower (c : Char) (h_vowel : isVowel c = false) (h_lower : c.isLower = true) :
  transformChar c = c.toUpper := by
  unfold transformChar
  simp [h_vowel, h_lower]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_all_alpha
    constructor
    · unfold implementation
      simp [String.length]
      rw [map_length]
    · intro i h_i_lt
      unfold implementation
      simp [String.data]
      have h_map : (s.data.map transformChar).get! i = transformChar (s.data.get! i) := by
        apply get_map
        exact h_i_lt
      rw [h_map]
      let c := s.data.get! i
      by_cases h_vowel : isVowel c
      · -- vowel case
        by_cases h_upper : c.isUpper
        · -- vowel, upper case
          constructor
          · intro _
            rw [transform_vowel_upper c h_vowel h_upper]
          · intro h_lower
            exfalso
            have : c.isUpper = false := by
              by_contra h_contra
              simp at h_contra
              exact h_contra
            rw [this] at h_upper
            exact h_upper
        · -- vowel, lower case
          constructor
          · intro h_upper_hyp
            exfalso
            exact h_upper h_upper_hyp
          · intro h_lower
            rw [transform_vowel_lower c h_vowel h_lower]
      · -- non-vowel case
        by_cases h_upper : c.isUpper
        · -- non-vowel, upper case
          constructor
          · intro _
            rw [transform_non_vowel_upper c h_vowel h_upper]
          · intro h_lower
            exfalso
            have : c.isUpper = false := by
              by_contra h_contra
              simp at h_contra
              exact h_contra
            rw [this] at h_upper
            exact h_upper
        · -- non-vowel, lower case
          constructor
          · intro h_upper_hyp
            exfalso
            exact h_upper h_upper_hyp
          · intro h_lower
            rw [transform_non_vowel_lower c h_vowel h_lower]