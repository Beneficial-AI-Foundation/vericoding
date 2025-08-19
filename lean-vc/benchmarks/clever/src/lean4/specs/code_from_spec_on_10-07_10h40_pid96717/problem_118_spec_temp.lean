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

-- LLM HELPER
def is_consonant (c: Char) : Bool :=
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha

-- LLM HELPER
def has_consonant_after (s: String) (start: Nat) : Bool :=
  let rec aux (i: Nat) : Bool :=
    if i >= s.length then
      false
    else if is_consonant s.data[i]! then
      true
    else
      aux (i + 1)
  aux start

-- LLM HELPER
def find_first_vowel_between_consonants (s: String) : Option (Nat × Char) :=
  let rec find_aux (i: Nat) (prev_consonant: Bool) : Option (Nat × Char) :=
    if i >= s.length then
      none
    else
      let c := s.data[i]!
      if is_consonant c then
        find_aux (i + 1) true
      else if prev_consonant ∧ ¬is_consonant c ∧ c.isAlpha then
        if has_consonant_after s (i + 1) then
          some (i, c)
        else
          find_aux (i + 1) false
      else
        find_aux (i + 1) false
  find_aux 0 false

def implementation (s: String) : String :=
  match find_first_vowel_between_consonants s with
  | none => ""
  | some (_, c) => String.mk [c]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let spec := fun result => 
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
  
  cases h : find_first_vowel_between_consonants s with
  | none => 
    use ""
    constructor
    · simp [h]
    · intro h_alpha
      constructor
      · intro h_empty
        classical
        by_contra h_exists
        obtain ⟨i, j, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k⟩ := h_exists
        have : ∃ (idx : Nat) (c : Char), find_first_vowel_between_consonants s = some (idx, c) := by
          unfold find_first_vowel_between_consonants
          simp
          exact Classical.choose_spec (Classical.choose_spec (Exists.intro i (Exists.intro j (Exists.intro k ⟨hi, hj, hk, hcons_i, hvowel_j, hcons_k⟩))))
        rw [h] at this
        exact this ⟨0, '!', rfl⟩
      · intro h_nempty
        contradiction
  | some p =>
    cases p with
    | mk j c =>
      use String.mk [c]
      constructor
      · simp [h]
      · intro h_alpha
        constructor
        · intro h_empty
          simp at h_empty
        · intro h_nempty
          simp
          constructor
          · rfl
          · constructor
            · simp
              classical
              use ⟨j, by
                unfold find_first_vowel_between_consonants at h
                simp at h
                exact Classical.choose_spec (Classical.choose_spec h)⟩
            · constructor
              · simp
                classical
                exact Classical.choose_spec (Classical.choose_spec h)
              · simp
                classical
                obtain ⟨i, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k⟩ := Classical.choose_spec (Classical.choose_spec h)
                use i, j, k
                constructor
                · exact hi
                · constructor
                  · exact hj
                  · constructor
                    · exact hk
                    · constructor
                      · simp
                        exact hcons_i
                      · constructor
                        · simp
                          exact hvowel_j
                        · constructor
                          · simp
                            exact hcons_k
                          · constructor
                            · simp
                            · intros i' j' k' hi' hj' hk' hcons_i' hvowel_j' hcons_k'
                              simp
                              exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))