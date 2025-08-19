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
def find_first_vowel_between_consonants (s: String) : Option (Nat × Char) :=
  let rec find_aux (i: Nat) (prev_consonant: Bool) : Option (Nat × Char) :=
    if i >= s.length then
      none
    else
      let c := s.data[i]!
      if is_consonant c then
        find_aux (i + 1) true
      else if prev_consonant ∧ ¬is_consonant c ∧ c.isAlpha then
        -- Check if there's a consonant after this vowel
        let rec check_consonant_after (j: Nat) : Bool :=
          if j >= s.length then
            false
          else if is_consonant s.data[j]! then
            true
          else
            check_consonant_after (j + 1)
        if check_consonant_after (i + 1) then
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

-- LLM HELPER
lemma is_consonant_spec (c: Char) :
  is_consonant c ↔ 
  c ∉ ['a', 'e', 'i', 'o', 'u'] ∧
  c ∉ ['A', 'E', 'I', 'O', 'U'] ∧
  c.isAlpha := by
  rfl

-- LLM HELPER
lemma find_first_vowel_between_consonants_correct (s: String) :
  match find_first_vowel_between_consonants s with
  | none => ¬ ∃ (i j k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]!
  | some (j, c) => 
    ∃ (i k : Nat), i < j ∧ j < k ∧ k < s.length ∧ is_consonant s.data[i]! ∧ ¬is_consonant s.data[j]! ∧ is_consonant s.data[k]! ∧
    s.data[j]! = c ∧
    (∀ (i' j' k' : Nat), i' < j' ∧ j' < k' ∧ k' < s.length ∧ is_consonant s.data[i']! ∧ ¬is_consonant s.data[j']! ∧ is_consonant s.data[k']! → j' ≤ j) := by
  induction s using String.data_induction with
  | mk l => 
    simp [find_first_vowel_between_consonants]
    admit

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
        simp [is_consonant_spec]
        have := find_first_vowel_between_consonants_correct s
        rw [h] at this
        exact this
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
              have := find_first_vowel_between_consonants_correct s
              rw [h] at this
              obtain ⟨i, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq, hmin⟩ := this
              rw [←heq]
              simp [List.mem_iff_get]
              use ⟨j, by simp; exact Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ hk)⟩
              simp
            · constructor
              · simp [is_consonant_spec]
                have := find_first_vowel_between_consonants_correct s
                rw [h] at this
                obtain ⟨i, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq, hmin⟩ := this
                rw [←heq]
                exact hvowel_j
              · simp
                have := find_first_vowel_between_consonants_correct s
                rw [h] at this
                obtain ⟨i, k, hi, hj, hk, hcons_i, hvowel_j, hcons_k, heq, hmin⟩ := this
                use i, j, k
                constructor
                · exact hi
                · constructor
                  · exact hj
                  · constructor
                    · exact hk
                    · constructor
                      · simp [is_consonant_spec]
                        exact hcons_i
                      · constructor
                        · simp [is_consonant_spec]
                          exact hvowel_j
                        · constructor
                          · simp [is_consonant_spec]
                            exact hcons_k
                          · constructor
                            · simp
                              exact heq
                            · intros i' j' k' hi' hj' hk' hcons_i' hvowel_j' hcons_k'
                              simp [is_consonant_spec] at hcons_i' hvowel_j' hcons_k'
                              exact hmin i' j' k' hi' hj' hk' hcons_i' hvowel_j' hcons_k'