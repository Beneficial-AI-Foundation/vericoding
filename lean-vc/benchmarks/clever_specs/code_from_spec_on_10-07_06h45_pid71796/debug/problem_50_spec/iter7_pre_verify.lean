def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s : String) : Prop :=
let isAlphabetic (string: String) : Prop :=
∀ i, i < string.length →
let c := string.get ⟨i⟩;
('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)
-- spec
let spec (result: String) :=
isAlphabetic result ∧ isAlphabetic s ∧
result.length = s.length ∧
∃ k : Nat, k < 26 ∧
∀ i : Nat, i < s.length →
((s.get ⟨i⟩).toNat + k) % 26 = (result.get ⟨i⟩).toNat % 26 →
k = 5
-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
def shiftChar (c : Char) : Char :=
if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat then
  Char.ofNat (((c.toNat - 'a'.toNat + 5) % 26) + 'a'.toNat)
else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then
  Char.ofNat (((c.toNat - 'A'.toNat + 5) % 26) + 'A'.toNat)
else
  c

def implementation (s: String) : String := 
s.map shiftChar

-- LLM HELPER
lemma shiftChar_preserves_alphabetic (c : Char) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shiftChar c).toNat ∧ (shiftChar c).toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ (shiftChar c).toNat ∧ (shiftChar c).toNat ≤ 'Z'.toNat)) :=
by
  intro h
  simp [shiftChar]
  cases h with
  | inl h_lower =>
    simp [h_lower]
    left
    constructor
    · simp [Char.ofNat_toNat]
      have h1 : c.toNat - 'a'.toNat < 26 := by
        have : c.toNat ≤ 'z'.toNat := h_lower.2
        omega
      have h2 : (c.toNat - 'a'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
    · simp [Char.ofNat_toNat]
      have h1 : c.toNat - 'a'.toNat < 26 := by
        have : c.toNat ≤ 'z'.toNat := h_lower.2
        omega
      have h2 : (c.toNat - 'a'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
  | inr h_upper =>
    simp [h_upper]
    right
    constructor
    · simp [Char.ofNat_toNat]
      have h1 : c.toNat - 'A'.toNat < 26 := by
        have : c.toNat ≤ 'Z'.toNat := h_upper.2
        omega
      have h2 : (c.toNat - 'A'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
    · simp [Char.ofNat_toNat]
      have h1 : c.toNat - 'A'.toNat < 26 := by
        have : c.toNat ≤ 'Z'.toNat := h_upper.2
        omega
      have h2 : (c.toNat - 'A'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega

-- LLM HELPER
lemma map_preserves_length (s : String) :
  (s.map shiftChar).length = s.length :=
by
  simp [String.map]

-- LLM HELPER
lemma map_preserves_alphabetic (s : String) :
  (∀ i, i < s.length → let c := s.get ⟨i⟩; ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (s.map shiftChar).length → let c := (s.map shiftChar).get ⟨i⟩; ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) :=
by
  intro h i hi
  simp [map_preserves_length] at hi
  simp [String.map_get]
  have h_orig := h i hi
  exact shiftChar_preserves_alphabetic (s.get ⟨i⟩) h_orig

-- LLM HELPER
lemma shiftChar_shift_5 (c : Char) :
  ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat) →
  (c.toNat + 5) % 26 = (shiftChar c).toNat % 26 :=
by
  intro h
  simp [shiftChar]
  cases h with
  | inl h_lower =>
    simp [h_lower]
    simp [Char.ofNat_toNat]
    rw [Nat.add_mod]
    simp [Nat.mod_mod]
  | inr h_upper =>
    simp [h_upper]
    simp [Char.ofNat_toNat]
    rw [Nat.add_mod]
    simp [Nat.mod_mod]

theorem correctness
(s: String)
: problem_spec implementation s := by
  simp [problem_spec]
  let isAlphabetic := fun string => ∀ i, i < string.length → let c := string.get ⟨i⟩; (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90)
  let spec := fun result => isAlphabetic result ∧ isAlphabetic s ∧ result.length = s.length ∧ ∃ k : Nat, k < 26 ∧ ∀ i : Nat, i < s.length → ((s.get ⟨i⟩).toNat + k) % 26 = (result.get ⟨i⟩).toNat % 26 → k = 5
  use s.map shiftChar
  constructor
  · simp [implementation]
  · constructor
    · exact map_preserves_alphabetic s
    · constructor
      · assumption
      · constructor
        · exact map_preserves_length s
        · use 5
          constructor
          · norm_num
          · intro i hi h_eq
            by_cases h : (97 ≤ (s.get ⟨i⟩).toNat ∧ (s.get ⟨i⟩).toNat ≤ 122) ∨ (65 ≤ (s.get ⟨i⟩).toNat ∧ (s.get ⟨i⟩).toNat ≤ 90)
            · have h_shift := shiftChar_shift_5 (s.get ⟨i⟩) h
              simp [String.map_get] at h_eq
              rw [←h_shift] at h_eq
              rfl
            · simp [String.map_get] at h_eq
              simp [shiftChar] at h_eq
              simp [h] at h_eq
              rfl