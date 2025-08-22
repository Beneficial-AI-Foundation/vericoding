def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s : String) :=
let isAlphabetic (string: String) : Bool :=
∀ i, i < string.length →
let c := string.get! ⟨i⟩;
('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)
-- spec
let spec (result: String) :=
isAlphabetic result ∧ isAlphabetic s ∧
result.length = s.length ∧
∃ k : Nat, k < 26 ∧
∀ i : Nat, i < s.length →
((s.get! ⟨i⟩).toNat + k) % 26 = (result.get! ⟨i⟩).toNat
→ k = 5
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
  String.mk (s.data.map shiftChar)

-- LLM HELPER
lemma shiftChar_preserves_alphabetic (c : Char) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shiftChar c).toNat ∧ (shiftChar c).toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ (shiftChar c).toNat ∧ (shiftChar c).toNat ≤ 'Z'.toNat)) := by
  intro h
  unfold shiftChar
  cases h with
  | inl h_lower =>
    simp only [h_lower, if_true]
    left
    constructor
    · simp [Char.ofNat_toNat]
      have : (c.toNat - 'a'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
    · simp [Char.ofNat_toNat]
      have : (c.toNat - 'a'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
  | inr h_upper =>
    simp only [h_upper, if_false, if_true]
    right
    constructor
    · simp [Char.ofNat_toNat]
      have : (c.toNat - 'A'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega
    · simp [Char.ofNat_toNat]
      have : (c.toNat - 'A'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      omega

-- LLM HELPER
lemma implementation_length (s : String) :
  (implementation s).length = s.length := by
  unfold implementation
  simp [String.length_mk]

-- LLM HELPER
lemma implementation_preserves_alphabetic (s : String) :
  (∀ i, i < s.length →
    let c := s.get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (implementation s).length →
    let c := (implementation s).get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) := by
  intro h i hi
  rw [implementation_length] at hi
  unfold implementation
  simp [String.get!_mk]
  have : i < s.data.length := by simp [String.length] at hi; exact hi
  simp [List.get!_map]
  apply shiftChar_preserves_alphabetic
  have : s.get! ⟨i⟩ = s.data.get! i := by simp [String.get!]
  rw [← this]
  exact h i hi

-- LLM HELPER
lemma shift_property_correct (c : Char) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (c.toNat + 5) % 26 = (shiftChar c).toNat % 26 := by
  intro h
  unfold shiftChar
  cases h with
  | inl h_lower =>
    simp only [h_lower, if_true]
    rw [Char.ofNat_toNat]
    ring_nf
    simp [Nat.add_mod]
  | inr h_upper =>
    simp only [h_upper, if_false, if_true]
    rw [Char.ofNat_toNat] 
    ring_nf
    simp [Nat.add_mod]

-- LLM HELPER
lemma key_property (s : String) (i : Nat) (hi : i < s.length) :
  ((s.get! ⟨i⟩).toNat + 5) % 26 = ((implementation s).get! ⟨i⟩).toNat →
  ('a'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'z'.toNat) ∨
  ('A'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'Z'.toNat) := by
  intro h_eq
  unfold implementation at h_eq
  simp [String.get!_mk, List.get!_map] at h_eq
  unfold shiftChar at h_eq
  by_cases h_lower : 'a'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'z'.toNat
  · left; exact h_lower
  · by_cases h_upper : 'A'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'Z'.toNat
    · right; exact h_upper
    · simp [h_lower, h_upper] at h_eq
      have : (s.get! ⟨i⟩).toNat + 5 = (s.get! ⟨i⟩).toNat := by
        rw [← Nat.mod_eq_of_lt] at h_eq
        · exact h_eq
        · norm_num
      omega

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  simp
  use implementation s
  constructor
  · rfl
  · constructor
    · intro h
      exact implementation_preserves_alphabetic s h
    · constructor
      · intro h
        exact h
      · constructor
        · exact implementation_length s
        · use 5
          constructor
          · norm_num
          · intro i hi h_eq
            rfl