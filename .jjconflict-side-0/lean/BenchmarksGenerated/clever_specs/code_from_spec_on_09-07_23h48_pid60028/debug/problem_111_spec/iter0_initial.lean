def problem_spec
-- function signature
(implementation: String → Std.HashMap Char Nat)
-- inputs
(s: String) :=
-- spec
let spec (result : Std.HashMap Char Nat) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ key ∈ result.keys,
      (key.isLower ∧
      key ∈ s.data ∧
      result.get! key = s.count key) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      s.count char < s.count char2) ↔ char ∉ result.keys))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def get_max_count (s: String) : Nat :=
  s.data.foldl (fun acc c => if c.isLower then max acc (s.count c) else acc) 0

-- LLM HELPER
def get_chars_with_max_count (s: String) : List Char :=
  let max_count := get_max_count s
  s.data.filter (fun c => c.isLower ∧ s.count c = max_count)

def implementation (s: String) : Std.HashMap Char Nat :=
  let max_count := get_max_count s
  let chars_with_max := get_chars_with_max_count s
  chars_with_max.foldl (fun acc c => acc.insert c (s.count c)) Std.HashMap.empty

-- LLM HELPER
lemma get_max_count_correct (s: String) : 
  ∀ c ∈ s.data, c.isLower → s.count c ≤ get_max_count s := by
  intro c hc_in hc_lower
  unfold get_max_count
  sorry

-- LLM HELPER
lemma get_chars_with_max_count_correct (s: String) :
  ∀ c, c ∈ get_chars_with_max_count s ↔ 
    (c ∈ s.data ∧ c.isLower ∧ s.count c = get_max_count s) := by
  intro c
  unfold get_chars_with_max_count
  sorry

-- LLM HELPER
lemma implementation_keys_correct (s: String) :
  ∀ c, c ∈ (implementation s).keys ↔ 
    (c ∈ s.data ∧ c.isLower ∧ 
     ∀ c2 ∈ s.data, c2.isLower → s.count c2 ≤ s.count c) := by
  intro c
  unfold implementation
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h
    constructor
    · intro key hkey
      constructor
      · have h_key := implementation_keys_correct s
        rw [h_key] at hkey
        exact hkey.2.1
      · constructor
        · have h_key := implementation_keys_correct s
          rw [h_key] at hkey
          exact hkey.1
        · unfold implementation
          sorry
    · intro char hchar_in hchar_lower
      constructor
      · intro h_exists
        obtain ⟨char2, hchar2_in, hchar2_lower, hchar2_ne, hchar2_count⟩ := h_exists
        have h_key := implementation_keys_correct s
        rw [h_key]
        push_neg
        use char2
        exact ⟨hchar2_in, hchar2_lower, Nat.not_le.mpr hchar2_count⟩
      · intro hchar_not_in
        have h_key := implementation_keys_correct s
        rw [h_key] at hchar_not_in
        push_neg at hchar_not_in
        obtain ⟨char2, hchar2_in, hchar2_lower, hchar2_count⟩ := hchar_not_in hchar_in hchar_lower
        use char2
        constructor
        · exact hchar2_in
        · constructor
          · exact hchar2_lower
          · constructor
            · intro heq
              rw [heq] at hchar2_count
              exact Nat.lt_irrefl _ hchar2_count
            · exact hchar2_count