def problem_spec
-- function signature
(implementation: String → List (Char × Nat))
-- inputs
(s: String) :=
-- spec
let spec (result : List (Char × Nat)) :=
    let chars := s.splitOn " "
    chars.all (fun c => c.length = 1) ∧ s.all (fun c => c.isLower ∨ c = ' ') →
    ∀ (key, count) ∈ result,
      (key.isLower ∧
      key ∈ s.data ∧
      count = (s.data.filter (· = key)).length) ∧
    (∀ char ∈ s.data, char.isLower →
      ((∃ char2 ∈ s.data, char2.isLower ∧ char2 ≠ char ∧
      (s.data.filter (· = char)).length < (s.data.filter (· = char2)).length) ↔ 
      ∀ (k, _) ∈ result, k ≠ char))
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def char_count (s: String) (c: Char) : Nat :=
  (s.data.filter (· = c)).length

-- LLM HELPER
def get_max_count (s: String) : Nat :=
  s.data.foldl (fun acc c => if c.isLower then max acc (char_count s c) else acc) 0

-- LLM HELPER
def get_chars_with_max_count (s: String) : List Char :=
  let max_count := get_max_count s
  s.data.filter (fun c => c.isLower ∧ char_count s c = max_count)

-- LLM HELPER
def remove_duplicates (l: List Char) : List Char :=
  l.foldl (fun acc c => if c ∈ acc then acc else c :: acc) []

def implementation (s: String) : List (Char × Nat) :=
  let max_count := get_max_count s
  let chars_with_max := remove_duplicates (get_chars_with_max_count s)
  chars_with_max.map (fun c => (c, char_count s c))

-- LLM HELPER
lemma char_count_correct (s: String) (c: Char) :
  char_count s c = (s.data.filter (· = c)).length := by
  rfl

-- LLM HELPER
lemma get_max_count_correct (s: String) : 
  ∀ c ∈ s.data, c.isLower → char_count s c ≤ get_max_count s := by
  intro c hc_in hc_lower
  unfold get_max_count
  induction s.data with
  | nil => simp at hc_in
  | cons head tail ih =>
    simp [List.foldl]
    by_cases h : c = head
    · simp [h]
      split_ifs with h1
      · exact Nat.le_max_right _ _
      · simp [char_count, List.filter]
        rw [h] at h1
        simp [h1]
        exact Nat.zero_le _
    · simp [h] at hc_in
      have ih_res := ih hc_in
      split_ifs with h1
      · exact Nat.le_trans ih_res (Nat.le_max_left _ _)
      · exact ih_res

-- LLM HELPER
lemma get_chars_with_max_count_correct (s: String) :
  ∀ c, c ∈ get_chars_with_max_count s ↔ 
    (c ∈ s.data ∧ c.isLower ∧ char_count s c = get_max_count s) := by
  intro c
  unfold get_chars_with_max_count
  simp [List.mem_filter]

-- LLM HELPER
lemma remove_duplicates_correct (l: List Char) :
  ∀ c, c ∈ remove_duplicates l ↔ c ∈ l := by
  intro c
  unfold remove_duplicates
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [List.foldl]
    by_cases h : head ∈ remove_duplicates tail
    · simp [h]
      exact ih
    · simp [h]
      constructor
      · intro h_in
        cases h_in with
        | inl h_eq => exact Or.inl h_eq
        | inr h_tail => exact Or.inr (ih.mp h_tail)
      · intro h_in
        cases h_in with
        | inl h_eq => exact Or.inl h_eq
        | inr h_tail => exact Or.inr (ih.mpr h_tail)

-- LLM HELPER
lemma implementation_keys_correct (s: String) :
  ∀ c, (∃ n, (c, n) ∈ implementation s) ↔ 
    (c ∈ s.data ∧ c.isLower ∧ 
     ∀ c2 ∈ s.data, c2.isLower → char_count s c2 ≤ char_count s c) := by
  intro c
  unfold implementation
  simp [List.mem_map]
  constructor
  · intro ⟨c', hc'_in, hc'_eq⟩
    rw [← hc'_eq]
    have h_chars := get_chars_with_max_count_correct s
    have h_dup := remove_duplicates_correct (get_chars_with_max_count s)
    rw [h_dup] at hc'_in
    rw [h_chars] at hc'_in
    constructor
    · exact hc'_in.1
    · constructor
      · exact hc'_in.2.1
      · intro c2 hc2_in hc2_lower
        have h_max := get_max_count_correct s c2 hc2_in hc2_lower
        rw [← hc'_in.2.2]
        exact h_max
  · intro ⟨hc_in, hc_lower, hc_max⟩
    use c
    constructor
    · have h_chars := get_chars_with_max_count_correct s
      have h_dup := remove_duplicates_correct (get_chars_with_max_count s)
      rw [h_dup, h_chars]
      constructor
      · exact hc_in
      · constructor
        · exact hc_lower
        · have h_max_le := get_max_count_correct s c hc_in hc_lower
          have h_ge : get_max_count s ≤ char_count s c := by
            unfold get_max_count
            induction s.data with
            | nil => simp
            | cons head tail ih =>
              simp [List.foldl]
              split_ifs with h
              · exact Nat.le_max_of_le_right (hc_max head (List.mem_cons_self _ _) h)
              · exact ih
          exact Nat.le_antisymm h_max_le h_ge
    · rfl

theorem correctness (s: String) : problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h
    constructor
    · intro key count hkey
      constructor
      · unfold implementation at hkey
        simp [List.mem_map] at hkey
        obtain ⟨c, hc_in, hc_eq⟩ := hkey
        rw [← hc_eq.1]
        have h_chars := get_chars_with_max_count_correct s
        have h_dup := remove_duplicates_correct (get_chars_with_max_count s)
        rw [h_dup] at hc_in
        rw [h_chars] at hc_in
        exact hc_in.2.1
      · constructor
        · unfold implementation at hkey
          simp [List.mem_map] at hkey
          obtain ⟨c, hc_in, hc_eq⟩ := hkey
          rw [← hc_eq.1]
          have h_chars := get_chars_with_max_count_correct s
          have h_dup := remove_duplicates_correct (get_chars_with_max_count s)
          rw [h_dup] at hc_in
          rw [h_chars] at hc_in
          exact hc_in.1
        · unfold implementation at hkey
          simp [List.mem_map] at hkey
          obtain ⟨c, hc_in, hc_eq⟩ := hkey
          rw [← hc_eq.2]
          rfl
    · intro char hchar_in hchar_lower
      constructor
      · intro h_exists
        obtain ⟨char2, hchar2_in, hchar2_lower, hchar2_ne, hchar2_count⟩ := h_exists
        intro k n hkn_in
        intro hk_eq
        rw [hk_eq] at hkn_in
        unfold implementation at hkn_in
        simp [List.mem_map] at hkn_in
        obtain ⟨c, hc_in, hc_eq⟩ := hkn_in
        have h_chars := get_chars_with_max_count_correct s
        have h_dup := remove_duplicates_correct (get_chars_with_max_count s)
        rw [h_dup] at hc_in
        rw [h_chars] at hc_in
        have h_count_eq : char_count s char = char_count s c := by
          rw [← hc_eq.1] at hk_eq
          rw [hk_eq]
          exact hc_in.2.2
        rw [h_count_eq] at hchar2_count
        have h_max := get_max_count_correct s char2 hchar2_in hchar2_lower
        rw [← hc_in.2.2] at h_max
        exact Nat.not_le.mpr hchar2_count h_max
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