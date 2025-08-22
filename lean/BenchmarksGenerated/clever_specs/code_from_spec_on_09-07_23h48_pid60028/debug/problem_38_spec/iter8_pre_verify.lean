def problem_spec
(impl: String → String)
(s: String) :=
let n := s.length;
let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
  (chars.drop start_index).take (end_index - start_index + 1);
let spec (result: String) :=
  let encoded_chars := result.toList;
  let original_chars := s.toList;
  encoded_chars.length = n ∧
  (∀ i : Nat, i * 3 + 3 ≤ n →
    extract encoded_chars (i * 3) (i * 3 + 2) =
      [original_chars[i * 3 + 1]!, original_chars[i * 3 + 2]!, original_chars[i * 3]!]) ∧
  (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
    extract original_chars (n - n % 3) (n - 1));
-- program termination
∃ result,
  impl s = result ∧
  spec result

-- LLM HELPER
def encodeString (chars: List Char) : List Char :=
  let rec encodeLoop (remaining: List Char) (acc: List Char) : List Char :=
    match remaining with
    | a :: b :: c :: rest => encodeLoop rest (acc ++ [b, c, a])
    | remainder => acc ++ remainder
  encodeLoop chars []

def implementation (s: String) : String :=
  let chars := s.toList
  let encoded := encodeString chars
  String.mk encoded

-- LLM HELPER  
lemma encodeString_length (chars: List Char) :
  (encodeString chars).length = chars.length := by
  unfold encodeString
  let rec loop_length (remaining: List Char) (acc: List Char) :
    (encodeString.encodeLoop remaining acc).length = acc.length + remaining.length := by
    unfold encodeString.encodeLoop
    cases remaining with
    | nil => simp
    | cons a tail =>
      cases tail with
      | nil => simp
      | cons b tail2 =>
        cases tail2 with
        | nil => simp
        | cons c rest => 
          simp [List.length_append]
          rw [loop_length rest (acc ++ [b, c, a])]
          simp [List.length_append]
          omega
  have := loop_length chars []
  simp at this
  exact this

-- LLM HELPER
lemma encodeString_spec (chars: List Char) (i: Nat) :
  i * 3 + 3 ≤ chars.length →
  let encoded := encodeString chars
  let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
    (chars.drop start_index).take (end_index - start_index + 1)
  extract encoded (i * 3) (i * 3 + 2) = [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  intro h
  unfold encodeString
  
  let rec prove_by_induction (j: Nat) (prefix: List Char) (remaining: List Char) (acc: List Char) :
    j ≤ i →
    prefix.length = j * 3 →
    prefix ++ remaining = chars →
    j * 3 + 3 ≤ chars.length →
    let encoded := encodeString.encodeLoop remaining acc
    let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
      (chars.drop start_index).take (end_index - start_index + 1)
    j < i → extract encoded ((i - j) * 3) ((i - j) * 3 + 2) = 
      [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
    intro h_j_le_i h_prefix h_combined h_bound h_j_lt_i
    unfold encodeString.encodeLoop
    cases remaining with
    | nil => 
      simp at h_bound
      omega
    | cons a tail =>
      cases tail with
      | nil => 
        simp at h_bound
        omega
      | cons b tail2 =>
        cases tail2 with
        | nil => 
          simp at h_bound
          omega
        | cons c rest =>
          by_cases h_eq : j + 1 = i
          · simp [h_eq]
            simp [List.drop, List.take]
            have h_indices : i * 3 < chars.length ∧ i * 3 + 1 < chars.length ∧ i * 3 + 2 < chars.length := by
              omega
            have h_get : chars[i * 3]! = a ∧ chars[i * 3 + 1]! = b ∧ chars[i * 3 + 2]! = c := by
              rw [← h_combined]
              simp [List.getElem_append_left, List.getElem_append_right]
              simp [h_prefix, h_eq]
              constructor
              · simp [List.getElem_cons_zero]
              · constructor
                · simp [List.getElem_cons_succ]
                · simp [List.getElem_cons_succ]
            simp [h_get]
            rfl
          · have h_j_plus_1_lt_i : j + 1 < i := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt h_j_lt_i) h_eq
            have h_rec := prove_by_induction (j + 1) (prefix ++ [a, b, c]) rest (acc ++ [b, c, a])
            simp [List.length_append] at h_rec
            have h_new_prefix : (prefix ++ [a, b, c]).length = (j + 1) * 3 := by
              simp [List.length_append, h_prefix]
              omega
            have h_new_combined : (prefix ++ [a, b, c]) ++ rest = chars := by
              rw [← List.append_assoc, h_combined]
              rfl
            have h_new_bound : (j + 1) * 3 + 3 ≤ chars.length := by
              omega
            have h_new_le : j + 1 ≤ i := Nat.le_of_lt h_j_plus_1_lt_i
            have h_sub : (i - (j + 1)) * 3 = (i - j) * 3 - 3 := by omega
            rw [h_rec h_new_le h_new_prefix h_new_combined h_new_bound h_j_plus_1_lt_i]
            simp [List.drop, List.take]
            rfl
  
  by_cases h_i_zero : i = 0
  · simp [h_i_zero]
    unfold encodeString.encodeLoop
    cases chars with
    | nil => simp at h
    | cons a tail =>
      cases tail with
      | nil => simp at h
      | cons b tail2 =>
        cases tail2 with
        | nil => simp at h
        | cons c rest =>
          simp [List.drop, List.take]
          rfl
  · have h_i_pos : 0 < i := Nat.pos_of_ne_zero h_i_zero
    have h_initial := prove_by_induction 0 [] chars [] (Nat.zero_le i) rfl rfl h h_i_pos
    simp at h_initial
    exact h_initial

-- LLM HELPER
lemma encodeString_remainder (chars: List Char) (n: Nat) :
  n = chars.length →
  n % 3 ≠ 0 →
  let encoded := encodeString chars
  let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
    (chars.drop start_index).take (end_index - start_index + 1)
  extract encoded (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  intro hn hmod
  unfold encodeString
  
  let full_groups := n / 3
  let remainder_len := n % 3
  
  let rec prove_remainder (k: Nat) (processed: List Char) (remaining: List Char) (acc: List Char) :
    k = full_groups →
    processed.length = k * 3 →
    remaining.length = remainder_len →
    processed ++ remaining = chars →
    let encoded := encodeString.encodeLoop remaining acc
    let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
      (chars.drop start_index).take (end_index - start_index + 1)
    extract encoded 0 (remainder_len - 1) = extract remaining 0 (remainder_len - 1) := by
    intro h_k h_processed h_remaining h_combined
    unfold encodeString.encodeLoop
    cases remaining with
    | nil => 
      simp at h_remaining
      simp [hmod] at h_remaining
    | cons a tail =>
      cases tail with
      | nil => 
        simp [List.drop, List.take]
        rfl
      | cons b tail2 =>
        cases tail2 with
        | nil => 
          simp [List.drop, List.take]
          rfl
        | cons c rest =>
          simp at h_remaining
          have : remainder_len ≥ 3 := by omega
          have : remainder_len < 3 := Nat.mod_lt n (by omega)
          omega
  
  have h_split : ∃ processed remaining, 
    processed.length = full_groups * 3 ∧ 
    remaining.length = remainder_len ∧
    processed ++ remaining = chars := by
    use chars.take (full_groups * 3), chars.drop (full_groups * 3)
    simp [List.length_take, List.length_drop, hn]
    constructor
    · simp [min_def]
      have : full_groups * 3 ≤ n := Nat.mul_div_le n 3
      omega
    · constructor
      · simp [min_def]
        have : full_groups * 3 ≤ n := Nat.mul_div_le n 3
        have : n = full_groups * 3 + remainder_len := Nat.div_add_mod n 3
        omega
      · simp [List.take_append_drop]
  
  obtain ⟨processed, remaining, h_proc_len, h_rem_len, h_split⟩ := h_split
  
  have h_remainder_preserved := prove_remainder full_groups processed remaining []
  simp at h_remainder_preserved
  
  have h_result := h_remainder_preserved rfl h_proc_len h_rem_len h_split
  
  simp [List.drop, List.take]
  rw [← h_split] at h_result
  simp [List.drop_append, List.take_append] at h_result
  have : full_groups * 3 = n - remainder_len := by
    have : n = full_groups * 3 + remainder_len := Nat.div_add_mod n 3
    omega
  rw [this]
  exact h_result

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let n := s.length
  let original_chars := s.toList
  let encoded := encodeString original_chars
  
  use String.mk encoded
  constructor
  · rfl
  · constructor
    · simp [String.toList_mk]
      exact encodeString_length original_chars
    · constructor
      · intro i hi
        simp [String.toList_mk]
        exact encodeString_spec original_chars i hi
      · intro h
        simp [String.toList_mk]
        exact encodeString_remainder original_chars n rfl h