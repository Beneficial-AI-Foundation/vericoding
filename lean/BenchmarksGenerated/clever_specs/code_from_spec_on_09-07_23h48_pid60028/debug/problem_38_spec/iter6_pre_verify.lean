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
  simp [encodeString]
  
  -- We need to prove by induction on the structure of the encoding
  let rec prove_encoding (prefix: List Char) (remaining: List Char) (acc: List Char) (j: Nat) :
    prefix.length = j * 3 →
    prefix ++ remaining = chars →
    j ≤ i →
    i * 3 + 3 ≤ (prefix ++ remaining).length →
    let encoded := encodeString.encodeLoop remaining acc
    let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
      (chars.drop start_index).take (end_index - start_index + 1)
    extract encoded ((i - j) * 3) ((i - j) * 3 + 2) = 
      [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
    intro h_prefix h_combined h_j_le_i h_bound
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
          by_cases h_eq : j = i
          · -- Base case: j = i
            simp [h_eq]
            simp [List.drop, List.take]
            have h_indices : i * 3 < chars.length ∧ i * 3 + 1 < chars.length ∧ i * 3 + 2 < chars.length := by
              omega
            have h_get : chars[i * 3]! = a ∧ chars[i * 3 + 1]! = b ∧ chars[i * 3 + 2]! = c := by
              rw [←h_combined]
              simp [List.getElem_append_left, List.getElem_append_right]
              simp [h_prefix, h_eq]
              constructor
              · simp [List.getElem_cons_zero]
              · constructor
                · simp [List.getElem_cons_succ]
                · simp [List.getElem_cons_succ]
            simp [h_get]
            rfl
          · -- Inductive case: j < i
            have h_j_lt_i : j < i := Nat.lt_of_le_of_ne h_j_le_i (Ne.symm h_eq)
            have h_rec := prove_encoding (prefix ++ [a, b, c]) rest (acc ++ [b, c, a]) (j + 1)
            simp [List.length_append] at h_rec
            have h_new_prefix : (prefix ++ [a, b, c]).length = (j + 1) * 3 := by
              simp [List.length_append, h_prefix]
              omega
            have h_new_combined : (prefix ++ [a, b, c]) ++ rest = chars := by
              rw [←List.append_assoc, h_combined]
              rfl
            have h_new_bound : i * 3 + 3 ≤ ((prefix ++ [a, b, c]) ++ rest).length := by
              rw [h_new_combined]
              exact h_bound
            have h_new_le : j + 1 ≤ i := by omega
            have h_sub : (i - (j + 1)) * 3 = (i - j) * 3 - 3 := by omega
            rw [h_rec h_new_prefix h_new_combined h_new_le h_new_bound]
            simp [List.drop, List.take]
            simp [h_sub]
            rfl
  
  have h_initial := prove_encoding [] chars [] 0
  simp at h_initial
  exact h_initial rfl rfl (Nat.zero_le i) h

-- LLM HELPER
lemma encodeString_remainder (chars: List Char) (n: Nat) :
  n = chars.length →
  n % 3 ≠ 0 →
  let encoded := encodeString chars
  let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
    (chars.drop start_index).take (end_index - start_index + 1)
  extract encoded (n - n % 3) (n - 1) = extract chars (n - n % 3) (n - 1) := by
  intro hn hmod
  simp [encodeString]
  
  -- The remainder elements are preserved unchanged
  let rec prove_remainder (processed: List Char) (remaining: List Char) (acc: List Char) (k: Nat) :
    processed.length = k * 3 →
    processed ++ remaining = chars →
    remaining.length = n % 3 →
    let encoded := encodeString.encodeLoop remaining acc
    let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
      (chars.drop start_index).take (end_index - start_index + 1)
    extract encoded 0 (remaining.length - 1) = extract remaining 0 (remaining.length - 1) := by
    intro h_processed h_combined h_remainder_len
    unfold encodeString.encodeLoop
    cases remaining with
    | nil => simp
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
          -- This case is impossible since remaining.length = n % 3 < 3
          simp at h_remainder_len
          omega
  
  have h_split : ∃ processed remaining, processed.length = (n - n % 3) ∧ 
                                      remaining.length = n % 3 ∧
                                      processed ++ remaining = chars := by
    use chars.take (n - n % 3), chars.drop (n - n % 3)
    simp [List.length_take, List.length_drop, hn]
    constructor
    · simp [min_def]
      omega
    · constructor
      · simp [min_def]
        omega
      · simp [List.take_append_drop]
  
  obtain ⟨processed, remaining, h_proc_len, h_rem_len, h_split⟩ := h_split
  
  have h_remainder_preserved := prove_remainder processed remaining [] (n / 3)
  simp [h_proc_len, Nat.div_mul_cancel] at h_remainder_preserved
  
  -- The final step involves showing that the encoding preserves the remainder
  simp [List.drop, List.take]
  rfl

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
    · -- Length preservation
      simp [String.toList_mk]
      exact encodeString_length original_chars
    · constructor
      · -- Triple encoding correctness
        intro i hi
        simp [String.toList_mk]
        exact encodeString_spec original_chars i hi
      · -- Remainder correctness
        intro h
        simp [String.toList_mk]
        exact encodeString_remainder original_chars n rfl h