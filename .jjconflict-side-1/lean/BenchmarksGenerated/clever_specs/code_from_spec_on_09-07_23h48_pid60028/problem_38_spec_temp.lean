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
  
  let rec prove_by_strong_induction (j: Nat) (prefix: List Char) (remaining: List Char) (acc: List Char) :
    j ≤ i →
    prefix.length = j * 3 →
    prefix ++ remaining = chars →
    j * 3 + 3 ≤ chars.length →
    let encoded := encodeString.encodeLoop remaining acc
    let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
      (chars.drop start_index).take (end_index - start_index + 1)
    extract encoded ((i - j) * 3) ((i - j) * 3 + 2) = 
      [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
    intro h_j_le_i h_prefix h_combined h_bound
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
          · have h_j_lt_i : j < i := Nat.lt_of_le_of_ne h_j_le_i h_eq
            have h_rec := prove_by_strong_induction (j + 1) (prefix ++ [a, b, c]) rest (acc ++ [b, c, a])
            simp [List.length_append] at h_rec
            have h_new_prefix : (prefix ++ [a, b, c]).length = (j + 1) * 3 := by
              simp [List.length_append, h_prefix]
              omega
            have h_new_combined : (prefix ++ [a, b, c]) ++ rest = chars := by
              rw [← List.append_assoc, h_combined]
              rfl
            have h_new_bound : (j + 1) * 3 + 3 ≤ chars.length := by
              omega
            have h_new_le : j + 1 ≤ i := Nat.succ_le_of_lt h_j_lt_i
            have h_sub : (i - (j + 1)) * 3 = (i - j) * 3 - 3 := by omega
            rw [h_rec h_new_le h_new_prefix h_new_combined h_new_bound]
            simp [List.drop, List.take]
            rfl
  
  have h_initial := prove_by_strong_induction 0 [] chars [] (Nat.zero_le i) rfl rfl h
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
    extract (acc ++ encoded) (acc.length) (acc.length + remainder_len - 1) = 
      extract remaining 0 (remainder_len - 1) := by
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
        have : remainder_len = 1 := by omega
        simp [this]
        rfl
      | cons b tail2 =>
        cases tail2 with
        | nil => 
          simp [List.drop, List.take]
          have : remainder_len = 2 := by omega
          simp [this]
          rfl
        | cons c rest =>
          simp at h_remaining
          have : remainder_len ≥ 3 := by omega
          have : remainder_len < 3 := Nat.mod_lt n (by omega)
          omega
  
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
    · simp [String.toList_mk]
      exact encodeString_length original_chars
    · constructor
      · intro i hi
        simp [String.toList_mk]
        exact encodeString_spec original_chars i hi
      · intro h
        simp [String.toList_mk]
        exact encodeString_remainder original_chars n rfl h