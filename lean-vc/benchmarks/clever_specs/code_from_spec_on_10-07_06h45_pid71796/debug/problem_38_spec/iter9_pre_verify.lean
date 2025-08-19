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
def encode_chars_aux (chars: List Char) (i: Nat) : List Char :=
  if i + 2 < chars.length then
    let triplet := [chars[i + 1]!, chars[i + 2]!, chars[i]!]
    triplet ++ encode_chars_aux chars (i + 3)
  else
    chars.drop i

-- LLM HELPER
def encode_chars (chars: List Char) : List Char :=
  encode_chars_aux chars 0

def implementation (s: String) : String := 
  String.mk (encode_chars s.toList)

-- LLM HELPER
lemma encode_chars_aux_length (chars: List Char) (i: Nat) :
  (encode_chars_aux chars i).length = chars.length - i := by
  induction i using Nat.strong_induction_on
  case ind i ih =>
    unfold encode_chars_aux
    if h : i + 2 < chars.length then
      simp [h]
      rw [List.length_append]
      rw [ih (i + 3)]
      · simp
        omega
      · omega
    else
      simp [h]
      rw [List.length_drop]
      omega

-- LLM HELPER  
lemma encode_chars_length (chars: List Char) :
  (encode_chars chars).length = chars.length := by
  unfold encode_chars
  rw [encode_chars_aux_length]
  simp

-- LLM HELPER
lemma get_encode_chars_aux (chars: List Char) (i j: Nat) :
  j * 3 + 2 < chars.length →
  i ≤ j * 3 →
  (encode_chars_aux chars i)[j * 3 - i]? = some chars[j * 3 + 1]! ∧
  (encode_chars_aux chars i)[j * 3 - i + 1]? = some chars[j * 3 + 2]! ∧
  (encode_chars_aux chars i)[j * 3 - i + 2]? = some chars[j * 3]! := by
  induction i using Nat.strong_induction_on
  case ind i ih =>
    intro h1 h2
    unfold encode_chars_aux
    if h : i + 2 < chars.length then
      simp [h]
      if h4 : i < j * 3 then
        have : j * 3 - i = 3 + (j * 3 - (i + 3)) := by omega
        rw [this]
        simp
        rw [List.getElem?_append_right]
        · apply ih
          · exact h1
          · omega
          · omega
        · simp; omega
      else
        have : i = j * 3 := by omega
        subst this
        simp
        constructor
        · rfl
        · constructor
          · rfl
          · rfl
    else
      have : j * 3 + 2 < i + 3 := by omega
      omega

-- LLM HELPER
lemma extract_encode_chars_aux (chars: List Char) (i j: Nat) :
  j * 3 + 2 < chars.length →
  i ≤ j * 3 →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars_aux chars i) (j * 3 - i) (j * 3 - i + 2) =
    [chars[j * 3 + 1]!, chars[j * 3 + 2]!, chars[j * 3]!] := by
  intro h1 h2
  unfold List.take List.drop
  have aux := get_encode_chars_aux chars i j h1 h2
  simp [List.take_succ_drop]
  rw [← List.take_append_drop 3]
  simp
  ext n
  simp
  cases n with
  | zero => 
    simp
    exact aux.1
  | succ n =>
    cases n with
    | zero =>
      simp
      exact aux.2.1
    | succ n =>
      cases n with
      | zero =>
        simp
        exact aux.2.2
      | succ n =>
        simp

-- LLM HELPER
lemma extract_encode_chars (chars: List Char) (i: Nat) :
  i * 3 + 2 < chars.length →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (i * 3) (i * 3 + 2) =
    [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  intro h
  unfold encode_chars
  rw [extract_encode_chars_aux chars 0 i]
  · exact h
  · omega

-- LLM HELPER
lemma extract_remainder (chars: List Char) :
  chars.length % 3 ≠ 0 →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (chars.length - chars.length % 3) (chars.length - 1) =
    extract chars (chars.length - chars.length % 3) (chars.length - 1) := by
  intro h
  unfold encode_chars
  have : chars.length - chars.length % 3 = (chars.length / 3) * 3 := by
    rw [Nat.sub_mod_eq_zero]
    rw [Nat.mul_div_cancel']
    simp
  rw [this]
  simp [encode_chars_aux]
  have : (chars.length / 3) * 3 + 2 ≥ chars.length := by
    cases' Nat.mod_two_eq_zero_or_one (chars.length % 3) with h1 h2
    · simp at h1
      omega
    · have : chars.length % 3 = 1 ∨ chars.length % 3 = 2 := by
        have : chars.length % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      cases this with
      | inl h3 => omega
      | inr h3 => omega
  simp [List.drop_take]
  rfl

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  let n := s.length
  let extract (chars: List Char) (start_index: Nat) (end_index: Nat) :=
    (chars.drop start_index).take (end_index - start_index + 1)
  let spec (result: String) :=
    let encoded_chars := result.toList
    let original_chars := s.toList
    encoded_chars.length = n ∧
    (∀ i : Nat, i * 3 + 3 ≤ n →
      extract encoded_chars (i * 3) (i * 3 + 2) =
        [original_chars[i * 3 + 1]!, original_chars[i * 3 + 2]!, original_chars[i * 3]!]) ∧
    (n % 3 ≠ 0 → extract encoded_chars (n - n % 3) (n - 1) =
      extract original_chars (n - n % 3) (n - 1))
  
  use String.mk (encode_chars s.toList)
  constructor
  · rfl
  · simp only [String.toList_mk]
    constructor
    · exact encode_chars_length s.toList
    · constructor
      · intro i h
        have : i * 3 + 2 < s.toList.length := by omega
        exact extract_encode_chars s.toList i this
      · intro h
        exact extract_remainder s.toList h