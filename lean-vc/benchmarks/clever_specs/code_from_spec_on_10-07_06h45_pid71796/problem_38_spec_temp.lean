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
lemma encode_chars_aux_get (chars: List Char) (i j: Nat) :
  j * 3 + 2 < chars.length →
  i ≤ j * 3 →
  (encode_chars_aux chars i)[j * 3 - i]? = some chars[j * 3 + 1]! ∧
  (encode_chars_aux chars i)[j * 3 - i + 1]? = some chars[j * 3 + 2]! ∧
  (encode_chars_aux chars i)[j * 3 - i + 2]? = some chars[j * 3]! := by
  induction i using Nat.strong_induction_on generalizing j
  case ind i ih =>
    intro h1 h2
    unfold encode_chars_aux
    if h : i + 2 < chars.length then
      simp [h]
      if h4 : i < j * 3 then
        have : j * 3 - i = 3 + (j * 3 - (i + 3)) := by omega
        rw [this]
        simp [List.getElem?_append_right]
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
lemma extract_encode_triplet (chars: List Char) (i: Nat) :
  i * 3 + 2 < chars.length →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (i * 3) (i * 3 + 2) =
    [chars[i * 3 + 1]!, chars[i * 3 + 2]!, chars[i * 3]!] := by
  intro h
  unfold encode_chars
  have aux := encode_chars_aux_get chars 0 i h (by omega)
  simp [List.drop_take]
  rw [List.take_three_eq_of_length_ge]
  · ext n
    simp
    cases n with
    | zero => exact aux.1
    | succ n =>
      cases n with
      | zero => exact aux.2.1
      | succ n =>
        cases n with
        | zero => exact aux.2.2
        | succ n => simp
  · rw [encode_chars_aux_length]
    omega

-- LLM HELPER
lemma List.take_three_eq_of_length_ge (l: List α) (h: l.length ≥ 3) :
  l.take 3 = [l[0]!, l[1]!, l[2]!] := by
  cases l with
  | nil => simp at h
  | cons a l' =>
    cases l' with
    | nil => simp at h
    | cons b l'' =>
      cases l'' with
      | nil => simp at h
      | cons c l''' =>
        simp [List.take]

-- LLM HELPER
lemma extract_remainder_aux (chars: List Char) (i: Nat) :
  i % 3 = 0 →
  i + 2 ≥ chars.length →
  chars.length % 3 ≠ 0 →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars_aux chars i) (chars.length - chars.length % 3 - i) (chars.length - 1 - i) =
    extract chars (chars.length - chars.length % 3) (chars.length - 1) := by
  intro h1 h2 h3
  unfold encode_chars_aux
  simp [h2]
  have : chars.length - chars.length % 3 = i := by
    rw [Nat.sub_mod_eq_zero]
    rw [Nat.mul_div_cancel']
    exact h1
  rw [this]
  simp [List.drop_take]

-- LLM HELPER
lemma extract_remainder (chars: List Char) :
  chars.length % 3 ≠ 0 →
  let extract (cs: List Char) (start_index: Nat) (end_index: Nat) :=
    (cs.drop start_index).take (end_index - start_index + 1);
  extract (encode_chars chars) (chars.length - chars.length % 3) (chars.length - 1) =
    extract chars (chars.length - chars.length % 3) (chars.length - 1) := by
  intro h
  unfold encode_chars
  apply extract_remainder_aux
  · rfl
  · have : chars.length - chars.length % 3 = (chars.length / 3) * 3 := by
      rw [Nat.sub_mod_eq_zero]
      rw [Nat.mul_div_cancel']
      rfl
    rw [this]
    omega
  · exact h

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
        exact extract_encode_triplet s.toList i this
      · intro h
        exact extract_remainder s.toList h