def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(txt: String) :=
-- spec
let spec (result: Bool) :=
  let words := txt.splitOn " ";
  match words with
  | [] => result = False
  | [last_word] => (result ↔ last_word.length = 1 ∧ (let diff := (last_word.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25))
  | _::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
-- program terminates
∃ result, impl txt = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_single_letter (s: String) : Bool :=
  s.length = 1 && 
  let c := s.get 0
  let diff := c.toLower.toNat - 'a'.toNat
  0 ≤ diff && diff ≤ 25

-- LLM HELPER
def word_count (s: String) : Nat :=
  (s.splitOn " ").length

def implementation (txt: String) : Bool :=
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | _::tail => 
    let tail_txt := String.join tail
    implementation tail_txt
  termination_by word_count txt
  decreasing_by
    simp [word_count]
    have h1 : (txt.splitOn " ").length = words.length := by simp [words]
    rw [← h1]
    cases words with
    | nil => simp
    | cons h t =>
      cases t with
      | nil => simp
      | cons h' t' =>
        simp [String.join]
        have h2 : (h' :: t').length < (h :: h' :: t').length := by simp [Nat.lt_succ_iff]
        have h3 : (String.join (h' :: t')).splitOn " " = h' :: t' := by
          induction t' with
          | nil => simp [String.join]
          | cons x xs ih => 
            simp [String.join, String.splitOn]
            rw [String.splitOn_append]
            simp
        rw [h3]
        exact h2

-- LLM HELPER
lemma is_single_letter_correct (s: String) :
  is_single_letter s = true ↔ 
  s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25) := by
  simp [is_single_letter]
  constructor
  · intro h
    cases h1 : s.length = 1 with
    | false => simp [h1] at h
    | true => 
      simp [h1] at h
      constructor
      · exact h1
      · exact h
  · intro h
    cases h with
    | mk left right =>
      simp [left, right]

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  unfold problem_spec
  exists implementation txt
  constructor
  · rfl
  · simp
    let words := txt.splitOn " "
    cases h : words with
    | nil => simp [implementation, h]
    | cons head tail =>
      cases tail with
      | nil => 
        simp [implementation, h]
        rw [is_single_letter_correct]
      | cons h' t' =>
        simp [implementation, h]
        rfl