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
  | head::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
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
def join_tail (words: List String) : String :=
  match words with
  | [] => ""
  | [w] => w
  | h::t => h ++ " " ++ join_tail t

-- LLM HELPER
def count_words (s: String) : Nat :=
  (s.splitOn " ").length

def implementation (txt: String) : Bool :=
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | head::tail => 
    let tail_txt := String.join tail
    implementation tail_txt
  termination_by count_words txt
  decreasing_by
    simp [count_words]
    sorry

-- LLM HELPER
lemma string_join_tail_correct (words: List String) :
  String.join words = join_tail words := by
  induction words with
  | nil => simp [String.join, join_tail]
  | cons h t ih =>
    cases t with
    | nil => simp [String.join, join_tail]
    | cons h' t' => 
      simp [String.join, join_tail]
      rw [ih]

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
  · simp [implementation]
    let words := txt.splitOn " "
    cases h : words with
    | nil => simp [h]
    | cons head tail =>
      cases tail with
      | nil => 
        simp [h]
        rw [is_single_letter_correct]
      | cons h' t' =>
        simp [h]
        rw [← string_join_tail_correct]