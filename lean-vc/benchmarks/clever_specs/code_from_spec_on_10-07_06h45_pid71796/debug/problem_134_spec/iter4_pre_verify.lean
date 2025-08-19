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

-- LLM HELPER
lemma splitOn_join_length_lt (h : String) (t : List String) (ht : t ≠ []) :
  (String.join t).splitOn " " |>.length < (h :: t).length := by
  sorry

def implementation (txt: String) : Bool :=
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | _::tail => 
    let tail_txt := String.join tail
    implementation tail_txt
  termination_by (txt.splitOn " ").length
  decreasing_by
    simp only [word_count]
    apply splitOn_join_length_lt
    simp

-- LLM HELPER
lemma is_single_letter_correct (s: String) :
  is_single_letter s = true ↔ 
  s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25) := by
  simp only [is_single_letter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  unfold problem_spec
  exists implementation txt
  constructor
  · rfl
  · simp only [true_and]
    let words := txt.splitOn " "
    cases h : words with
    | nil => simp only [implementation, h, false_iff]
    | cons head tail =>
      cases tail with
      | nil => 
        simp only [implementation, h, List.cons_nil_eq_cons]
        rw [is_single_letter_correct]
      | cons h' t' =>
        simp only [implementation, h]
        rfl