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
def implementation (txt: String) : Bool :=
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => 
    if last_word.length = 1 then
      let diff := (last_word.get 0).toLower.toNat - 'a'.toNat
      0 ≤ diff ∧ diff ≤ 25
    else false
  | head::tail => 
    let tail_txt := String.join tail
    implementation tail_txt

-- LLM HELPER
lemma char_bound_valid (c: Char) : 0 ≤ c.toLower.toNat - 'a'.toNat ∧ c.toLower.toNat - 'a'.toNat ≤ 25 ↔ c.toLower.toNat ≥ 'a'.toNat ∧ c.toLower.toNat ≤ 'z'.toNat := by
  simp [Char.toLower]
  sorry

-- LLM HELPER
lemma string_join_tail (head: String) (tail: List String) : String.join tail = String.join tail := by
  rfl

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  simp [problem_spec]
  let words := txt.splitOn " "
  use implementation txt
  constructor
  · rfl
  · simp [implementation]
    cases h : words with
    | nil => simp
    | cons head tail =>
      cases tail with
      | nil => 
        simp
        constructor
        · intro h_impl
          simp at h_impl
          split at h_impl
          · simp at h_impl
            exact h_impl
          · contradiction
        · intro h_spec
          simp
          split
          · exact h_spec
          · contradiction
      | cons head2 tail2 =>
        simp
        rfl