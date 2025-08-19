def problem_spec
-- function signature
(impl: String → String → Bool)
-- inputs
(a b: String) :=
-- spec
let spec (result: Bool) :=
(b.length = 0 → result) ∧
(0 < b.length →
result ↔ ((b.length ≤ a.length) ∧
  (∃ i : Nat, i < b.length ∧
  let b_rotation := b.drop i ++ b.take i;
  a.contains b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def rotate_string (s: String) (i: Nat) : String :=
  s.drop i ++ s.take i

-- LLM HELPER
def check_rotation_at (a b: String) (i: Nat) : Bool :=
  if i < b.length then
    a.contains (rotate_string b i)
  else
    false

-- LLM HELPER
def check_all_rotations (a b: String) (i: Nat) : Bool :=
  if i >= b.length then
    false
  else if check_rotation_at a b i then
    true
  else
    check_all_rotations a b (i + 1)
termination_by b.length - i

def implementation (a b: String) : Bool := 
  if b.length = 0 then
    true
  else if b.length > a.length then
    false
  else
    check_all_rotations a b 0

-- LLM HELPER
lemma check_rotation_at_correct (a b: String) (i: Nat) :
  check_rotation_at a b i = true ↔ 
  (i < b.length ∧ a.contains (rotate_string b i)) := by
  simp only [check_rotation_at]
  split_ifs with h
  · simp [h]
  · simp [h]

-- LLM HELPER
lemma check_all_rotations_correct (a b: String) (start: Nat) :
  check_all_rotations a b start = true ↔ 
  (∃ i : Nat, start ≤ i ∧ i < b.length ∧ a.contains (rotate_string b i)) := by
  induction start using Nat.strong_induction_on with
  | h start ih =>
    simp only [check_all_rotations]
    split_ifs with h1 h2
    · simp [h1]
      constructor
      · intro h
        exfalso
        exact h
      · intro ⟨i, hi1, hi2, _⟩
        have : i < start := by
          by_contra hnot
          simp at hnot
          have : start ≤ i := hnot
          have : i < b.length := hi2
          have : start ≤ i := this
          have : start < b.length := Nat.lt_of_le_of_lt this hi2
          have : ¬(start >= b.length) := Nat.not_le.mpr this
          exact this h1
        exact Nat.lt_irrefl i (Nat.lt_of_le_of_lt hi1 this)
    · simp [check_rotation_at_correct] at h2
      simp [h2]
      constructor
      · intro h
        use start
        simp [h1, h2, h]
      · intro ⟨i, hi1, hi2, hi3⟩
        cases' Nat.eq_or_lt_of_le hi1 with h h
        · rw [← h]
          exact hi3
        · exfalso
          exact h2 ⟨hi2, hi3⟩
    · have h3 : start < b.length := by
        by_contra h
        simp [Nat.not_lt] at h
        exact h1 h
      rw [ih (start + 1) (Nat.lt_add_one start)]
      simp [check_rotation_at_correct] at h2
      constructor
      · intro h
        obtain ⟨i, hi1, hi2, hi3⟩ := h
        use i
        constructor
        · have : start + 1 ≤ i := hi1
          exact Nat.le_trans (Nat.le_add_right start 1) this
        · exact ⟨hi2, hi3⟩
      · intro ⟨i, hi1, hi2, hi3⟩
        cases' Nat.eq_or_lt_of_le hi1 with h h
        · rw [← h] at hi2 hi3
          exact h2 ⟨hi2, hi3⟩
        · use i
          exact ⟨Nat.le_of_succ_le_succ h, hi2, hi3⟩

-- LLM HELPER
lemma rotate_string_eq (b: String) (i: Nat) :
  rotate_string b i = b.drop i ++ b.take i := by
  simp [rotate_string]

theorem correctness
(a b: String)
: problem_spec implementation a b := by
  simp [problem_spec]
  use implementation a b
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro h
      split_ifs
      · trivial
      · exfalso
        exact h
    · intro h
      split_ifs with h1 h2
      · simp at h1
        exact h1
      · simp at h2
        constructor
        · intro _
          constructor
          · have : ¬(b.length > a.length) := h2
            exact Nat.le_of_not_gt this
          · simp [check_all_rotations_correct]
            intro ⟨i, hi1, hi2⟩
            use i
            simp [rotate_string_eq]
            exact ⟨hi1, hi2⟩
        · intro ⟨_, hex⟩
          simp [check_all_rotations_correct]
          obtain ⟨i, hi1, hi2⟩ := hex
          use i
          simp [rotate_string_eq] at hi2
          exact ⟨Nat.zero_le i, hi1, hi2⟩
      · constructor
        · intro _
          constructor
          · have : ¬(b.length > a.length) := h2
            exact Nat.le_of_not_gt this
          · simp [check_all_rotations_correct]
            intro ⟨i, _, hi2⟩
            use i
            simp [rotate_string_eq]
            exact ⟨hi2.1, hi2.2⟩
        · intro ⟨hlen, hex⟩
          simp [check_all_rotations_correct]
          obtain ⟨i, hi1, hi2⟩ := hex
          use i
          simp [rotate_string_eq] at hi2
          exact ⟨Nat.zero_le i, hi1, hi2⟩