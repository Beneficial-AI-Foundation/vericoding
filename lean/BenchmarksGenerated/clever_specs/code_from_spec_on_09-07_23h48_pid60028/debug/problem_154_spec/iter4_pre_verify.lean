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
  a.isSubstring b_rotation)));
-- program terminates
∃ result, impl a b = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def String.isSubstring (s : String) (t : String) : Bool :=
  t.splitOn s |>.length > 1

-- LLM HELPER
def rotate_string (s : String) (i : Nat) : String :=
  s.drop i ++ s.take i

-- LLM HELPER
def check_rotation_at (a b : String) (i : Nat) : Bool :=
  String.isSubstring a (rotate_string b i)

-- LLM HELPER
def check_all_rotations (a b : String) (i : Nat) : Bool :=
  if i >= b.length then false
  else if check_rotation_at a b i then true
  else check_all_rotations a b (i + 1)

def implementation (a b: String) : Bool :=
  if b.length = 0 then true
  else if b.length > a.length then false
  else check_all_rotations a b 0

-- LLM HELPER
lemma rotate_string_correct (s : String) (i : Nat) :
  rotate_string s i = s.drop i ++ s.take i := by
  rfl

-- LLM HELPER
lemma check_rotation_at_correct (a b : String) (i : Nat) :
  check_rotation_at a b i = true ↔ String.isSubstring a (b.drop i ++ b.take i) := by
  simp [check_rotation_at, rotate_string_correct]

-- LLM HELPER
lemma check_all_rotations_correct (a b : String) (start : Nat) :
  check_all_rotations a b start = true ↔ 
  ∃ i : Nat, start ≤ i ∧ i < b.length ∧ String.isSubstring a (b.drop i ++ b.take i) := by
  induction start using Nat.strong_induction_on with
  | ind start ih =>
    simp [check_all_rotations]
    split_ifs with h1 h2
    · simp [h1]
      constructor
      · intro h
        exfalso
        exact h
      · intro ⟨i, hi1, hi2, _⟩
        omega
    · simp [check_rotation_at_correct]
      constructor
      · intro h
        exact ⟨start, le_refl start, Nat.lt_of_not_ge h1, h⟩
      · intro ⟨i, hi1, hi2, hi3⟩
        cases' Nat.eq_or_lt_of_le hi1 with h h
        · rw [←h]
          exact hi3
        · rw [ih (start + 1) (Nat.lt_add_one start)]
          exact ⟨i, Nat.le_of_succ_le_succ h, hi2, hi3⟩
    · simp [check_rotation_at_correct]
      rw [ih (start + 1) (Nat.lt_add_one start)]
      constructor
      · intro ⟨i, hi1, hi2, hi3⟩
        exact ⟨i, Nat.le_trans (Nat.le_succ start) hi1, hi2, hi3⟩
      · intro ⟨i, hi1, hi2, hi3⟩
        cases' Nat.eq_or_lt_of_le hi1 with h h
        · rw [←h] at hi3
          exact absurd hi3 h2
        · exact ⟨i, Nat.le_of_succ_le_succ h, hi2, hi3⟩

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
      simp [h]
    · intro h
      split_ifs with h1
      · simp
        constructor
        · intro
          exfalso
          omega
        · intro ⟨_, h2, _⟩
          omega
      · simp [check_all_rotations_correct]
        constructor
        · intro h2
          constructor
          · omega
          · exact ⟨0, Nat.zero_le 0, h, h2⟩
        · intro ⟨h2, i, hi1, hi2, hi3⟩
          rw [check_all_rotations_correct]
          exact ⟨i, hi1, hi2, hi3⟩