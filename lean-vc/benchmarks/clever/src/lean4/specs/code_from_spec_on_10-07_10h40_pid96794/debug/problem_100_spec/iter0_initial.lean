import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def buildSequence (n: Int) (current: Int) (count: Int) : List Int :=
  if count <= 0 then []
  else current :: buildSequence n (current + 2) (count - 1)

def implementation (n: Int) : List Int := 
  if n <= 0 then [] else buildSequence n n n

-- LLM HELPER
lemma buildSequence_length (n: Int) (current: Int) (count: Int) :
  (buildSequence n current count).length = max 0 count := by
  induction count using Int.emod_two_emod_two_induction generalizing current with
  | zero => simp [buildSequence]
  | pos k ih =>
    simp [buildSequence]
    rw [List.length_cons]
    rw [ih]
    simp [Int.add_one_le_iff]
  | neg k ih => simp [buildSequence]

-- LLM HELPER
lemma buildSequence_get (n: Int) (current: Int) (count: Int) (i: Nat) :
  i < (buildSequence n current count).length →
  (buildSequence n current count)[i]! = current + 2 * i := by
  intro h
  induction count using Int.emod_two_emod_two_induction generalizing current i with
  | zero => 
    simp [buildSequence] at h
  | pos k ih =>
    simp [buildSequence] at h ⊢
    cases i with
    | zero => simp
    | succ j =>
      rw [List.get_cons_succ]
      rw [ih]
      ring
      simp at h
      exact h
  | neg k ih => simp [buildSequence] at h

-- LLM HELPER
lemma buildSequence_first (n: Int) (current: Int) (count: Int) :
  0 < count → (buildSequence n current count)[0]! = current := by
  intro h
  cases' count.trichotomous 0 with h1 h2
  · contradiction
  · cases h2 with
    | inl h2 => contradiction
    | inr h2 =>
      simp [buildSequence]
      rw [List.get_cons_zero]

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  split_ifs with h
  · simp
    use []
    simp
    constructor
    · rfl
    · simp
      intro i h1 h2
      exfalso
      linarith
  · push_neg at h
    use buildSequence n n n
    constructor
    · rfl
    · simp
      constructor
      · rw [buildSequence_length]
        simp [h]
      · constructor
        · intro i h1 h2
          rw [buildSequence_get, buildSequence_get]
          ring
          · rw [buildSequence_length]
            simp [h]
            linarith
          · rw [buildSequence_length]
            simp [h]
            linarith
        · rw [buildSequence_first]
          exact h