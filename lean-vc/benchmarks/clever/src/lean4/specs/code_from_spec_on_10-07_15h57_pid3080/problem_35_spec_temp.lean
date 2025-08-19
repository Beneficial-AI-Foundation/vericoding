import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l.get! i ≤ result) ∧
  (∃ i, i < l.length ∧ l.get! i = result));
-- program termination
∃ result, implementation l = result ∧
spec result

def implementation (l: List Int) : Int := 
  match l with
  | [] => 0
  | h :: t => List.foldl max h t

-- LLM HELPER
lemma list_max_ge_all (l: List Int) (h: Int) :
  ∀ i, i < (h :: l).length → (h :: l).get! i ≤ List.foldl max h l := by
  intro i hi
  induction l generalizing h i with
  | nil => 
    simp at hi
    cases hi with
    | refl => simp [List.get!]
  | cons a t ih =>
    simp at hi
    cases' hi with hi hi
    · subst hi
      simp [List.get!]
      exact le_max_left h a
    · have : (h :: a :: t).get! i.succ = (a :: t).get! i := by simp [List.get!]
      rw [this]
      have ih_inst := ih (max h a) i
      simp at ih_inst
      apply ih_inst
      exact hi

-- LLM HELPER
lemma list_max_in_list (l: List Int) (h: Int) :
  ∃ i, i < (h :: l).length ∧ (h :: l).get! i = List.foldl max h l := by
  induction l generalizing h with
  | nil => 
    use 0
    simp [List.get!]
  | cons a t ih =>
    by_cases h_le : h ≤ a
    · have ih_inst := ih (max h a)
      obtain ⟨i, hi, eq⟩ := ih_inst
      use i + 1
      constructor
      · simp
        exact Nat.succ_lt_succ hi
      · simp [List.get!]
        simp at eq
        rw [max_def h a] at eq
        simp [h_le] at eq
        exact eq
    · use 0
      simp [List.get!, max_def]
      exact not_le.mp h_le

theorem correctness
(l: List Int)
: problem_spec implementation l
:= by
  unfold problem_spec implementation
  cases l with
  | nil => 
    use 0
    simp
  | cons h t =>
    use List.foldl max h t
    constructor
    · rfl
    · intro h_pos
      constructor
      · exact list_max_ge_all t h
      · exact list_max_in_list t h