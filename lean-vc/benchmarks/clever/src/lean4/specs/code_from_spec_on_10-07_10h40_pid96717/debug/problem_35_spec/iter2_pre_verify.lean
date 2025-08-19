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
lemma max_le_iff {a b c : Int} : max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  constructor
  · intro h
    constructor
    · exact le_trans (le_max_left a b) h
    · exact le_trans (le_max_right a b) h
  · intro ⟨ha, hb⟩
    exact max_le ha hb

-- LLM HELPER
lemma foldl_max_ge_all {l : List Int} {h : Int} (i : Nat) (hi : i < (h :: l).length) : 
  (h :: l).get! i ≤ List.foldl max h l := by
  induction l generalizing h i with
  | nil => 
    simp at hi
    cases i with
    | zero => simp [List.get!, List.foldl]
    | succ n => simp at hi
  | cons a t ih =>
    simp at hi
    cases i with
    | zero => 
      simp [List.get!, List.foldl]
      exact le_max_left h a
    | succ j =>
      simp [List.get!]
      have : List.foldl max h (a :: t) = List.foldl max (max h a) t := by simp [List.foldl]
      rw [this]
      have hj : j < (max h a :: t).length := by simp; exact Nat.lt_of_succ_lt_succ hi
      exact ih hj

-- LLM HELPER
lemma foldl_max_exists {l : List Int} {h : Int} : 
  ∃ i, i < (h :: l).length ∧ (h :: l).get! i = List.foldl max h l := by
  induction l generalizing h with
  | nil => 
    use 0
    simp [List.get!, List.foldl]
  | cons a t ih =>
    have : List.foldl max h (a :: t) = List.foldl max (max h a) t := by simp [List.foldl]
    rw [this]
    obtain ⟨i, hi, eq⟩ := ih
    use i + 1
    constructor
    · simp; exact hi
    · simp [List.get!]; exact eq

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
    · intro hlen
      constructor
      · exact foldl_max_ge_all
      · exact foldl_max_exists