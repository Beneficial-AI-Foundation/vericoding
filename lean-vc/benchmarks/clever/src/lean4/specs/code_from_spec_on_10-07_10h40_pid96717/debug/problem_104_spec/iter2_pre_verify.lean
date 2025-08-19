import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def Even (n : Nat) : Prop := n % 2 = 0

-- LLM HELPER
def Nat.digits (base : Nat) (n : Nat) : List Nat :=
  if n < base then [n]
  else (n % base) :: Nat.digits base (n / base)

-- LLM HELPER
def List.filter {α : Type*} (p : α → Bool) : List α → List α
  | [] => []
  | a :: as => if p a then a :: List.filter p as else List.filter p as

-- LLM HELPER
def List.toSorted {α : Type*} (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | a :: as => List.insertSorted r a (List.toSorted r as)

-- LLM HELPER
def List.insertSorted {α : Type*} (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if r a b then a :: b :: bs else b :: List.insertSorted r a bs

-- LLM HELPER
def List.Sorted {α : Type*} (r : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => r a b ∧ List.Sorted r (b :: rest)

-- LLM HELPER
instance : DecidableRel (Nat.le) := fun a b => Nat.decLe a b

-- LLM HELPER
instance (n : Nat) : Decidable (Even n) := Nat.decidableEq (n % 2) 0

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(x: List Nat) :=
-- spec
let spec (result: List Nat) :=
  let has_even_digits(i: Nat): Bool :=
    (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0;
  (List.Sorted Nat.le result) ∧
  (forall i, i ∈ result ↔ (i ∈ x ∧ !(has_even_digits i)))
-- program termination
∃ result, implementation x = result ∧
spec result

-- LLM HELPER
def has_even_digits (i: Nat): Bool :=
  (List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0

def implementation (x: List Nat) : List Nat := 
  (List.filter (fun i => !(has_even_digits i)) x).toSorted Nat.le

-- LLM HELPER
lemma filter_mem_iff (p : Nat → Bool) (l : List Nat) (x : Nat) :
  x ∈ List.filter p l ↔ x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [List.filter]
  | cons a as ih =>
    simp [List.filter]
    split
    · simp [ih]
    · simp [ih]

-- LLM HELPER
lemma toSorted_sorted (l : List Nat) : List.Sorted Nat.le (l.toSorted Nat.le) := by
  induction l with
  | nil => simp [List.toSorted, List.Sorted]
  | cons a as ih =>
    simp [List.toSorted]
    sorry

-- LLM HELPER
lemma mem_toSorted_iff (l : List Nat) (x : Nat) :
  x ∈ l.toSorted Nat.le ↔ x ∈ l := by
  induction l with
  | nil => simp [List.toSorted]
  | cons a as ih =>
    simp [List.toSorted]
    sorry

-- LLM HELPER
lemma bool_not_true_iff_false (b : Bool) : ¬(b = true) ↔ b = false := by
  cases b <;> simp

theorem correctness
(x: List Nat)
: problem_spec implementation x
:= by
  unfold problem_spec implementation
  simp only [has_even_digits]
  use (List.filter (fun i => !(List.filter (fun d => Even d) (Nat.digits 10 i)).length > 0) x).toSorted Nat.le
  constructor
  · rfl
  · constructor
    · exact toSorted_sorted _
    · intro i
      simp [mem_toSorted_iff, filter_mem_iff]
      constructor
      · intro h
        exact ⟨h.1, by simp [Bool.not_eq_true, h.2]⟩
      · intro h
        exact ⟨h.1, by simp [Bool.not_eq_true] at h ⊢; exact h.2⟩