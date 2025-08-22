import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
-- return a tuple of Option (List String) and Option Nat
(impl: String → Option (List String) × Option Nat)
-- inputs
(text: String) :=
-- spec
let spec (result: Option (List String) × Option Nat) :=
  -- both cannot be None
  let words := result.fst;
  let ord := result.snd;
  0 < text.length →
  ¬ (words = none ∧ ord = none) ∧
    (words = none ↔ ∀ ch, ch ∈ text.toList →  (ch = ',' ∨ ch = ' ')) ∧
    (∀ num, ord = some num → (text.get! 0).toNat = num) ∧
    (∀ lst, words = some lst → ∀ i, i < lst.length →
      let str := lst.get! i;
      text.containsSubstr str) ∧
    (∀ lst, words = some lst →
      let first := text.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ');
      let nextImpl := impl (text.drop (first.length + 1));
      let nextWords := nextImpl.fst;
      (∃ nextLst, nextWords = some nextLst ∧
        lst = [first] ++ nextLst))
-- program terminates
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def splitWords (text: String) : List String :=
  text.splitOn " " |>.filter (fun s => s ≠ "") |>.map (fun s => s.replace "," "")

-- LLM HELPER
def allSeparators (text: String) : Bool :=
  text.toList.all (fun c => c = ',' ∨ c = ' ')

def implementation (text: String) : Option (List String) × Option Nat :=
  if text.length = 0 then
    (none, none)
  else if allSeparators text then
    (none, some (text.get! 0).toNat)
  else
    let words := splitWords text
    (some words, some (text.get! 0).toNat)

-- LLM HELPER
lemma pos_length_not_zero (text: String) : 0 < text.length → text.length ≠ 0 := by
  intro h
  exact Nat.ne_of_gt h

-- LLM HELPER
lemma allSeparators_spec (text: String) : 
  allSeparators text = true ↔ ∀ ch, ch ∈ text.toList → (ch = ',' ∨ ch = ' ') := by
  constructor
  · intro h ch hch
    have : List.all text.toList (fun c => decide (c = ',' ∨ c = ' ')) = true := h
    have : decide (ch = ',' ∨ ch = ' ') = true := List.all_eq_true.mp this ch hch
    exact of_decide_eq_true this
  · intro h
    exact List.all_eq_true.mpr (fun ch hch => of_decide_eq_true (decide_eq_true (h ch hch)))

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro h_pos
    unfold implementation
    simp only [and_true]
    split_ifs with h_empty h_sep
    · exfalso
      rw [h_empty] at h_pos
      exact Nat.lt_irrefl 0 h_pos
    · constructor
      · simp only [not_and, not_true_eq_false, false_implies]
        trivial
      · constructor
        · constructor
          · intro
            exact (allSeparators_spec text).mp h_sep
          · intro h_all
            exact (allSeparators_spec text).mpr h_all
        · constructor
          · intro num h_some
            simp at h_some
            exact h_some
          · constructor
            · intro lst h_some
              simp at h_some
            · intro lst h_some
              simp at h_some
    · constructor
      · simp only [not_and, not_true_eq_false, false_implies]
        trivial
      · constructor
        · constructor
          · intro h_all
            exfalso
            have : ¬allSeparators text = true := h_sep
            exact this ((allSeparators_spec text).mpr h_all)
          · intro
            simp only [false_iff]
            intro h_all
            exact h_sep ((allSeparators_spec text).mpr h_all)
        · constructor
          · intro num h_some
            simp at h_some
            exact h_some
          · constructor
            · intro lst h_some
              simp at h_some
              subst h_some
              intro i hi
              simp [String.containsSubstr]
            · intro lst h_some
              simp at h_some
              subst h_some
              use []
              simp