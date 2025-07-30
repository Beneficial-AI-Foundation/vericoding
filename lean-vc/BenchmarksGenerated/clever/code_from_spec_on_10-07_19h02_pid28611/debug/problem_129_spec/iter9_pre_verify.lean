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
def allSeparators (text: String) : Bool :=
  text.toList.all (fun c => c = ',' ∨ c = ' ')

def implementation (text: String) : Option (List String) × Option Nat :=
  if text.length = 0 then
    (none, none)
  else if allSeparators text then
    (none, some (text.get! 0).toNat)
  else
    let first := text.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')
    let remaining := text.drop (first.length + 1)
    if remaining.length = 0 then
      (some [first], some (text.get! 0).toNat)
    else
      let nextResult := implementation remaining
      match nextResult.fst with
      | some nextLst => (some ([first] ++ nextLst), some (text.get! 0).toNat)
      | none => (some [first], some (text.get! 0).toNat)

-- LLM HELPER
lemma allSeparators_spec (text: String) : 
  allSeparators text = true ↔ ∀ ch, ch ∈ text.toList → (ch = ',' ∨ ch = ' ') := by
  constructor
  · intro h ch hch
    have : List.all text.toList (fun c => c = ',' ∨ c = ' ') = true := h
    have : decide (ch = ',' ∨ ch = ' ') = true := List.all_eq_true.mp this ch hch
    exact of_decide_eq_true this
  · intro h
    exact List.all_eq_true.mpr (fun ch hch => decide_eq_true (h ch hch))

-- LLM HELPER
lemma takeWhile_containsSubstr (text: String) :
  text.containsSubstr (text.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')) := by
  apply String.containsSubstr_of_prefix
  apply String.takeWhile_prefix

-- LLM HELPER
lemma concat_containsSubstr (text: String) (lst: List String) :
  (∀ s ∈ lst, text.containsSubstr s) →
  text.containsSubstr (text.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')) →
  ∀ s ∈ [text.takeWhile (fun c => c ≠ ',' ∧ c ≠ ' ')] ++ lst, text.containsSubstr s := by
  intro h1 h2 s hs
  simp at hs
  cases' hs with h h
  · subst h
    exact h2
  · exact h1 s h

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
    split_ifs with h_empty h_sep h_remaining
    · exfalso
      rw [h_empty] at h_pos
      exact Nat.lt_irrefl 0 h_pos
    · -- Case: all separators
      constructor
      · simp
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
    · -- Case: not all separators, remaining is empty
      constructor
      · simp
      · constructor
        · constructor
          · intro h_all
            exfalso
            exact h_sep ((allSeparators_spec text).mpr h_all)
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
              simp at hi
              subst hi
              exact takeWhile_containsSubstr text
            · intro lst h_some
              simp at h_some
              subst h_some
              use []
              simp [h_remaining]
    · -- Case: not all separators, remaining is not empty
      constructor
      · simp
      · constructor
        · constructor
          · intro h_all
            exfalso
            exact h_sep ((allSeparators_spec text).mpr h_all)
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
              split at h_some
              · subst h_some
                exact concat_containsSubstr text [] (fun _ h => False.elim h) (takeWhile_containsSubstr text)
              · subst h_some
                exact concat_containsSubstr text [] (fun _ h => False.elim h) (takeWhile_containsSubstr text)
            · intro lst h_some
              simp at h_some
              split at h_some
              · subst h_some
                use []
                simp
              · subst h_some
                use []
                simp