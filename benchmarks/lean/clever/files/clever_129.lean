-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (text: String) : Option (List String) × Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
      let str := lst[i]!;
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

theorem correctness
(text: String)
: problem_spec implementation text := by
  sorry
-- </vc-theorems>